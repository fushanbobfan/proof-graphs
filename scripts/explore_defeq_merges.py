#!/usr/bin/env python3
"""Exploratory, not registered: what defeq-v0.1's merges bridge in the step prover's search.

  python scripts/explore_defeq_merges.py --run [--workers 3]
  python scripts/explore_defeq_merges.py --check

Identity up to definitional equality added 150 goal duplicates to the step prover's whole-state search in defeq-v0.1,
all at reducible transparency, but its logs keep only hashes of the printed goals. This replays every step-prover unit
with such a duplicate, merges its goals again at reducible transparency, as the registered merge does, and classifies
each merged pair by the first of these erasures that makes the two expressions equal: none (equal after the merge's
beta-reduction and level normalization), binder names and kinds, proof subterms, instance arguments, instance
arguments and proofs, implicit arguments and proofs; a pair none of them equates needs unfolding ("other"). Each added
duplicate is attributed to the merge that joins its first goal to the earlier first goal of its class. The replays use
defeq-v0.1's amended session with one more tactic defined after the imports; faithful keys of goals without
metavariables, the only goals merged, do not depend on that. `--run` writes
`experiments/defeq-v0.1-merges/rows.jsonl` and the summary; `--check` recomputes the summary from the rows.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import difflib
import json
import re
import sys
import tempfile
import threading
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_defeq as gd  # noqa: E402
import run_defeq_replay as dq  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

OUT = dq.ROOT / "experiments" / "defeq-v0.1-merges"
ROWS = OUT / "rows.jsonl"
SUMMARY = OUT / "summary.json"
EXAMPLES = 3
WINDOW = 160

# The elaboration of `goal_defeq`'s merge, unchanged, followed by the reducible pass and the classification.
_PREFIX = gd.DEFEQ_TEMPLATE.split("  let mut result : Array")[0]
_SUFFIX = r"""  -- An erased subterm becomes `sorryAx` of its type, so that the result stays well typed and two erased subterms
  -- are equal exactly when their types are.
  let placeholder : Lean.Expr → Lean.MetaM Lean.Expr := fun x => do
    let t ← Lean.Meta.inferType x
    let u ← Lean.Meta.getLevel t
    return Lean.mkApp2 (Lean.mkConst ``sorryAx [u]) t (Lean.mkConst ``Bool.false)
  let eraseProofs : Lean.Expr → Lean.MetaM Lean.Expr := fun e =>
    Lean.Meta.transform e (post := fun x => do
      if (← Lean.Meta.isProof x) then return .done (← placeholder x) else return .continue)
  let eraseArgs : (Lean.Meta.ParamInfo → Bool) → Lean.Expr → Lean.MetaM Lean.Expr := fun drop e =>
    Lean.Meta.transform e (post := fun x => do
      match x with
      | .app .. =>
        let f := x.getAppFn
        let args := x.getAppArgs
        if f.hasLooseBVars then return .continue
        let info ← Lean.Meta.getFunInfoNArgs f args.size
        let mut newArgs := args
        for i in [0:args.size] do
          if h : i < info.paramInfo.size then
            if drop info.paramInfo[i] then
              newArgs := newArgs.set! i (← placeholder args[i]!)
        return .done (Lean.mkAppN f newArgs)
      | _ => return .continue)
  let eraseBinders : Lean.Expr → Lean.MetaM Lean.Expr := fun e =>
    Lean.Core.transform e (post := fun x => match x with
      | .forallE _ d b _ => pure (.done (.forallE `x d b .default))
      | .lam _ d b _ => pure (.done (.lam `x d b .default))
      | _ => pure .continue)
  let mut buckets : Std.HashMap UInt64 (Array Nat) := {}
  let mut out : Array Lean.Json := #[]
  for i in [0:terms.size] do
    match terms[i]! with
    | none => pure ()
    | some e =>
      let k := keys[i]!
      let mut found : Option Nat := none
      for j in buckets.getD k #[] do
        let saved ← Lean.Elab.Tactic.saveState
        let verdict? ← Lean.tryCatchRuntimeEx
            (do
              let v ← Lean.withCurrHeartbeats <| Lean.Meta.withTransparency .reducible <|
                Lean.Meta.isDefEq e terms[j]!.get!
              return some v)
            (fun _ => do
              saved.restore
              return none)
        if verdict? == some true then
          found := some j
          break
      match found with
      | none => buckets := buckets.insert k ((buckets.getD k #[]).push i)
      | some j =>
        let e' := terms[j]!.get!
        let be ← eraseBinders e
        let be' ← eraseBinders e'
        let pe ← eraseProofs be
        let pe' ← eraseProofs be'
        let ie ← eraseArgs (fun p => p.isInstImplicit) be
        let ie' ← eraseArgs (fun p => p.isInstImplicit) be'
        let ipe ← eraseArgs (fun p => p.isInstImplicit) pe
        let ipe' ← eraseArgs (fun p => p.isInstImplicit) pe'
        let ape ← eraseArgs (fun p => !p.isExplicit) pe
        let ape' ← eraseArgs (fun p => !p.isExplicit) pe'
        let kind :=
          if e == e' then "equal after normalization"
          else if be == be' then "binder names and kinds"
          else if pe == pe' then "proofs"
          else if ie == ie' then "instance arguments"
          else if ipe == ipe' then "instance arguments and proofs"
          else if ape == ape' then "implicit arguments and proofs"
          else "other"
        out := out.push (Lean.Json.mkObj [("i", Lean.toJson i), ("j", Lean.toJson j), ("kind", Lean.Json.str kind)])
  Lean.logInfo (Lean.Json.arr out).compress"""
KINDS_DEFINITION = ("open Lean Elab Tactic in\nelab \"pg_defeq_kinds \" path:str : tactic => do"
                    + (_PREFIX + _SUFFIX).replace("run_tac do", "", 1).replace("PATH", "path.getString"))


# Each faithful key's text, kept as the replays compute the keys, to show what the expression key tells apart.
FAITHFUL_TEXT: dict[str, str] = {}
_goal_key = dq.gi.goal_key


def _recording_goal_key(goal: dict[str, Any]) -> str:
    key = _goal_key(goal)
    FAITHFUL_TEXT.setdefault(key, dq.gi._renumber([goal])[0])
    return key


class KindsSession(dq.DefeqSession):
    """defeq-v0.1's amended session, with the classifying tactic defined after its own three."""

    def __init__(self, repl: Any, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        response = repl._exchange({"cmd": KINDS_DEFINITION, "env": self.env}, repl.import_timeout)
        errors = [m.get("data", "") for m in response.get("messages", []) if m.get("severity") == "error"]
        if "env" not in response or errors:
            raise RuntimeError(f"pg_defeq_kinds did not define: {errors[:2] or response}")
        self.env = response["env"]


def added_duplicates(log: dict[str, Any]) -> list[tuple[str, str]]:
    """Each goal duplicate the reducible classes add to a unit: (its first goal, the earlier first goal of its class)."""
    classes = dq.classes_of(log, "reducible")
    firsts: set[str] = set()
    owner: dict[str, str] = {}
    out = []
    for state, _ in dq.kv.expansions_of(log):
        goals = log["states"][str(state)].get("faithful")
        if not goals:
            continue
        first = goals[0]
        c = classes.get(first, first)
        if c in owner and first not in firsts:
            out.append((first, owner[c]))
        owner.setdefault(c, first)
        firsts.add(first)
    return out


HYPOTHESIS = re.compile(r"(?<![\w.])h(\d+)(?![\w.])")


def without_lets(text: str) -> str:
    """A faithful key's text without its let-bound hypotheses (the lines whose type is followed by ` := ` and a
    value), the remaining hypotheses renumbered by position and references to a dropped one written `hL`."""
    lines = text.split("\n")
    is_let = []
    for line in lines:
        depth, found = 0, False
        if not line.startswith("|- "):
            for i, c in enumerate(line):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                elif depth == 0 and line.startswith(" := ", i):
                    found = True
                    break
        is_let.append(found)
    hypotheses = [i for i, line in enumerate(lines) if not line.startswith("|- ")]
    position: dict[int, str] = {}
    for p, i in enumerate(hypotheses):
        position[p] = "hL" if is_let[i] else f"h{sum(1 for q in hypotheses[:p] if not is_let[q])}"
    return "\n".join(HYPOTHESIS.sub(lambda m: position.get(int(m.group(1)), m.group(0)), line)
                     for line, let in zip(lines, is_let) if not let)


def category(merge: dict[str, Any], texts: dict[str, str]) -> str:
    """The merge's kind, with equal closed types split by what their expression keys differ in. The closed type leaves
    out let-bound hypotheses the goal does not use (`mkForallFVars` drops them), which are equal up to zeta-reduction
    whatever their types and values."""
    if merge["kind"] != "equal after normalization":
        return merge["kind"]
    if not merge["samePrinted"]:
        return "beta-reduction or universe levels"
    a, b = texts.get(merge["member"]), texts.get(merge["representative"])
    if a is not None and b is not None and without_lets(a) == without_lets(b):
        return "unused let hypotheses"
    return "same closed type, other"


CATEGORIES = ["unused let hypotheses", "same closed type, other", "beta-reduction or universe levels",
              "binder names and kinds", "proofs", "instance arguments", "instance arguments and proofs",
              "implicit arguments and proofs", "other"]


def first_difference(a: str, b: str) -> list[str]:
    """The two texts around their first difference, by tokens."""
    ta, tb = re.findall(r"[^\s()]+|[()]", a), re.findall(r"[^\s()]+|[()]", b)
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(a=ta, b=tb, autojunk=False).get_opcodes():
        if tag != "equal":
            left = " ".join(ta[max(0, i1 - 12):i2 + 12])
            right = " ".join(tb[max(0, j1 - 12):j2 + 12])
            return [left[:2 * WINDOW], right[:2 * WINDOW]]
    return ["", ""]


def run_unit(kind: str, task: dict[str, Any], search: str, sets: dict[str, Any] | None,
             log: dict[str, Any]) -> dict[str, Any]:
    kv = dq.kv
    unit = list(kv.unit_key(kind, task, search))
    repl = dq.DefeqRecordingRepl(dq.find_lake(), imports=None)
    try:
        path = dq.ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = KindsSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return {"unit": unit, "error": "not constructed"}
            proposer = kv.ReplayDraws(sets or {}).proposer(search)
            repl.recording = True
            result = kv.FUNCTIONS[search](repl, made.proof_state, [made.goal], proposer, kv.v7.BUDGET,
                                          verifier=lambda s, m=made: session.verify(m, s))
            repl.recording = False
            usable = [k for k in repl.order if repl.closed[k].get("rt") in ("exact", "reducible")]
            folder = Path(tempfile.mkdtemp(prefix="defeq-kinds-"))
            entries = folder / "entries.json"
            entries.write_text(json.dumps([{"pp": repl.closed[k]["pp"], "levels": repl.closed[k]["levels"],
                                            "hyps": repl.closed[k]["hyps"]} for k in usable], ensure_ascii=False),
                               encoding="utf-8")
            try:
                # A limit set inside a tactic does not bound elaboration (docs/heartbeat-limit.md), so this runs
                # under the declaration's limit, as the registered merge did.
                response = repl._exchange({"tactic": f"set_option maxHeartbeats {gd.DEFEQ_HEARTBEATS} in\n"
                                                     f"pg_defeq_kinds {json.dumps(str(entries))}",
                                           "proofState": made.proof_state}, dq.PASS_TIMEOUT)
            finally:
                entries.unlink()
                folder.rmdir()
            pairs = gd._info(response)
            if not isinstance(pairs, list):
                return {"unit": unit, "error": f"classification failed: {json.dumps(response)[:300]}"}
            kind_of = {usable[p["i"]]: (usable[p["j"]], p["kind"]) for p in pairs}
            texts = {k: repl.closed[k]["pp"] for k in usable}
            merges = [{"member": m, "representative": r, "kind": k, "samePrinted": texts[m] == texts[r],
                       "roundTrips": [repl.closed[m]["rt"], repl.closed[r]["rt"]],
                       "difference": first_difference(texts[m], texts[r]),
                       "faithfulDifference": first_difference(FAITHFUL_TEXT.get(m, ""), FAITHFUL_TEXT.get(r, ""))}
                      for m, (r, k) in kind_of.items()]
            for m in merges:
                m["category"] = category(m, FAITHFUL_TEXT)
            category_of = {m["member"]: m["category"] for m in merges}
            added = []
            for first, earlier in added_duplicates(log):
                link = first if first in kind_of else earlier if earlier in kind_of else None
                added.append({"first": first, "earlier": earlier,
                              "category": category_of[link] if link is not None else None})
            return {"unit": unit, "outcome": [bool(result["proof"]), len(result["expansions"])],
                    "usable": len(usable), "merges": merges, "added": added}
        return {"unit": unit, "error": "declaration range not found"}
    finally:
        repl.close()


def selected() -> list[tuple[tuple[str, dict[str, Any], str], dict[str, Any]]]:
    logs = dq.read_logs()
    out = []
    for u in dq.units():
        key = json.dumps(list(dq.kv.unit_key(*u)))
        log = logs.get(key)
        if u[0] == "prover" and log and (log.get("merge") or {}).get("completed") and added_duplicates(log):
            out.append((u, log))
    return out


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    added = [a for r in rows for a in r.get("added", [])]
    merges = [m for r in rows for m in r.get("merges", [])]
    examples: dict[str, list[dict[str, Any]]] = {k: [] for k in CATEGORIES}
    linked = {(r["unit"][2], a[f]) for r in rows for a in r.get("added", []) for f in ("first", "earlier")}
    for r in rows:
        for m in r.get("merges", []):
            # Examples are drawn from the merges behind added duplicates, then from the rest.
            if (r["unit"][2], m["member"]) in linked and len(examples[m["category"]]) < EXAMPLES:
                examples[m["category"]].append({"unit": r["unit"][2], "printed": m["difference"],
                                                "expressionKeys": m["faithfulDifference"]})
    for r in rows:
        for m in r.get("merges", []):
            if (r["unit"][2], m["member"]) not in linked and len(examples[m["category"]]) < EXAMPLES:
                examples[m["category"]].append({"unit": r["unit"][2], "printed": m["difference"],
                                                "expressionKeys": m["faithfulDifference"]})
    by_unit = {r["unit"][2]: {c: sum(1 for a in r.get("added", []) if a["category"] == c) for c in CATEGORIES}
               for r in rows if r.get("added")}
    return {"experiment": "defeq-v0.1-merges", "registered": False, "source": "defeq-v0.1",
            "defeqLogsSha256": sha256_file(dq.LOGS), "units": len(rows),
            "unitsFailed": [r["unit"][2] for r in rows if r.get("error")],
            "addedDuplicates": len(added),
            "addedByCategory": {c: sum(1 for a in added if a["category"] == c) for c in CATEGORIES}
            | {"unmatched": sum(1 for a in added if a["category"] is None)},
            "mergedPairs": len(merges),
            "pairsByCategory": {c: sum(1 for m in merges if m["category"] == c) for c in CATEGORIES},
            "addedByUnit": {u: {c: n for c, n in v.items() if n} for u, v in sorted(by_unit.items())},
            "examples": examples}


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()
    if args.run:
        dq.gi.goal_key = _recording_goal_key
        OUT.mkdir(parents=True, exist_ok=True)
        sets = dq.kv.recorded_draws()
        units = selected()
        print(f"{len(units)} units", flush=True)
        rows: list[dict[str, Any]] = []
        lock = threading.Lock()

        def one(item: tuple[tuple[str, dict[str, Any], str], dict[str, Any]]) -> dict[str, Any]:
            (kind, task, search), log = item
            dq.admit()
            try:
                return run_unit(kind, task, search, sets.get(task["index"]), log)
            except Exception as error:  # noqa: BLE001
                return {"unit": list(dq.kv.unit_key(kind, task, search)), "error": f"{type(error).__name__}: {error}"[:300]}

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            for row in pool.map(one, units):
                with lock:
                    rows.append(row)
                    print(json.dumps({"unit": row["unit"][2][:50], "added": len(row.get("added", [])),
                                      "merges": len(row.get("merges", [])), "error": row.get("error")},
                                     ensure_ascii=False), flush=True)
        write_lf(ROWS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        write_lf(SUMMARY, json.dumps(summarize(rows), indent=1, ensure_ascii=False) + "\n")
        print(json.dumps(summarize(rows)["addedByCategory"]))
        return 0
    rows = [json.loads(l) for l in ROWS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(rows))):
        raise SystemExit("the summary does not follow from the rows")
    print(f"defeq-v0.1-merges-check-ok: units={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
