#!/usr/bin/env python3
"""Redundancy inside a real tactic search, and the equal-budget comparison.

  python scripts/run_search.py --register
  python scripts/run_search.py --run [--arms menu,model]
  python scripts/run_search.py --check-committed

Tasks are theorems of the Mathlib slice (`experiments/linearizations-mathlib-v0.1`)
whose proof is one `by` block of 3 to 20 steps, every k-th in (module, line)
order, proved again in their original context through the Lean REPL
(`scripts/search_harness.py`). For each task and each proposer arm (a fixed
tactic menu; a local model sampled four times plus the menu) two searches run
with the same expansion budget: the whole-state search, which records order
and goal duplicates among its expansions, and the AND-OR search over
canonical goals. Every found proof is re-verified from the statement.
"""

from __future__ import annotations

import argparse
import gzip
import json
import statistics
import sys
import time
import urllib.request
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_linearizations as base  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
import search_harness as harness  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, read_gz_lines, sha256_file, write_lf  # noqa: E402

ROOT = base.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
MODEL_CALLS = EXPERIMENT / "model-calls.jsonl.gz"
MODEL_CALLS_PLAIN = EXPERIMENT / "model-calls.jsonl"  # during a run; compressed when it completes
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py",
    "runner": Path(__file__).resolve(),
}
MIN_STEPS, MAX_STEPS = 3, 20
TARGET_TASKS = 48
BUDGET = 24
SAMPLES = 4
TEMPERATURE = 0.8
MODEL_ID = "qwen3.6-35b-a3b-ud-q4_k_xl"
ARMS = ("menu", "model")
ORDER_THRESHOLD = 0.01
SHARING_THRESHOLD = 0.10
CHECK_BUDGET = 4


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def generated(name: str) -> bool:
    last = name.split(":")[0].split(".")[-1]
    return last.startswith("inst") or last in ("ext", "ext_iff") or last == "_example" or ":" in name


def candidate_tasks() -> list[dict[str, Any]]:
    """Slice theorems with one `by` block of 3 to 20 steps, in (module, line) order."""
    rows = {(r["module"], r["declaration"]): r
            for r in (json.loads(l) for l in slice_.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip())}
    out = []
    for record in read_gz_lines(slice_.EXTRACTION):
        row = rows[(record["module"], record["declaration"])]
        roots = [n for n in record["nodes"] if n["parent"] is None]
        if not (MIN_STEPS <= row["steps"] <= MAX_STEPS) or generated(record["declaration"]):
            continue
        if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic"):
            continue
        out.append({"module": record["module"], "declaration": record["declaration"], "line": roots[0]["line"],
                    "steps": row["steps"], "structure": row["structure"], "linearizations": row["linearizations"]})
    return sorted(out, key=lambda t: (t["module"], t["line"]))


def select_tasks() -> tuple[list[dict[str, Any]], int]:
    candidates = candidate_tasks()
    stride = max(1, -(-len(candidates) // TARGET_TASKS))
    return candidates[::stride], stride


def registration_payload() -> dict[str, Any]:
    tasks, stride = select_tasks()
    return {
        "experiment": "search-v0.1",
        "question": "how much of a whole-state tactic search is spent on states that differ only in goal order, "
                    "how much on goals already expanded elsewhere, and whether a search over canonical goals "
                    "proves more at equal budget",
        "tasks": {"source": "linearizations-mathlib-v0.1", "sliceResultsSha256": sha256_file(slice_.RESULTS),
                  "sliceExtractionSha256": sha256_file(slice_.EXTRACTION),
                  "rule": f"theorems of the slice whose proof is one `by` block of {MIN_STEPS} to {MAX_STEPS} "
                          f"steps, not generated, every {stride}th in (module, line) order",
                  "count": len(tasks), "stride": stride,
                  "context": "each theorem is stated with `sorry` after elaborating its module up to the theorem, "
                             "so that the search sees exactly the original context and not the theorem itself"},
        "arms": {"menu": {"proposer": "the fixed menu of scripts/search_harness.py"},
                 "model": {"proposer": f"{MODEL_ID} at temperature {TEMPERATURE}, {SAMPLES} samples per expansion, "
                                       "thinking off, 64 tokens, then the menu"}},
        "searches": {"whole": "breadth-first over whole states, exact-state deduplication, tactic applied to the "
                              "first goal", "andor": "breadth-first over canonical goals, each goal expanded once, "
                              "`pick_goal` to bring a goal to the front of the state it was created in"},
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "measures": {"orderDuplicates": "whole-state expansions whose goal multiset was already expanded in "
                                        "another order, over all whole-state expansions of the arm",
                     "goalDuplicates": "whole-state expansions whose first goal, canonicalized, was already "
                                       "expanded as a first goal, over all whole-state expansions of the arm",
                     "proved": "tasks whose found proof re-verifies from the statement"},
        "hypotheses": {
            "H14": f"in both arms the order-duplicate fraction is below {ORDER_THRESHOLD:.0%}",
            "H15": f"in both arms the goal-duplicate fraction is at least {SHARING_THRESHOLD:.0%}",
            "H16a": "in both arms the AND-OR search proves at least as many tasks as the whole-state search",
            "H16b": "in the model arm the AND-OR search proves strictly more tasks",
        },
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "both searches with the menu, budget 8, on three theorems of "
                                                "Mathlib.Logic.Basic in their module context (none proved; one "
                                                "goal duplicate in 8 expansions), the model arm on two of them "
                                                "(one unverified proof that used the theorem's own name, which "
                                                "is why tasks are stated as examples), the full pipeline with "
                                                "both arms at budget 3 on two candidate theorems of "
                                                "Mathlib.Algebra.AddConstMap.Basic that the stride does not "
                                                "select (none proved), and, with the full Mathlib environment "
                                                "and `type_of%` statements, eight library theorems that simp, "
                                                "omega, or exact? closed in one expansion; no task of this "
                                                "corpus was run",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def model_server_alive() -> bool:
    try:
        with urllib.request.urlopen("http://127.0.0.1:8080/v1/models", timeout=5) as response:
            return response.status == 200
    except Exception:  # noqa: BLE001
        return False


def run_tasks(tasks: list[dict[str, Any]], arms: list[str], budget: int,
              model_log: list[dict[str, Any]] | None, sink: Path | None = None) -> list[dict[str, Any]]:
    """Runs every task; with `sink`, appends each row to it as it completes and
    skips the tasks already in it, so that an interrupted run resumes."""
    repl = LeanRepl(find_lake(), imports=None)
    if model_log is not None:
        harness.MODEL_LOG = model_log
    rows: list[dict[str, Any]] = []
    done: set[tuple[str, str]] = set()
    if sink is not None and sink.exists():
        rows = [json.loads(l) for l in sink.read_text(encoding="utf-8").splitlines() if l.strip()]
        done = {(r["module"], r["declaration"]) for r in rows if "declaration" in r}

    flushed = len(model_log) if model_log is not None else 0

    def record(row: dict[str, Any]) -> None:
        nonlocal flushed
        rows.append(row)
        if sink is not None:
            with sink.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            if model_log is not None and len(model_log) > flushed:
                with MODEL_CALLS_PLAIN.open("a", encoding="utf-8", newline="\n") as handle:
                    for entry in model_log[flushed:]:
                        handle.write(json.dumps(entry, ensure_ascii=False) + "\n")
                flushed = len(model_log)

    by_module: dict[str, list[dict[str, Any]]] = {}
    for task in tasks:
        if (task["module"], task["declaration"]) not in done:
            by_module.setdefault(task["module"], []).append(task)
    try:
        for module, module_tasks in by_module.items():
            path = ROOT / ".lake" / "packages" / "mathlib" / (module.replace(".", "/") + ".lean")
            remaining = list(module_tasks)
            while remaining:
                session = harness.ModuleSession(repl, module, path, [(t["declaration"], t["line"]) for t in remaining])
                current: dict[str, Any] | None = None
                try:
                    for name, made in session.tasks_in_order():
                        current = next(t for t in remaining if t["declaration"] == name)
                        if made is None:
                            record({**current, "task": None})
                            print(json.dumps({"task": name, "constructed": False}), flush=True)
                            continue
                        row: dict[str, Any] = {**current, "task": {"goal": made.goal}}
                        for arm in arms:
                            proposer = harness.menu_proposer if arm == "menu" else                                 harness.model_proposer(SAMPLES, TEMPERATURE, MODEL_ID)
                            for search in ("whole", "andor"):
                                function = harness.whole_state_search if search == "whole" else harness.and_or_search
                                result = function(repl, made.proof_state, [made.goal], proposer, budget)
                                verified = session.verify(made, result["proof"]) if result["proof"] else False
                                row[f"{arm}.{search}"] = {**result, "verified": verified}
                        record(row)
                        print(json.dumps({"task": name, **{k: (v["verified"], len(v["expansions"]),
                                                               v.get("goalDuplicates"), v.get("orderDuplicates"))
                                                           for k, v in row.items() if "." in k}}), flush=True)
                    remaining = []
                except ReplTimeout:
                    # the REPL restarted and the module's environments are gone: record the
                    # task that was running and resume with the tasks after it
                    if current is None:
                        record({"module": module, "abandoned": "repl timeout before the first task"})
                        remaining = []
                    else:
                        record({**current, "task": None, "abandoned": "repl timeout"})
                        print(json.dumps({"task": current["declaration"], "abandoned": True}), flush=True)
                        remaining = remaining[remaining.index(current) + 1:]
                if session.errors:
                    record({"module": module, "elaborationErrors": session.errors[:5]})
    finally:
        repl.close()
    return rows


def summarize(rows: list[dict[str, Any]], arms: list[str]) -> dict[str, Any]:
    tasks = [r for r in rows if "declaration" in r]
    constructed = [r for r in tasks if r.get("task")]
    out: dict[str, Any] = {"experiment": "search-v0.1", "preregistrationSha256": sha256_file(PREREG),
                           "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
                           "tasks": len(tasks), "constructed": len(constructed), "arms": {}}
    for arm in arms:
        whole = [r[f"{arm}.whole"] for r in constructed if f"{arm}.whole" in r]
        andor = [r[f"{arm}.andor"] for r in constructed if f"{arm}.andor" in r]
        expansions = [e for w in whole for e in w["expansions"]]
        order = sum(1 for e in expansions if e["orderDuplicate"])
        goal = sum(1 for e in expansions if e["goalDuplicate"])
        out["arms"][arm] = {
            "tasks": len(whole), "wholeExpansions": len(expansions),
            "orderDuplicates": order, "orderFraction": order / len(expansions) if expansions else None,
            "goalDuplicates": goal, "goalFraction": goal / len(expansions) if expansions else None,
            "wholeProved": sum(1 for w in whole if w["verified"]),
            "andorProved": sum(1 for a in andor if a["verified"]),
            "wholeFoundUnverified": sum(1 for w in whole if w["proof"] and not w["verified"]),
            "andorFoundUnverified": sum(1 for a in andor if a["proof"] and not a["verified"]),
            "timeouts": sum(w["timeouts"] for w in whole) + sum(a["timeouts"] for a in andor),
            "restarts": max([w["restarts"] for w in whole] + [a["restarts"] for a in andor] + [0]),
            "medianSecondsWhole": statistics.median([w["seconds"] for w in whole]) if whole else None,
            "medianSecondsAndor": statistics.median([a["seconds"] for a in andor]) if andor else None,
            "validPerExpansion": statistics.mean([e["valid"] for e in expansions]) if expansions else None,
        }
    a = out["arms"]
    ran = [arm for arm in arms if a[arm]["wholeExpansions"]]
    out["hypotheses"] = {
        "H14": {"supported": bool(ran) and all(a[arm]["orderFraction"] < ORDER_THRESHOLD for arm in ran)},
        "H15": {"supported": bool(ran) and all(a[arm]["goalFraction"] >= SHARING_THRESHOLD for arm in ran)},
        "H16a": {"supported": bool(ran) and all(a[arm]["andorProved"] >= a[arm]["wholeProved"] for arm in ran)},
        "H16b": {"supported": "model" in ran and a["model"]["andorProved"] > a["model"]["wholeProved"]},
        "armsRun": ran,
    }
    out["resultsSha256"] = sha256_file(RESULTS)
    out["modelCallsSha256"] = sha256_file(MODEL_CALLS) if MODEL_CALLS.exists() else None
    return out


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Redundancy inside a tactic search (search v0.1)", "",
             "Whole-state and AND-OR searches with the same proposer and budget on theorems of the",
             "Mathlib slice, in their original context; definitions, tasks, and hypotheses are frozen",
             "in `preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             f"Tasks: {summary['tasks']}; stated in context: {summary['constructed']}.", "",
             "| Arm | Tasks | Whole-state expansions | Order duplicates | Goal duplicates | Valid tactics per "
             "expansion | Proved: whole | Proved: AND-OR | Found but unverified (whole / AND-OR) |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for arm, e in summary["arms"].items():
        if not e["wholeExpansions"]:
            lines.append(f"| {arm} | {e['tasks']} | 0 | n/a | n/a | n/a | n/a | n/a | n/a |")
            continue
        lines.append(f"| {arm} | {e['tasks']} | {e['wholeExpansions']} | {e['orderDuplicates']} "
                     f"({e['orderFraction']:.1%}) | {e['goalDuplicates']} ({e['goalFraction']:.1%}) | "
                     f"{e['validPerExpansion']:.1f} | {e['wholeProved']} | {e['andorProved']} | "
                     f"{e['wholeFoundUnverified']} / {e['andorFoundUnverified']} |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              f"- H14 (order-duplicate fraction below {ORDER_THRESHOLD:.0%} in both arms): supported: {h['H14']['supported']}.",
              f"- H15 (goal-duplicate fraction at least {SHARING_THRESHOLD:.0%} in both arms): supported: {h['H15']['supported']}.",
              f"- H16a (AND-OR proves at least as many tasks in both arms): supported: {h['H16a']['supported']}.",
              f"- H16b (AND-OR proves strictly more in the model arm): supported: {h['H16b']['supported']}.",
              "", f"Arms run: {', '.join(h['armsRun']) or 'none'}.", "",
              "## Interpretation boundary", "",
              "Both searches are breadth-first with a small budget and a weak proposer; the",
              "fractions describe where such a search spends its expansions, not the best",
              "achievable prover. A proof counts only when it re-verifies from the statement."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--arms", default=",".join(ARMS))
    args = parser.parse_args()
    arms = [a for a in args.arms.split(",") if a]

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload()
        tasks, _ = select_tasks()
        write_lf(TASKS, json.dumps(tasks, indent=1) + "\n")
        payload["tasksSha256"] = sha256_file(TASKS)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("tasks changed since registration")
    if prereg["tasks"]["sliceResultsSha256"] != sha256_file(slice_.RESULTS):
        raise SystemExit("the slice results changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))

    if args.run:
        if "model" in arms and not model_server_alive():
            raise SystemExit("the local model server is not running")
        model_log: list[dict[str, Any]] = []
        if MODEL_CALLS_PLAIN.exists():  # resuming: keep the calls already logged
            model_log = [json.loads(l) for l in MODEL_CALLS_PLAIN.read_text(encoding="utf-8").splitlines() if l.strip()]
        rows = run_tasks(tasks, arms, BUDGET, model_log if "model" in arms else None, sink=RESULTS)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        if model_log:
            MODEL_CALLS.write_bytes(gzip.compress("".join(json.dumps(m, ensure_ascii=False) + "\n"
                                                          for m in model_log).encode("utf-8"), 9, mtime=0))
            MODEL_CALLS_PLAIN.unlink()
        summary = summarize(rows, arms)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-run": summary["hypotheses"]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, [a for a in ARMS if a in summary["arms"]])
    if recomputed["arms"] != summary["arms"] or recomputed["hypotheses"] != summary["hypotheses"]:
        raise SystemExit("the committed summary does not follow from the committed results")
    first = next((r for r in committed if r.get("task") and "menu.whole" in r), None)
    if first is not None:
        rows = run_tasks([{k: first[k] for k in ("module", "declaration", "line", "steps", "structure",
                                                  "linearizations")}], ["menu"], CHECK_BUDGET, None)
        fresh = rows[0]["menu.whole"]["expansions"][:CHECK_BUDGET]
        want = first["menu.whole"]["expansions"][:CHECK_BUDGET]
        keys = ("state", "depth", "goals", "candidates", "orderDuplicate", "goalDuplicate")
        if [{k: e[k] for k in keys} for e in fresh] != [{k: e[k] for k in keys} for e in want]:
            raise SystemExit(f"the first task's menu search differs on re-run: {fresh} vs {want}")
    print(f"search-check-ok: tasks={len(committed)} rerun={'yes' if first else 'no'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
