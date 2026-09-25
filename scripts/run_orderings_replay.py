#!/usr/bin/env python3
"""Orderings replay v0.1: do the orderings of a goal-origin graph replay as Lean scripts?

  python scripts/run_orderings_replay.py --register
  python scripts/run_orderings_replay.py --run [--workers 4]
  python scripts/run_orderings_replay.py --check-committed

The number of orderings L counts the linear extensions of a proof's
goal-origin graph. An ordering is a script only if Lean accepts its steps in
that order. For a seeded sample of small proofs from both corpora of step 1,
whose steps can be cut out of the source one line each, every ordering is
replayed through the Lean REPL in the theorem's own context: before each
step, `rotate_left` brings the goal that step consumed in the original proof
to the front, and the step's own tactic text runs on it. An ordering replays
when every tactic succeeds, every step leaves exactly the goals the graph
says it creates, no goal is left, and the resulting script re-verifies from
the statement. The original order is replayed first as a control of the
mechanism; proofs whose original order does not replay are reported and set
aside.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import random
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
import run_linearizations as library  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
import search_harness as harness  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, read_gz_lines, sha256_file, write_lf  # noqa: E402
from run_search import generated  # noqa: E402

ROOT = library.ROOT
EXPERIMENT = ROOT / "experiments" / "orderings-replay-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
SAMPLE = EXPERIMENT / "sample.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations.py",
                   "harness": ROOT / "scripts" / "search_harness.py",
                   "repl": ROOT / "scripts" / "lean_repl.py",
                   "runner": Path(__file__).resolve()}
CORPORA = {
    "proofnet-ir": {"extraction": library.EXTRACTION, "source": ROOT / ".lake" / "packages" / "proofnet-ir"},
    "mathlib-slice": {"extraction": slice_.EXTRACTION, "source": ROOT / ".lake" / "packages" / "mathlib"},
}
MIN_STEPS, MAX_STEPS = 3, 8
MIN_ORDERINGS, MAX_ORDERINGS = 2, 24
PER_CORPUS = 40
SEED = 20260925
THRESHOLD = 0.9
STRUCTURAL = re.compile(r"(case|next|calc|conv|induction|cases|match|all_goals|any_goals|first|try|repeat|focus|"
                        r"on_goal|pick_goal|swap|rotate_left|rotate_right|iterate|show)\b")


def step_texts(record: dict[str, Any], steps: list[dict[str, Any]], lines: list[str]) -> list[str] | None:
    """The tactic text of each step, one source line each, or None when the proof does not separate so."""
    root = next(n for n in record["nodes"] if n["parent"] is None)
    by_line = root["line"]
    step_lines = [s["line"] for s in steps]
    if len(set(step_lines)) != len(step_lines):
        return None
    last = max(n["line"] for n in record["nodes"])
    for number in range(by_line + 1, last + 1):  # every other line of the body is blank, a comment, or a bullet
        text = lines[number - 1].strip()
        if number not in step_lines and text not in ("", "·") and not text.startswith("--"):
            return None
    out = []
    for number in step_lines:
        text = lines[number - 1]
        if number == by_line:
            inline = re.search(r":=\s*by\s+(\S.*)$", text)
            if inline is None:
                return None
            text = inline.group(1)
        text = re.sub(r"\s--.*$", "", text).strip()
        while text.startswith("·"):
            text = text[1:].strip()
        if not text or "<;>" in text or ";" in text or re.search(r"\bby\b", text) or STRUCTURAL.match(text):
            return None
        out.append(text)
    return out


def eligible(corpus: str) -> list[dict[str, Any]]:
    paths = CORPORA[corpus]
    out = []
    cache: dict[str, list[str]] = {}
    for record in read_gz_lines(paths["extraction"]):
        roots = [n for n in record["nodes"] if n["parent"] is None]
        if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic") or generated(record["declaration"]):
            continue
        steps = counter.derive_steps(record["nodes"])
        if not MIN_STEPS <= len(steps) <= MAX_STEPS:
            continue
        parents = counter.dependency_graph(steps)
        if not all(len(ps) <= 1 for ps in parents) or any(len(s["consumed"]) != 1 for s in steps):
            continue
        produced = [g for s in steps for g in s["produced"]]
        consumed = [s["consumed"][0] for s in steps]
        roots_consumed = [c for c in consumed if c not in produced]
        if len(roots_consumed) != 1 or sorted(set(produced)) != sorted(set(consumed) - set(roots_consumed)):
            continue
        count = counter.forest_linearizations(parents)
        if not MIN_ORDERINGS <= count <= MAX_ORDERINGS:
            continue
        path = paths["source"] / (record["module"].replace(".", "/") + ".lean")
        if record["module"] not in cache:
            cache[record["module"]] = path.read_text(encoding="utf-8").split("\n")
        texts = step_texts(record, steps, cache[record["module"]])
        if texts is None:
            continue
        out.append({"corpus": corpus, "module": record["module"], "declaration": record["declaration"],
                    "source": path.relative_to(ROOT).as_posix(), "byLine": roots[0]["line"],
                    "steps": len(steps), "orderings": count})
    return sorted(out, key=lambda e: (e["module"], e["byLine"], e["declaration"]))


def draw_sample() -> tuple[list[dict[str, Any]], dict[str, int]]:
    rng = random.Random(SEED)
    sample, pools = [], {}
    for corpus in CORPORA:
        pool = eligible(corpus)
        pools[corpus] = len(pool)
        sample += rng.sample(pool, min(PER_CORPUS, len(pool)))
    return sample, pools


def registration_payload(sample: list[dict[str, Any]], pools: dict[str, int]) -> dict[str, Any]:
    return {
        "experiment": "orderings-replay-v0.1",
        "question": "how many of the orderings counted by L replay as Lean scripts in the theorem's own context",
        "sample": {"rule": f"seed {SEED}; for each corpus of step 1, up to {PER_CORPUS} proofs drawn uniformly from those "
                           f"with one root `by` block, a name that is not generated, {MIN_STEPS} to {MAX_STEPS} steps, a "
                           f"forest graph whose steps each consume one goal, {MIN_ORDERINGS} to {MAX_ORDERINGS} "
                           "orderings, and steps that can be cut out of the source one line each (every other line of "
                           "the body blank, a comment, or a bullet; no step line with `<;>`, `;`, a nested `by`, or a "
                           "structural tactic)",
                   "pools": pools, "count": len(sample),
                   "libraryExtractionSha256": sha256_file(library.EXTRACTION),
                   "sliceExtractionSha256": sha256_file(slice_.EXTRACTION)},
        "procedure": ["a fresh REPL per proof; the theorem is stated as an `example` in its module's context before "
                      "it, as in the search experiments",
                      "each ordering, the original first, is replayed step by step: `rotate_left k` brings the goal the "
                      "step consumed in the original proof to the front, then the step's tactic text runs",
                      "an ordering replays when every tactic succeeds, every step leaves exactly the number of goals "
                      "the graph says it creates, no goal is left, and the script re-verifies from the statement",
                      "a proof whose original order does not replay is reported and excluded from the measure"],
        "measures": {"replayed": "the orderings other than the original that replay, over all orderings other than "
                                 "the original of the proofs whose original order replays",
                     "failures": "for each ordering that does not replay, the first failure: goal selection, tactic "
                                 "error, goal count, goal missing, goals left, or verification"},
        "hypotheses": {"H29": f"at least {THRESHOLD:.0%} of the orderings other than the original replay"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the procedure was exercised on two eligible library proofs outside the "
                                                "sample: one could not be stated as an example, and all 21 orderings of "
                                                "the other replayed after `pick_goal`, which modules without Mathlib "
                                                "lack, was replaced by the core `rotate_left`; no proof of the sample "
                                                "had been replayed",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def linear_extensions(parents: list[set[int]]) -> list[list[int]]:
    n = len(parents)
    out: list[list[int]] = []

    def extend(prefix: list[int], placed: set[int]) -> None:
        if len(prefix) == n:
            out.append(list(prefix))
            return
        for i in range(n):
            if i not in placed and parents[i] <= placed:
                prefix.append(i)
                placed.add(i)
                extend(prefix, placed)
                placed.discard(i)
                prefix.pop()

    extend([], set())
    return out


def replay_order(repl: LeanRepl, session: Any, task: Any, steps: list[dict[str, Any]], texts: list[str],
                 root_goal: str, order: list[int]) -> dict[str, Any]:
    labels = [root_goal]
    proof_state = task.proof_state
    script: list[str] = []
    mvar_goals = 0
    for position, index in enumerate(order):
        step = steps[index]
        goal = step["consumed"][0]
        if goal not in labels:
            return {"ok": False, "failure": "goal missing", "at": position}
        k = labels.index(goal)
        if k > 0:  # `rotate_left` is core Lean, so it also works in modules without Mathlib
            moved = repl.tactic(proof_state, f"rotate_left {k}")
            if moved is None:
                return {"ok": False, "failure": "goal selection", "at": position}
            proof_state = moved[1]
            labels = labels[k:] + labels[:k]
            script.append(f"rotate_left {k}")
        result = repl.tactic(proof_state, texts[index])
        if result is None:
            return {"ok": False, "failure": "tactic error", "at": position}
        goals, proof_state = result
        mvar_goals += sum(1 for g in goals if re.search(r"(^|[\s(\[,])\?[\w.]", g.split("⊢")[-1]))
        if len(goals) != len(labels) - 1 + len(step["produced"]):
            return {"ok": False, "failure": "goal count", "at": position}
        labels = list(step["produced"]) + labels[1:]
        script.append(texts[index])
    if labels:
        return {"ok": False, "failure": "goals left", "at": len(order)}
    if not session.verify(task, script):
        return {"ok": False, "failure": "verification", "at": len(order)}
    return {"ok": True, "mvarGoals": mvar_goals}


def replay_proof(entry: dict[str, Any]) -> dict[str, Any]:
    head = {k: entry[k] for k in ("corpus", "module", "declaration", "steps", "orderings")}
    record = next(r for r in read_gz_lines(CORPORA[entry["corpus"]]["extraction"])
                  if r["module"] == entry["module"] and r["declaration"] == entry["declaration"])
    steps = counter.derive_steps(record["nodes"])
    parents = counter.dependency_graph(steps)
    lines = (ROOT / entry["source"]).read_text(encoding="utf-8").split("\n")
    texts = step_texts(record, steps, lines)
    produced = {g for s in steps for g in s["produced"]}
    root_goal = next(s["consumed"][0] for s in steps if s["consumed"][0] not in produced)
    orders = linear_extensions(parents)
    original = list(range(len(steps)))
    orders = [original] + [o for o in orders if o != original]
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        session = harness.ModuleSession(repl, entry["module"], ROOT / entry["source"],
                                        [(entry["declaration"], entry["byLine"])])
        task = None
        for _, made in session.tasks_in_order():
            task = made
            break
        if task is None:
            return head | {"stated": False, "seconds": round(time.monotonic() - started, 1)}
        outcomes = [replay_order(repl, session, task, steps, texts, root_goal, order) for order in orders]
    except ReplTimeout:
        return head | {"stated": True, "abandoned": "repl timeout", "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()
    return head | {"stated": True, "enumerated": len(orders), "original": outcomes[0],
                   "others": [o | {"order": order} for o, order in zip(outcomes[1:], orders[1:])],
                   "seconds": round(time.monotonic() - started, 1)}


def run_all(sample: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    done: set[tuple[str, str]] = set()
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
        done = {(r["module"], r["declaration"]) for r in rows}
    lock = threading.Lock()

    def guarded(entry: dict[str, Any]) -> dict[str, Any]:
        try:
            return replay_proof(entry)
        except Exception as error:  # noqa: BLE001  an unexpected failure is recorded, never lost
            return {k: entry[k] for k in ("corpus", "module", "declaration", "steps", "orderings")} | \
                {"stated": None, "error": f"{type(error).__name__}: {error}"[:300]}

    todo = [e for e in sample if (e["module"], e["declaration"]) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for row in pool.map(guarded, todo):
            with lock:
                rows.append(row)
                with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
                others = row.get("others", [])
                print(json.dumps({"proof": row["declaration"], "original": (row.get("original") or {}).get("ok"),
                                  "replayed": sum(1 for o in others if o["ok"]), "of": len(others),
                                  "error": row.get("error")}), flush=True)
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    replayable = [r for r in rows if r.get("original", {}).get("ok")]
    others = [o for r in replayable for o in r["others"]]
    ok = sum(1 for o in others if o["ok"])
    failures: dict[str, int] = {}
    for o in others:
        if not o["ok"]:
            failures[o["failure"]] = failures.get(o["failure"], 0) + 1
    original_failures: dict[str, int] = {}
    for r in rows:
        if r.get("original") and not r["original"]["ok"]:
            original_failures[r["original"]["failure"]] = original_failures.get(r["original"]["failure"], 0) + 1
    per_proof = sorted(sum(1 for o in r["others"] if o["ok"]) / len(r["others"]) for r in replayable if r["others"])
    return {"experiment": "orderings-replay-v0.1", "preregistrationSha256": sha256_file(PREREG),
            "proofs": len(rows), "stated": sum(1 for r in rows if r.get("stated")),
            "errors": sum(1 for r in rows if r.get("error")), "abandoned": sum(1 for r in rows if r.get("abandoned")),
            "originalReplays": len(replayable), "originalFailures": original_failures,
            "orderings": len(others), "replayed": ok, "fraction": ok / len(others) if others else None,
            "failures": failures, "proofsAllReplay": sum(1 for f in per_proof if f == 1.0),
            "proofsNoneReplay": sum(1 for f in per_proof if f == 0.0), "proofsWithOthers": len(per_proof),
            "hypotheses": {"H29": {"supported": None if not others else ok / len(others) >= THRESHOLD}},
            "resultsSha256": sha256_file(RESULTS)}


def write_report(summary: dict[str, Any]) -> None:
    s = summary
    fraction = "n/a" if s["fraction"] is None else f"{s['fraction']:.1%}"
    lines = ["# Replaying the orderings of goal-origin graphs (orderings replay v0.1)", "",
             "Sample, procedure, and hypothesis are frozen in `preregistration.json` (SHA-256",
             "`" + s["preregistrationSha256"] + "`).", "",
             f"Proofs: {s['proofs']}; stated: {s['stated']}; original order replays: {s['originalReplays']} "
             f"(failures of the original: {s['originalFailures']}).", "",
             f"Other orderings: {s['orderings']}; replayed: {s['replayed']} ({fraction}); first failures: "
             f"{s['failures']}.", "",
             f"Proofs whose other orderings all replay: {s['proofsAllReplay']} of {s['proofsWithOthers']}; none "
             f"replay: {s['proofsNoneReplay']}.", "",
             f"H29 (at least {THRESHOLD:.0%} of the other orderings replay): supported: "
             f"{s['hypotheses']['H29']['supported']}."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        sample, pools = draw_sample()
        write_lf(SAMPLE, json.dumps(sample, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(sample, pools)
        payload["sampleSha256"] = sha256_file(SAMPLE)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(sample)} proofs (pools {pools}): {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["sampleSha256"] != sha256_file(SAMPLE):
        raise SystemExit("the sample changed since registration")
    for name in ("counter", "harness", "repl"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    sample = json.loads(SAMPLE.read_text(encoding="utf-8"))
    if args.run:
        rows = run_all(sample, args.workers)
        order = {(e["module"], e["declaration"]): i for i, e in enumerate(sample)}
        rows.sort(key=lambda r: order[(r["module"], r["declaration"])])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: summary[k] for k in ("proofs", "originalReplays", "orderings", "replayed", "hypotheses")}))
        return 0
    rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if summarize(rows) != json.loads(SUMMARY.read_text(encoding="utf-8")):
        raise SystemExit("the committed summary does not follow from the committed results")
    print(f"orderings-replay-check-ok: proofs={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
