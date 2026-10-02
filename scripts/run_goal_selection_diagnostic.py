#!/usr/bin/env python3
"""Goal-selection diagnostic v0.1: constructed tasks whose goals are coupled, or independent, by design.

  python scripts/run_goal_selection_diagnostic.py --register
  python scripts/run_goal_selection_diagnostic.py --run [--workers W]
  python scripts/run_goal_selection_diagnostic.py --check-committed

Each task is a statement and a fixed tactic prefix, posed in a full-Mathlib REPL; the four arms of
goal-selection-v0.1 then search from the state the prefix leaves (`run_search_goal_selection.run_development_unit`).
In a coupled task the prefix leaves the witness goals first and the equations that pin them last, so that a
first-goal search must choose a witness blind; in an independent task the goals share no metavariable.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import subprocess
import time
from pathlib import Path
from typing import Any

import run_search_goal_selection as runner
from run_linearizations import sha256_file, write_lf

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "experiments" / "goal-selection-diagnostic-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
ONE = ["refine ⟨?_, ?_, ?_⟩"]
TWO = ["refine ⟨?_, ?_, ?_, ?_, ?_⟩"]
PAIR = ["refine ⟨?_, ?_⟩"]
TASKS = [
    {"declaration": "square_sixteen", "statement": "∃ n : ℕ, n ^ 2 = 16 ∧ n = 4", "prefix": ONE, "kind": "coupled"},
    {"declaration": "affine_seven", "statement": "∃ n : ℕ, 2 * n + 1 = 7 ∧ n = 3", "prefix": ONE, "kind": "coupled"},
    {"declaration": "mod_five", "statement": "∃ n : ℕ, n % 5 = 2 ∧ n = 7", "prefix": ONE, "kind": "coupled"},
    {"declaration": "triple_twelve", "statement": "∃ n : ℕ, n * 3 = 12 ∧ n = 4", "prefix": ONE, "kind": "coupled"},
    {"declaration": "truncated_sub", "statement": "∃ n : ℕ, n - 2 = 5 ∧ n = 7", "prefix": ONE, "kind": "coupled"},
    {"declaration": "sub_from_ten", "statement": "∃ n : ℕ, 10 - n = 4 ∧ n = 6", "prefix": ONE, "kind": "coupled"},
    {"declaration": "half_eight", "statement": "∃ n : ℕ, n / 2 = 4 ∧ n = 8", "prefix": ONE, "kind": "coupled"},
    {"declaration": "cube_eight", "statement": "∃ n : ℕ, n * n * n = 8 ∧ n = 2", "prefix": ONE, "kind": "coupled"},
    {"declaration": "pair_sum", "statement": "∃ a b : ℕ, a + b = 5 ∧ a = 2 ∧ b = 3", "prefix": TWO, "kind": "coupled"},
    {"declaration": "pair_product", "statement": "∃ a b : ℕ, a * b = 12 ∧ a = 3 ∧ b = 4", "prefix": TWO,
     "kind": "coupled"},
    {"declaration": "two_facts", "statement": "2 * 3 = 6 ∧ 5 + 5 = 10", "prefix": PAIR, "kind": "independent"},
    {"declaration": "order_facts", "statement": "(3 : ℕ) < 4 ∧ (7 : ℕ) ≠ 8", "prefix": PAIR, "kind": "independent"},
    {"declaration": "divisibility", "statement": "(2 : ℕ) ∣ 4 ∧ 9 % 2 = 1", "prefix": PAIR, "kind": "independent"},
    {"declaration": "three_facts", "statement": "10 - 3 = 7 ∧ 2 ^ 3 = 8 ∧ 1 + 1 = 2", "prefix": ONE,
     "kind": "independent"},
    {"declaration": "true_and_sum", "statement": "True ∧ (4 : ℕ) = 2 + 2", "prefix": PAIR, "kind": "independent"},
    {"declaration": "quotient_square", "statement": "(6 : ℕ) / 2 = 3 ∧ 7 * 7 = 49", "prefix": PAIR,
     "kind": "independent"},
    {"declaration": "forall_first", "statement": "(∀ n : ℕ, n + 0 = n) ∧ 3 * 3 = 9", "prefix": PAIR,
     "kind": "independent"},
    {"declaration": "comm_first", "statement": "(∀ a b : ℕ, a + b = b + a) ∧ 2 ^ 2 = 4", "prefix": PAIR,
     "kind": "independent"},
]
PREDICTIONS = {
    "D1": "No coupled task is proved by first or by firstText.",
    "D2": "Every coupled task is proved by any and by anyMultiset.",
    "D3": "Every proof of a coupled task found by any or anyMultiset acts, at some step, on a goal other than the "
          "first that shares a metavariable with another open goal (coupling replay of the found proof).",
    "D4": "Every independent task that some arm proves is proved by first.",
}
IMPLEMENTATIONS = {"diagnostic": Path(__file__).resolve()} | runner.IMPLEMENTATIONS


def task_of(row: dict[str, Any]) -> str:
    return row["declaration"]


def coupled_choice(row: dict[str, Any]) -> bool | None:
    """Whether the replayed proof acts on a coupled non-first goal; None without a replay."""
    probe = row.get("probe")
    if not probe:
        return None
    return bool(probe.get("closed")) and any(step["position"] > 1 and step["chosenCoupled"] is True
                                             for step in probe.get("steps", []))


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    latest = {(task_of(r), r["arm"]): r for r in rows}
    tasks = []
    for task in TASKS:
        arms = {}
        for arm in runner.ARMS:
            row = latest.get((task["declaration"], arm), {})
            result = row.get("result")
            arms[arm] = None if result is None else {
                "proved": bool(result["proof"]), "expansions": len(result["expansions"]),
                "steps": runner.result_steps(result), "stepsAtProof": runner.proof_steps(result),
                "proof": result["proof"], "coupledChoice": coupled_choice(row) if result["proof"] else None}
        tasks.append({"declaration": task["declaration"], "kind": task["kind"], "arms": arms})
    complete = all(cell is not None for t in tasks for cell in t["arms"].values())
    coupled = [t for t in tasks if t["kind"] == "coupled"]
    independent = [t for t in tasks if t["kind"] == "independent"]
    if not complete:
        predictions = dict.fromkeys(PREDICTIONS, "incomplete")
    else:
        free = [t["arms"][a] for t in coupled for a in ("any", "anyMultiset") if t["arms"][a]["proved"]]
        verdict = {True: "holds", False: "fails"}
        predictions = {
            "D1": verdict[not any(t["arms"][a]["proved"] for t in coupled for a in ("firstText", "first"))],
            "D2": verdict[all(t["arms"][a]["proved"] for t in coupled for a in ("any", "anyMultiset"))],
            "D3": verdict[all(c["coupledChoice"] is True for c in free)] if free else "untested",
            "D4": verdict[all(t["arms"]["first"]["proved"] for t in independent
                              if any(cell["proved"] for cell in t["arms"].values()))],
        }
    return {"experiment": "goal-selection-diagnostic-v0.1", "tasks": tasks, "complete": complete,
            "units": len(latest), "errors": sum(bool(r.get("error")) for r in latest.values()),
            "abandoned": sum(bool(r.get("abandoned")) for r in latest.values()), "predictions": predictions}


def report(summary: dict[str, Any]) -> str:
    lines = ["# Goal-selection diagnostic v0.1", "",
             "Constructed tasks, each posed with a fixed prefix; cells give expansions and candidate applications, "
             "with the applications at the proof, or a dash without a proof.", "",
             "| Task | Kind | " + " | ".join(runner.ARMS) + " |", "| --- | --- |" + " ---: |" * len(runner.ARMS)]
    for task in summary["tasks"]:
        cells = []
        for arm in runner.ARMS:
            cell = task["arms"][arm]
            cells.append("missing" if cell is None else
                         f"{cell['expansions']} / {cell['stepsAtProof']}" if cell["proved"] else
                         f"{cell['expansions']} / {cell['steps']}, -")
        lines.append(f"| {task['declaration']} | {task['kind']} | " + " | ".join(cells) + " |")
    lines += ["", "## Predictions", "", "| Item | Statement | Result |", "| --- | --- | --- |"]
    for name, text in PREDICTIONS.items():
        lines.append(f"| {name} | {text} | {summary['predictions'][name]} |")
    lines += ["", "## Proofs found", ""]
    for task in summary["tasks"]:
        for arm in runner.ARMS:
            cell = task["arms"][arm]
            if cell and cell["proved"]:
                lines.append(f"- {task['declaration']}, {arm}: `{'; '.join(cell['proof'])}`"
                             + ("" if cell["coupledChoice"] is None else f" (coupled choice: {cell['coupledChoice']})"))
    return "\n".join(lines) + "\n"


def registration_payload() -> dict[str, Any]:
    return {"experiment": "goal-selection-diagnostic-v0.1",
            "question": "on constructed tasks whose goals are coupled, or independent, by design, does free goal choice "
                        "prove what first-goal search cannot, and only through coupling",
            "tasks": TASKS,
            "arms": "the four arms of goal-selection-v0.1 (run_search_goal_selection.search): budget "
                    f"{runner.BUDGET} expansions, the typed arms also limited to {runner.SEARCH_SECONDS} s of search",
            "environment": "a fresh full-Mathlib REPL per unit; the statement posed as an example, the prefix applied, "
                           "then the search; proofs verified from the statement with the prefix; found proofs of the "
                           "typed arms replayed for coupling",
            "predictions": PREDICTIONS,
            "development": "four other constructed tasks (two coupled, two independent) were run during development; "
                           "none is reused here",
            "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
            "resultsAbsentAtRegistration": True,
            "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles"}


def validate_registration() -> None:
    prereg = runner.read_json(PREREG)
    if prereg["tasks"] != TASKS or prereg["predictions"] != PREDICTIONS:
        raise SystemExit("tasks or predictions changed since registration")
    expected = dict(prereg["implementationSha256"])
    for amendment in sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1])):
        expected.update(runner.read_json(amendment).get("implementationSha256AfterAmendment", {}))
    for name, path in IMPLEMENTATIONS.items():
        if expected[name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration or amendment")


def guarded(task: dict[str, Any], arm: str) -> dict[str, Any]:
    try:
        return runner.run_development_unit(task, arm)
    except Exception as error:  # noqa: BLE001
        return {"module": "development", "declaration": task["declaration"], "arm": arm,
                "error": f"{type(error).__name__}: {error}"[:300]}


def run(workers: int) -> list[dict[str, Any]]:
    rows = runner.read_rows(RESULTS) if RESULTS.exists() else []
    done = {(task_of(r), r["arm"]) for r in rows if "result" in r}
    units = [(t, a) for t in TASKS for a in runner.ARMS if (t["declaration"], a) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for future in concurrent.futures.as_completed([pool.submit(guarded, t, a) for t, a in units]):
            row = future.result()
            rows.append(row)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")
            runner.print_row(row)
    order = {(t["declaration"], a): i for i, (t, a) in enumerate((t, a) for t in TASKS for a in runner.ARMS)}
    latest = {(task_of(r), r["arm"]): r for r in rows}
    return sorted(latest.values(), key=lambda r: order[(task_of(r), r["arm"])])


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ("register", "run", "check-committed"):
        mode.add_argument("--" + name, action="store_true")
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("workers must be positive")
    if args.register:
        if PREREG.exists() or RESULTS.exists():
            raise SystemExit("registration or experiment data already exist")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        runner.write_json(PREREG, registration_payload())
        print(f"registered {len(TASKS)} tasks: {PREREG}")
        return 0
    validate_registration()
    if args.run:
        relative = PREREG.relative_to(ROOT).as_posix()
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
        published = subprocess.check_output(["git", "for-each-ref", f"--contains={commit}", "refs/remotes/"],
                                            cwd=ROOT, text=True).strip() if commit else ""
        clean = subprocess.check_output(["git", "status", "--porcelain", "--", relative], cwd=ROOT, text=True).strip()
        if not commit or not published or clean:
            raise SystemExit("commit and push registration before running (checked against local remote-tracking refs)")
        rows = run(args.workers)
        write_lf(RESULTS, "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows) | {"resultsSha256": sha256_file(RESULTS), "preregistrationSha256": sha256_file(PREREG)}
        runner.write_json(SUMMARY, summary)
        write_lf(REPORT, report(summary))
        print(json.dumps({"diagnostic": summary["predictions"], "complete": summary["complete"]}))
        return 0
    rows = runner.read_rows(RESULTS)
    summary = runner.read_json(SUMMARY)
    recomputed = summarize(rows) | {"resultsSha256": sha256_file(RESULTS), "preregistrationSha256": sha256_file(PREREG)}
    if summary != recomputed or REPORT.read_text(encoding="utf-8") != report(recomputed):
        raise SystemExit("committed summary or report does not follow from results")
    print(f"goal-selection-diagnostic-check-ok: {summary['predictions']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
