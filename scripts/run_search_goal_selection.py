#!/usr/bin/env python3
"""Goal-selection v0.1: the fixed menu on first goals or on every open goal.

Development and smoke outputs require --output-dir outside the repository.
Registration precedes the experiment; --run resumes its recorded units.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import random
import subprocess
import time
from pathlib import Path
from typing import Any

import goal_identity_typed as gi
import run_search_deep as deep
import search_goal_selection as selection
import search_harness as harness
from lean_repl import ReplTimeout
from run_linearizations import find_lake, sha256_file, write_lf

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "experiments" / "goal-selection-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
SOURCE = ROOT / "experiments" / "search-v0.3"
ARMS = ("firstText", "first", "any", "anyMultiset")
PAIRS = (("firstText", "first"), ("first", "any"), ("any", "anyMultiset"), ("first", "anyMultiset"))
SAMPLE_SEED = 20260930
SAMPLE_SIZE = 200
SEARCH_SECONDS = 7200
MAX_ABANDONMENTS = 2
ALPHA = 0.05
BOOTSTRAP_SEED = 20261001
BOOTSTRAP_RESAMPLES = 10000
EXPORT_FAILURE_CEILING = 0.03
COUPLING = EXPERIMENT / "coupling.json"
HYPOTHESES = {
    "H78": "At equal expansions first proves more theorems than any: among tasks completed in both arms, theorems "
           "proved by first only outnumber those proved by any only (one-sided exact sign test).",
    "H79": "Every theorem proved by any or by anyMultiset and not by first owes it to coupling: replayed step by "
           "step, its found proof acts at least once on a goal other than the first that shares a metavariable "
           "with another open goal. A replay that fails to verify or close, or whose coupling is unknown at every "
           "such step, counts against. With no such theorem H79 is untested.",
    "H80": "anyMultiset proves more theorems than any (one-sided exact sign test on the tasks completed in both).",
    "H81": "The share of expansions that are typed order duplicates is larger in any than in first: any's share "
           "minus first's, pooled over the tasks completed in both arms, bootstrapped over those tasks "
           f"({BOOTSTRAP_RESAMPLES:,} resamples, seed {BOOTSTRAP_SEED}); one-sided p is the number of resamples "
           f"with a difference at most zero, plus one, over {BOOTSTRAP_RESAMPLES + 1:,}.",
    "family": f"H78, H80 and H81 are decided at {ALPHA} after Holm's adjustment; H79 has no p-value.",
}
CHECKS = {
    "C1": "All 200 firstText sample units reproduce search-v0.3's menu whole-state search: posing, proof found, "
          "and all expansion records.",
    "C2": "anyMultiset expands no state whose unordered typed key was already expanded under another ordered key.",
    "C3": f"Typed exports fail on at most {EXPORT_FAILURE_CEILING:.0%} of the exports the typed arms attempt.",
}
BUDGET = 24
STEP_BUDGET = BUDGET * len(harness.MENU)
IMPLEMENTATIONS = {name: ROOT / "scripts" / file for name, file in {
    "selection": "search_goal_selection.py", "runner": "run_search_goal_selection.py",
    "identity": "goal_identity_typed.py", "harness": "search_harness.py",
    "faithful": "search_faithful.py", "repl": "lean_repl.py", "deepRunner": "run_search_deep.py",
    "linearizationsRunner": "run_linearizations.py", "v1Runner": "run_search.py",
    "legacyIdentity": "goal_identity.py", "renaming": "renaming.py",
    "textKeys": "search_keys.py", "sliceRunner": "run_mathlib_slice.py",
}.items()}
CONTROLS = [
    {"declaration": "coupled_square", "statement": "∃ n : ℕ, n * n = 9 ∧ n = 3",
     "prefix": ["refine ⟨?_, ?_, ?_⟩"], "kind": "coupled"},
    {"declaration": "independent_arithmetic", "statement": "2 + 2 = 4 ∧ 3 * 3 = 9",
     "prefix": ["refine ⟨?_, ?_⟩"], "kind": "independent"},
    {"declaration": "coupled_sum", "statement": "∃ n : ℕ, n + n = 6 ∧ n = 3",
     "prefix": ["refine ⟨?_, ?_, ?_⟩"], "kind": "coupled"},
    {"declaration": "independent_true", "statement": "True ∧ True",
     "prefix": ["refine ⟨?_, ?_⟩"], "kind": "independent"},
]
DEVELOPMENT = ("Nat.add_assoc", "Nat.mul_assoc", "List.reverse_reverse", "List.map_id",
               "Nat.add_left_comm", "Nat.mul_left_comm", "List.append_assoc", "Nat.zero_add",
               "Nat.mul_one", "List.length_reverse")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def read_rows(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_json(path: Path, value: Any) -> None:
    write_lf(path, json.dumps(value, indent=1, ensure_ascii=False) + "\n")


def task_key(row: dict[str, Any]) -> tuple[str, str]:
    return row["module"], row["declaration"]


def unit_key(row: dict[str, Any]) -> tuple[str, str, str]:
    return *task_key(row), row["arm"]


def latest_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    latest = {}
    counts: dict[tuple[str, str, str], int] = {}
    for row in rows:
        key = unit_key(row)
        counts[key] = max(counts.get(key, 0) + bool(row.get("abandoned")), row.get("abandonments", 0))
        latest[key] = row | {"abandonments": counts[key]}
    return list(latest.values())


def baseline_sample(tasks: list[dict[str, Any]], seed: int = SAMPLE_SEED) -> list[dict[str, Any]]:
    baseline = {task_key(r): r for r in read_rows(SOURCE / "results.jsonl")
                if r["arm"] == "menu" and r["search"] == "whole"}
    proved = sorted(task_key(t) for t in tasks if baseline.get(task_key(t), {}).get("result", {}).get("proof"))
    others = sorted(task_key(t) for t in tasks if task_key(t) not in proved and
                    "result" in baseline.get(task_key(t), {}))
    if len(proved) > SAMPLE_SIZE or len(proved) + len(others) < SAMPLE_SIZE:
        raise ValueError("baseline cannot supply the registered 200-task sample")
    chosen = set(proved + random.Random(seed).sample(others, SAMPLE_SIZE - len(proved)))
    return sorted((t for t in tasks if task_key(t) in chosen), key=task_key)


def result_steps(result: dict[str, Any]) -> int:
    if "steps" in result:
        return result["steps"]
    expansions = result["expansions"]
    if not result["proof"]:
        return sum(e["candidates"] for e in expansions)
    return sum(e["candidates"] for e in expansions[:-1]) + harness.MENU.index(result["proof"][-1]) + 1


def proof_steps(result: dict[str, Any]) -> int | None:
    return result.get("stepsAtProof", result_steps(result) if result["proof"] else None)


def search(repl: Any, arm: str, proof_state: int, goals: list[str], verifier: Any,
           budget: int = BUDGET) -> dict[str, Any]:
    if arm == "firstText":
        return harness.whole_state_search(repl, proof_state, goals, harness.menu_proposer, budget, verifier)
    if arm not in ARMS:
        raise ValueError(f"unknown arm: {arm}")
    return selection.any_goal_search(repl, proof_state, goals, harness.menu_proposer, budget, verifier,
                                     identify="multiset" if arm == "anyMultiset" else "ordered",
                                     positions="first" if arm == "first" else "all", time_limit=SEARCH_SECONDS)


def run_unit(task: dict[str, Any], arm: str, budget: int = BUDGET,
             probe: list[str] | None = None) -> dict[str, Any]:
    """One task in its own module and a fresh REPL, as run_search_deep.run_unit."""
    head = {"module": task["module"], "declaration": task["declaration"], "arm": arm, "search": "whole"}
    started = time.monotonic()
    repl = None
    constructed = False
    try:
        repl = selection.ClosingRepl(find_lake(), imports=None)
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session_type = harness.ModuleSession if arm == "firstText" else selection.ExportingSession
        session = session_type(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            constructed = True
            verifier = lambda script: session.verify(made, script)
            if probe is not None:
                return head | {"constructed": True, "verified": verifier(probe),
                               "probe": selection.coupling_probe(repl, made.proof_state, probe)}
            setup_seconds = round(time.monotonic() - started, 1)
            result = search(repl, arm, made.proof_state, [made.goal], verifier, budget)
            if repl.restarts:
                raise ReplTimeout("search restarted the task environment")
            return head | {"constructed": True, "result": result,
                           "fastExport": getattr(repl, "typed_fast_export", False),
                           "setupSeconds": setup_seconds}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": constructed, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        if repl is not None:
            repl.close()


def run_development_unit(task: dict[str, Any], arm: str) -> dict[str, Any]:
    head = {"module": "development", "declaration": task["declaration"], "arm": arm, "search": "whole",
            "kind": task.get("kind", "theorem"), "prefix": task.get("prefix", [])}
    repl = selection.ClosingRepl(find_lake())
    try:
        if arm != "firstText":
            repl.env = selection.define_exporter(repl, repl.env)
        if "statement" in task:
            header = f"example : {task['statement']} := by"
            response = repl.command(header + "\n  sorry")
            sorries = response.get("sorries") or []
            if not sorries or any(m.get("severity") == "error" for m in response.get("messages", [])):
                return head | {"constructed": False, "messages": response.get("messages", [])}
            made = harness.Task(task["declaration"], [], header, sorries[0]["goal"])
            proof_state = int(sorries[0]["proofState"])
        else:
            posed = harness.make_task(repl, task["declaration"])
            if posed is None:
                return head | {"constructed": False}
            made, proof_state = posed
        goals = [made.goal]
        for step in head["prefix"]:
            result = repl.tactic(proof_state, step)
            if result is None:
                return head | {"constructed": False, "reason": "prefix failed"}
            goals, proof_state = result
        verifier = lambda script: harness.verify_script(repl, made, head["prefix"] + script)
        result = search(repl, arm, proof_state, goals, verifier)
        if repl.restarts:
            raise ReplTimeout("search restarted the task environment")
        probe = selection.coupling_probe(repl, proof_state, result["proof"]) \
            if arm != "firstText" and result["proof"] else None
        root_export = selection.export(repl, proof_state) if arm != "firstText" else None
        return head | {"constructed": True, "rootGoals": goals,
                       "rootGroups": gi.groups(root_export) if root_export is not None else None,
                       "fastExport": getattr(repl, "typed_fast_export", False), "result": result, "probe": probe}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout"}
    finally:
        repl.close()


def sign_test(wins: int, losses: int) -> float | None:
    """Exact upper binomial tail under equal probability, with no test when there are no discordances."""
    n = wins + losses
    return sum(math.comb(n, i) for i in range(wins, n + 1)) / 2 ** n if n else None


def replication(rows: list[dict[str, Any]], sample: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    old = {task_key(r): r for r in read_rows(SOURCE / "results.jsonl")
           if r["arm"] == "menu" and r["search"] == "whole"}
    compared = matched = 0
    mismatches = []
    for row in latest_rows(rows):
        if row["arm"] != "firstText" or task_key(row) not in old:
            continue
        committed = old[task_key(row)]
        compared += 1
        got, want = row.get("result"), committed.get("result")
        same = row.get("constructed") == committed.get("constructed")
        same = same and bool(got is not None) == bool(want is not None)
        if same and got is not None:
            records = lambda r: [{k: e[k] for k in deep.WHOLE_KEYS} for e in r["expansions"]]
            same = bool(got["proof"]) == bool(want["proof"]) and records(got) == records(want)
        if same and not row.get("error") and not row.get("abandoned"):
            matched += 1
        else:
            mismatches.append({"module": row["module"], "declaration": row["declaration"]})
    result = {"compared": compared, "matched": matched, "mismatches": mismatches}
    if sample is not None:
        result["sampleMatches"] = {task_key(r) for r in latest_rows(rows) if r["arm"] == "firstText"} == \
            {task_key(t) for t in sample}
    return result


def fraction(numerator: int, denominator: int) -> float | None:
    return numerator / denominator if denominator else None


def holm(pvalues: dict[str, float | None], alpha: float = ALPHA) -> dict[str, bool]:
    """Holm's step-down decisions; a missing p-value (no discordant tasks) is never rejected."""
    order = sorted(pvalues, key=lambda name: (2.0 if pvalues[name] is None else pvalues[name], name))
    decisions = dict.fromkeys(pvalues, False)
    for rank, name in enumerate(order):
        p = pvalues[name]
        if p is None or p > alpha / (len(order) - rank):
            break
        decisions[name] = True
    return decisions


def pooled_difference(cells: list[tuple[int, int, int, int]]) -> float:
    """any's pooled typed order-duplicate share minus first's; cells are per task
    (first duplicates, first support, any duplicates, any support), each support positive."""
    first_duplicates, first_support, any_duplicates, any_support = map(sum, zip(*cells))
    return any_duplicates / any_support - first_duplicates / first_support


def order_redundancy(cells: list[tuple[int, int, int, int]]) -> dict[str, Any]:
    """H81: the pooled difference, a percentile interval and a one-sided p-value from a bootstrap over tasks."""
    if not cells:
        return {"tasks": 0, "difference": None, "interval": None, "p": None}
    rng = random.Random(BOOTSTRAP_SEED)
    draws = sorted(pooled_difference(rng.choices(cells, k=len(cells))) for _ in range(BOOTSTRAP_RESAMPLES))
    return {"tasks": len(cells), "difference": pooled_difference(cells),
            "interval": [draws[int(0.025 * BOOTSTRAP_RESAMPLES)], draws[int(0.975 * BOOTSTRAP_RESAMPLES) - 1]],
            "p": (sum(d <= 0 for d in draws) + 1) / (BOOTSTRAP_RESAMPLES + 1)}


def coupling_decision(free_only: list[dict[str, Any]], probes: list[dict[str, Any]] | None) -> dict[str, Any]:
    """H79 from the committed replays of the free-choice-only proofs."""
    if not free_only:
        return {"status": "untested", "cases": []}
    if probes is None:
        return {"status": "pending", "cases": []}
    replays = {unit_key(p): p for p in probes}
    cases = []
    for proof in free_only:
        replay = replays.get(unit_key(proof), {})
        probe = replay.get("probe") or {}
        shown = bool(replay.get("verified")) and bool(probe.get("closed")) and \
            any(step["position"] > 1 and step["chosenCoupled"] is True for step in probe.get("steps", []))
        cases.append({"module": proof["module"], "declaration": proof["declaration"], "arm": proof["arm"],
                      "coupledChoice": shown})
    return {"status": "holds" if all(c["coupledChoice"] for c in cases) else "fails", "cases": cases}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], arms: list[str],
              probes: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    keys = {task_key(task) for task in tasks}
    rows = [r for r in latest_rows(rows) if task_key(r) in keys and r["arm"] in arms]
    by_unit = {unit_key(r): r for r in rows}
    out: dict[str, Any] = {"experiment": "goal-selection-v0.1", "tasks": len(tasks),
                           "budget": BUDGET, "typedSearchSeconds": SEARCH_SECONDS,
                           "stepBudget": STEP_BUDGET, "arms": {}, "pairs": {},
                           "freeChoiceOnlyProofs": []}
    for arm in arms:
        units = [r for r in rows if r["arm"] == arm]
        ran = [r for r in units if "result" in r]
        expansions = [e for r in ran for e in r["result"]["expansions"]]
        typed = [e for e in expansions if e.get("orderDuplicateTyped") is not None]
        multi = [e for e in expansions if e["goals"] > 1 and e.get("coupled") is not None]
        valid = sum(e["valid"] for e in expansions)
        exact = sum(e["exactDuplicates"] for e in expansions)
        multiset_support = [e for e in expansions if "multisetDuplicates" in e]
        multiset = sum(e["multisetDuplicates"] for e in multiset_support)
        order = sum(bool(e["orderDuplicate"]) for e in expansions)
        typed_order = sum(bool(e["orderDuplicateTyped"]) for e in typed)
        coupled = sum(bool(e["coupled"]) for e in multi)
        out["arms"][arm] = {
            "tasksPosed": sum(bool(r.get("constructed")) for r in units), "completed": len(ran),
            "missing": (SAMPLE_SIZE if arm == "firstText" else len(tasks)) - len(units),
            "errors": sum(bool(r.get("error")) for r in units),
            "abandoned": sum(bool(r.get("abandoned")) for r in units),
            "finalAbandoned": sum(bool(r.get("abandoned")) and r["abandonments"] >= MAX_ABANDONMENTS for r in units),
            "wallClockStops": sum(r["result"].get("stopped") == "wall-clock" for r in ran),
            "proved": sum(bool(r["result"]["proof"]) for r in ran), "expansions": len(expansions),
            "steps": sum(result_steps(r["result"]) for r in ran), "validChildren": valid,
            "orderDuplicates": order, "orderFraction": fraction(order, len(expansions)),
            "typedOrderDuplicates": typed_order, "typedOrderSupport": len(typed),
            "typedOrderFraction": fraction(typed_order, len(typed)),
            "exactDuplicates": exact, "exactFraction": fraction(exact, valid),
            "multisetDuplicates": multiset if multiset_support else None,
            "multisetFraction": fraction(multiset, sum(e["valid"] for e in multiset_support)),
            "distinctTypedMultisets": sum(r["result"].get("distinctTypedMultisets", 0) for r in ran)
                if arm != "firstText" else None,
            "coupledMultiGoalStates": coupled, "exportedMultiGoalStates": len(multi),
            "coupledFraction": fraction(coupled, len(multi)),
            "exportFailures": sum(r["result"].get("exportFailures", 0) for r in ran),
            "exportAttempts": sum(r["result"].get("exportAttempts", 0) for r in ran)}
    paired_keys = {}
    for a, b in PAIRS:
        if a not in arms or b not in arms:
            continue
        paired = [key for key in sorted(keys)
                  if all("result" in by_unit.get((*key, arm), {}) and
                         not by_unit[(*key, arm)].get("abandoned") and
                         not by_unit[(*key, arm)].get("error") for arm in (a, b))]
        paired_keys[(a, b)] = paired
        comparison = {"pairedCompleted": len(paired)}
        for measure in ("equalExpansions", "equalSteps"):
            def proved(key: tuple[str, str], arm: str) -> bool:
                result = by_unit[(*key, arm)]["result"]
                return bool(result["proof"]) and (measure == "equalExpansions" or
                                                  (proof_steps(result) is not None and
                                                   proof_steps(result) <= STEP_BUDGET))
            a_only = sum(proved(key, a) and not proved(key, b) for key in paired)
            b_only = sum(proved(key, b) and not proved(key, a) for key in paired)
            comparison[measure] = {"aOnly": a_only, "bOnly": b_only,
                                   "pAGreater": sign_test(a_only, b_only), "pBGreater": sign_test(b_only, a_only)}
        out["pairs"][f"{a}:{b}"] = comparison
    for row in rows:
        baseline = by_unit.get((*task_key(row), "first"), {}).get("result")
        if row["arm"] in ("any", "anyMultiset") and row.get("result", {}).get("proof") and baseline is not None \
                and not baseline["proof"]:
            out["freeChoiceOnlyProofs"].append({"module": row["module"], "declaration": row["declaration"],
                                               "arm": row["arm"], "proof": row["result"]["proof"],
                                               "stepsAtProof": row["result"]["stepsAtProof"]})
    out["freeChoiceOnlyProofs"].sort(key=unit_key)
    if all(arm in arms for arm in ("first", "any", "anyMultiset")):
        cells = []
        for key in paired_keys[("first", "any")]:
            cell: list[int] = []
            for arm in ("first", "any"):
                typed = [e for e in by_unit[(*key, arm)]["result"]["expansions"]
                         if e.get("orderDuplicateTyped") is not None]
                cell += [sum(bool(e["orderDuplicateTyped"]) for e in typed), len(typed)]
            if cell[1] and cell[3]:
                cells.append((cell[0], cell[1], cell[2], cell[3]))
        redundancy = order_redundancy(cells)
        choice = out["pairs"]["first:any"]["equalExpansions"]
        quotient = out["pairs"]["any:anyMultiset"]["equalExpansions"]
        holds = holm({"H78": choice["pAGreater"], "H80": quotient["pBGreater"], "H81": redundancy["p"]})
        out["hypotheses"] = {
            "H78": {"firstOnly": choice["aOnly"], "anyOnly": choice["bOnly"], "p": choice["pAGreater"],
                    "holds": holds["H78"]},
            "H79": coupling_decision(out["freeChoiceOnlyProofs"], probes),
            "H80": {"anyOnly": quotient["aOnly"], "anyMultisetOnly": quotient["bOnly"], "p": quotient["pBGreater"],
                    "holds": holds["H80"]},
            "H81": redundancy | {"holds": holds["H81"]}}
        typed_arms = [out["arms"][arm] for arm in ("first", "any", "anyMultiset")]
        failures = sum(arm["exportFailures"] for arm in typed_arms)
        attempts = sum(arm["exportAttempts"] for arm in typed_arms)
        duplicates = out["arms"]["anyMultiset"]["typedOrderDuplicates"]
        out["checks"] = {
            "C2": {"typedOrderDuplicates": duplicates, "holds": duplicates == 0},
            "C3": {"exportFailures": failures, "exportAttempts": attempts, "share": fraction(failures, attempts),
                   "holds": attempts > 0 and failures <= EXPORT_FAILURE_CEILING * attempts}}
    return out


def report(summary: dict[str, Any]) -> str:
    lines = ["# Goal-selection search v0.1", "",
             f"Candidate tasks: {summary['tasks']}; budget: {BUDGET} expansions, or {SEARCH_SECONDS} search seconds in typed arms.",
             "", "| Arm | Posed | Completed | Proved | Expansions | Steps | Text order fraction | Typed order fraction |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for arm, entry in summary["arms"].items():
        lines.append(f"| {arm} | {entry['tasksPosed']} | {entry['completed']} | {entry['proved']} | "
                     f"{entry['expansions']} | {entry['steps']} | {entry['orderFraction']} | {entry['typedOrderFraction']} |")
    lines += ["", "Typed fractions use exported support; unknown keys do not count as nonduplicates.",
              "Distinct typed multisets are summed within searches, whose task environments differ.",
              "Pairwise comparisons use tasks with completed results in both arms.",
              "At equal steps every arm's proof must close within 624 candidate applications.",
              "Wall-clock stops remain paired; abandoned units are excluded and become final after two abandonments."]
    hypotheses = summary.get("hypotheses")
    if hypotheses:
        lines += ["", "## Decisions", "", "| Item | Result |", "| --- | --- |"]
        for name in ("H78", "H80", "H81"):
            lines.append(f"| {name} | {'holds' if hypotheses[name]['holds'] else 'fails'}, p = {hypotheses[name]['p']} |")
        lines.append(f"| H79 | {hypotheses['H79']['status']} |")
        checks = ({"C1": summary["C1"]} if summary.get("C1") else {}) | summary.get("checks", {})
        for name, check in checks.items():
            lines.append(f"| {name} | {'holds' if check.get('holds') else 'fails'} |")
    lines += ["", "## Measures and paired comparisons", "", "```json",
              json.dumps({"arms": summary["arms"], "pairs": summary["pairs"], "hypotheses": hypotheses,
                          "checks": summary.get("checks"), "C1": summary.get("C1")}, indent=1),
              "```", "", "## Free-choice-only proofs", ""]
    for proof in summary["freeChoiceOnlyProofs"]:
        lines += [f"### {proof['declaration']} ({proof['arm']})", "", "```lean", *proof["proof"], "```", ""]
    return "\n".join(lines) + "\n"


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {"experiment": "goal-selection-v0.1",
            "question": "does free goal choice find proofs that first-goal search misses, and do those use coupling",
            "tasks": {"source": "search-v0.3/tasks.json", "count": len(tasks), "previouslyPosed": 1171,
                      "sourceSha256": sha256_file(SOURCE / "tasks.json"),
                      "baselineResultsSha256": sha256_file(SOURCE / "results.jsonl")},
            "arms": {"firstText": "unchanged search_harness.whole_state_search and ModuleSession; no exports or observers; C1 sample only",
                     "first": "whole-state breadth-first; first position only; joint typed ordered state key; all candidates",
                     "any": "whole-state breadth-first; all positions in order, then menu order; joint typed ordered state key; all candidates",
                     "anyMultiset": "the same search, deduplicated by joint typed unordered state key"},
            "baselineSample": {"size": SAMPLE_SIZE, "seed": SAMPLE_SEED,
                               "selection": "all menu/whole proved tasks, plus Random(seed).sample of sorted remaining posed tasks",
                               "tasks": [list(task_key(t)) for t in baseline_sample(tasks)]},
            "proposer": list(harness.MENU),
            "budget": {"expansions": BUDGET, "secondarySteps": STEP_BUDGET, "typedSearchSeconds": SEARCH_SECONDS},
            "identity": "goal_identity_typed; export root and every valid child; failed exports and None keys never merge",
            "execution": {"units": "fresh REPL in the task's module", "maxAbandonments": MAX_ABANDONMENTS,
                          "retry": "REPL timeout retried on next run; second abandonment final and excluded from pairs",
                          "wallClock": "checked before expansions and goal positions; completed without proof, retained in pairs; partial expansions marked interrupted"},
            "hypotheses": HYPOTHESES,
            "checks": CHECKS,
            "secondary": {"equalSteps": f"the same comparisons with a proof counted only within {STEP_BUDGET} "
                                        "candidate applications, the most the first-goal search can spend",
                          "identity": "firstText against first on the sample",
                          "coupledShare": "share of exported multi-goal expanded states with a coupled group, per arm",
                          "diagnostic": "constructed coupled and independent tasks, registered separately as "
                                        "goal-selection-diagnostic-v0.1"},
            "analyses": {"pairs": "completed paired tasks; both one-sided exact sign tails, at equal expansions and steps",
                         "contrasts": {"firstText:first": "identity, on the registered sample", "first:any": "goal choice",
                                       "any:anyMultiset": "goal order quotient", "first:anyMultiset": "goal choice and order quotient"},
                         "typedSupport": "fractions divide by observations with known typed keys or coupling",
                         "distinctTypedMultisets": "sum of distinct keys within each task search",
                         "coupling": "replay every free-choice-only proof and report the chosen position and typed "
                                     "groups; committed as coupling.json, from which H79 is decided"},
            "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
            "resultsAbsentAtRegistration": True, "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles"}


def validate_registration() -> list[dict[str, Any]]:
    prereg = read_json(PREREG)
    expected = dict(prereg["implementationSha256"])
    for amendment in sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1])):
        expected.update(read_json(amendment).get("implementationSha256AfterAmendment", {}))
    for name, path in IMPLEMENTATIONS.items():
        if expected[name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration or amendment")
    for path, digest in ((TASKS, prereg["tasksSha256"]),
                         (SOURCE / "tasks.json", prereg["tasks"]["sourceSha256"]),
                         (SOURCE / "results.jsonl", prereg["tasks"]["baselineResultsSha256"])):
        if sha256_file(path) != digest:
            raise SystemExit(f"registered input changed: {path}")
    tasks = read_json(TASKS)
    if tasks != read_json(SOURCE / "tasks.json"):
        raise SystemExit("task list differs from search-v0.3")
    if prereg["baselineSample"]["tasks"] != [list(task_key(t)) for t in baseline_sample(tasks, prereg["baselineSample"]["seed"])]:
        raise SystemExit("registered baseline sample differs from its selection rule")
    return tasks


def artifact_summary(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], arms: list[str]) -> dict[str, Any]:
    sample = baseline_sample(tasks, read_json(PREREG)["baselineSample"]["seed"])
    probes = read_json(COUPLING) if COUPLING.exists() else None
    check = replication(rows, sample)
    check["holds"] = check["compared"] == check["matched"] == SAMPLE_SIZE and check["sampleMatches"]
    return summarize(rows, tasks, arms, probes) | {"C1": check,
        "resultsSha256": sha256_file(RESULTS), "preregistrationSha256": sha256_file(PREREG),
        "couplingSha256": sha256_file(COUPLING) if COUPLING.exists() else None,
        "amendmentsSha256": {p.name: sha256_file(p) for p in sorted(EXPERIMENT.glob("amendment-*.json"))}}


def run_all(tasks: list[dict[str, Any]], arms: list[str], workers: int,
            sample: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    rows = read_rows(RESULTS) if RESULTS.exists() else []
    previous = {unit_key(r): r for r in latest_rows(rows)}
    done = {key for key, r in previous.items() if
            (not r.get("error") and not r.get("abandoned")) or r["abandonments"] >= MAX_ABANDONMENTS}
    sampled = {task_key(t) for t in (sample if sample is not None else baseline_sample(tasks))} \
        if "firstText" in arms else set()
    units = [(task, arm) for task in tasks for arm in arms if (*task_key(task), arm) not in done and
             (arm != "firstText" or task_key(task) in sampled)]

    def guarded(task: dict[str, Any], arm: str) -> dict[str, Any]:
        try:
            return run_unit(task, arm)
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "arm": arm, "search": "whole",
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300]}

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, task, arm) for task, arm in units]
        for future in concurrent.futures.as_completed(futures):
            row = future.result()
            row["abandonments"] = previous.get(unit_key(row), {}).get("abandonments", 0) + bool(row.get("abandoned"))
            rows.append(row)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")
            print_row(row)
    order = {(*task_key(task), arm): i for i, (task, arm) in
             enumerate((t, a) for t in tasks for a in ARMS)}
    return sorted(latest_rows(rows), key=lambda r: order[unit_key(r)])


def print_row(row: dict[str, Any]) -> None:
    result = row.get("result") or {}
    print(json.dumps({"task": row["declaration"], "arm": row["arm"], "constructed": row.get("constructed"),
                      "seconds": result.get("seconds", row.get("seconds")), "setupSeconds": row.get("setupSeconds"),
                      "expansions": len(result.get("expansions", [])), "steps": result_steps(result) if result else None,
                      "stepsAtProof": proof_steps(result) if result else None, "proof": result.get("proof"),
                      "exportFailures": result.get("exportFailures", 0), "stopped": result.get("stopped"), "error": row.get("error"),
                      "abandoned": row.get("abandoned")}, ensure_ascii=False), flush=True)


def outside_output(path: Path | None) -> Path:
    if path is None:
        raise SystemExit("this mode requires --output-dir outside the repository")
    path = path.resolve()
    if path == ROOT or ROOT in path.parents:
        raise SystemExit("development and smoke output must be outside the repository")
    path.mkdir(parents=True, exist_ok=True)
    return path


def self_test(output: Path) -> int:
    repl = selection.ClosingRepl(find_lake())
    checks = {}
    try:
        response = repl.command("example : True := by\n  sorry")
        made = response["sorries"][0]
        task = harness.Task("self_test_text", [], "example : True := by", made["goal"])
        result = search(repl, "firstText", made["proofState"], [made["goal"]],
                        lambda script: harness.verify_script(repl, task, script), budget=4)
        checks["firstText"] = result["proof"] is not None
        repl.env = selection.define_exporter(repl, repl.env)
        checks["fastExporterDefined"] = bool(getattr(repl, "typed_fast_export", False))
        response = repl.command("example : 2 + 2 = 4 ∧ 3 * 3 = 9 := by\n  sorry")
        _, proof_state = repl.tactic(int(response["sorries"][0]["proofState"]), "refine ⟨?_, ?_⟩")
        named = selection.export(repl, proof_state)
        plain = gi.export(repl, proof_state)
        checks["namedEqualsPlain"] = named is not None and named == plain
        checks["independentGroups"] = named is not None and gi.groups(named) == [[0], [1]]
        for arm in ARMS[1:]:
            header = "example : 2 + 2 = 4 ∧ 3 * 3 = 9 := by"
            made = repl.command(header + "\n  sorry")["sorries"][0]
            goals, state = repl.tactic(int(made["proofState"]), "refine ⟨?_, ?_⟩")
            task = harness.Task("self_test", [], header, made["goal"])
            verifier = lambda script: harness.verify_script(repl, task, ["refine ⟨?_, ?_⟩"] + script)
            result = search(repl, arm, state, goals, verifier, budget=4)
            checks[arm] = result["proof"] is not None and verifier(result["proof"])
        response = repl.command("example : True ∧ (2 + 2 = 4) := by\n  sorry")
        goals, state = repl.tactic(response["sorries"][0]["proofState"], "refine ⟨?_, ?_⟩")
        probe = selection.coupling_probe(repl, state, ["pick_goal 2", "norm_num", "trivial"])
        checks["pickReplay"] = probe["closed"] and probe["steps"][0]["position"] == 2
    finally:
        repl.close()
    write_json(output / "self-test.json", checks)
    print(json.dumps({"self-test": checks, "ok": all(checks.values())}), flush=True)
    return 0 if all(checks.values()) else 1


def development_names(count: int) -> list[str]:
    corpus = {t["declaration"] for t in read_json(SOURCE / "tasks.json")}
    corpus.update(r["declaration"] for r in read_rows(ROOT / "experiments" / "linearizations-mathlib-v0.1" / "results.jsonl"))
    return [name for name in DEVELOPMENT if name not in corpus][:count]


def develop(output: Path, count: int) -> int:
    names = development_names(count)
    tasks = [{"declaration": name} for name in names] + CONTROLS
    rows = []
    for task in tasks:
        for arm in ARMS:
            row = run_development_unit(task, arm)
            rows.append(row)
            print_row(row)
            write_lf(output / "dev-results.jsonl", "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    completed = all("result" in row for row in rows)
    controls = {t["declaration"]: {r["arm"]: bool(r.get("result", {}).get("proof"))
                                  for r in rows if r["declaration"] == t["declaration"]} for t in CONTROLS}
    write_json(output / "dev-summary.json", {"developmentTheorems": names, "controls": controls,
                                            "completed": completed})
    print(json.dumps({"dev": {"developmentTheorems": names, "controls": controls, "completed": completed}}), flush=True)
    return 0 if completed else 1


def holdout_tasks() -> list[dict[str, Any]]:
    source = ROOT / "experiments" / "holdout-v0.1"
    selected = {task_key(r) for r in read_rows(source / "searches.jsonl") if r["search"] == "whole" and
                any(e["goals"] >= 3 for e in r.get("result", {}).get("expansions", []))}
    return sorted((t for t in read_json(source / "tasks.json") if task_key(t) in selected), key=task_key)


def develop_holdout(output: Path, count: int) -> int:
    tasks = holdout_tasks()
    if not 1 <= count <= len(tasks):
        raise SystemExit(f"dev-holdout must be between 1 and {len(tasks)}")
    rows = []
    for task in tasks[:count]:
        for arm in ARMS:
            row = run_unit(task, arm)
            rows.append(row)
            print_row(row)
            write_lf(output / "holdout-results.jsonl", "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    completed = all("result" in row for row in rows)
    write_json(output / "holdout-summary.json", {"eligibleTasks": len(tasks), "tasks": count,
                                                "units": len(rows), "completed": completed})
    print(json.dumps({"dev-holdout": {"eligibleTasks": len(tasks), "tasks": count,
                                      "units": len(rows), "completed": completed}}), flush=True)
    return 0 if completed else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ("self-test", "dev", "register", "run", "check-committed", "coupling"):
        mode.add_argument("--" + name, action="store_true")
    mode.add_argument("--smoke-first", type=int, metavar="N")
    mode.add_argument("--dev-holdout", type=int, metavar="N")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--arms", nargs="+", default=list(ARMS), help="space- or comma-separated arms")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--dev-count", type=int, default=4)
    args = parser.parse_args()
    arms = [a for value in args.arms for a in value.split(",") if a]
    if not arms or len(set(arms)) != len(arms) or any(a not in ARMS for a in arms):
        parser.error("arms must be distinct members of firstText, first, any, anyMultiset")
    if args.workers < 1 or not 0 <= args.dev_count <= 10:
        parser.error("workers must be positive and dev-count must be between 0 and 10")
    if (args.self_test or args.dev or args.smoke_first is not None or args.dev_holdout is not None or args.coupling) and args.workers != 1:
        parser.error("smoke, development, and coupling modes require --workers 1")
    if args.self_test:
        return self_test(outside_output(args.output_dir))
    if args.dev:
        return develop(outside_output(args.output_dir), args.dev_count)
    if args.dev_holdout is not None:
        return develop_holdout(outside_output(args.output_dir), args.dev_holdout)
    if args.smoke_first is not None:
        if not 1 <= args.smoke_first <= 5:
            parser.error("smoke-first must be between 1 and 5")
        output = outside_output(args.output_dir)
        committed = {task_key(r): r for r in read_rows(SOURCE / "results.jsonl")
                     if r["arm"] == "menu" and r["search"] == "whole" and "result" in r}
        tasks = [t for t in read_json(SOURCE / "tasks.json") if task_key(t) in committed][:args.smoke_first]
        rows = []
        for task in tasks:
            row = run_unit(task, "firstText")
            rows.append(row)
            print_row(row)
            write_lf(output / "first-results.jsonl", "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
        check = replication(rows)
        write_json(output / "first-replication.json", check)
        print(json.dumps({"first-replication": check}), flush=True)
        return 0 if check["compared"] == check["matched"] == args.smoke_first else 1
    if args.register:
        if PREREG.exists() or RESULTS.exists() or TASKS.exists():
            raise SystemExit("registration or experiment data already exist")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(TASKS, (SOURCE / "tasks.json").read_text(encoding="utf-8"))
        payload = registration_payload(read_json(TASKS)) | {"tasksSha256": sha256_file(TASKS)}
        write_json(PREREG, payload)
        print(f"registered {payload['tasks']['count']} tasks: {PREREG}")
        return 0
    tasks = validate_registration()
    if args.run:
        relative = PREREG.relative_to(ROOT).as_posix()
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
        published = subprocess.check_output(["git", "for-each-ref", f"--contains={commit}", "refs/remotes/"],
                                            cwd=ROOT, text=True).strip() if commit else ""
        clean = subprocess.check_output(["git", "status", "--porcelain", "--", relative], cwd=ROOT, text=True).strip()
        if not commit or not published or clean:
            raise SystemExit("commit and push registration before running (checked against local remote-tracking refs)")
        prereg = read_json(PREREG)
        rows = run_all(tasks, arms, args.workers, baseline_sample(tasks, prereg["baselineSample"]["seed"]))
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        present = [a for a in ARMS if any(r["arm"] == a for r in rows)]
        summary = artifact_summary(rows, tasks, present)
        write_json(SUMMARY, summary)
        write_lf(REPORT, report(summary))
        print(json.dumps({"goal-selection-run": summary["arms"], "C1": summary["C1"]}))
        return 0
    rows = read_rows(RESULTS)
    summary = read_json(SUMMARY)
    if args.coupling:
        by_task = {task_key(t): t for t in tasks}
        probes = []
        for proof in summary["freeChoiceOnlyProofs"]:
            row = run_unit(by_task[task_key(proof)], proof["arm"], probe=proof["proof"])
            probes.append(row)
            print(json.dumps(row, ensure_ascii=False), flush=True)
        write_json(COUPLING, probes)
        summary = artifact_summary(rows, tasks, list(summary["arms"]))
        write_json(SUMMARY, summary)
        write_lf(REPORT, report(summary))
        print(json.dumps({"H79": summary.get("hypotheses", {}).get("H79")}, ensure_ascii=False))
        return 0
    recomputed = artifact_summary(rows, tasks, list(summary["arms"]))
    if summary != recomputed or REPORT.read_text(encoding="utf-8") != report(recomputed):
        raise SystemExit("committed summary or report does not follow from results")
    print(f"goal-selection-check-ok: units={len(rows)} C1={summary['C1']['matched']}/{summary['C1']['compared']}"
          f" holds={summary['C1']['holds']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
