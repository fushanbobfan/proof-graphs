#!/usr/bin/env python3
"""Goal-selection v0.1: the fixed menu on first goals or on every open goal.

Development and smoke outputs require --output-dir outside the repository.
Registration precedes the experiment; --run resumes its recorded units.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import itertools
import json
import math
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
ARMS = ("first", "any", "anyMultiset")
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
    return list({unit_key(row): row for row in rows}.values())


def search(repl: Any, arm: str, proof_state: int, goals: list[str], verifier: Any,
           budget: int = BUDGET) -> dict[str, Any]:
    if arm == "first":
        return selection.first_search(repl, proof_state, goals, harness.menu_proposer, budget, verifier)
    return selection.any_goal_search(repl, proof_state, goals, harness.menu_proposer, budget, verifier,
                                     identify="multiset" if arm == "anyMultiset" else "ordered")


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
        session_type = harness.ModuleSession if arm == "first" else selection.ExportingSession
        session = session_type(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            constructed = True
            verifier = lambda script: session.verify(made, script)
            if probe is not None:
                return head | {"constructed": True, "verified": verifier(probe),
                               "probe": selection.coupling_probe(repl, made.proof_state, probe)}
            result = search(repl, arm, made.proof_state, [made.goal], verifier, budget)
            return head | {"constructed": True, "result": result,
                           "fastExport": getattr(repl, "typed_fast_export", False),
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
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
        probe = selection.coupling_probe(repl, proof_state, result["proof"]) if result["proof"] else None
        root_export = selection.export(repl, proof_state)
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


def replication(rows: list[dict[str, Any]]) -> dict[str, Any]:
    old = {task_key(r): r for r in read_rows(SOURCE / "results.jsonl")
           if r["arm"] == "menu" and r["search"] == "whole"}
    compared = matched = 0
    mismatches = []
    for row in latest_rows(rows):
        if row["arm"] != "first" or task_key(row) not in old:
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
    return {"compared": compared, "matched": matched, "mismatches": mismatches}


def fraction(numerator: int, denominator: int) -> float | None:
    return numerator / denominator if denominator else None


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], arms: list[str]) -> dict[str, Any]:
    keys = {task_key(task) for task in tasks}
    rows = [r for r in latest_rows(rows) if task_key(r) in keys and r["arm"] in arms]
    by_unit = {unit_key(r): r for r in rows}
    out: dict[str, Any] = {"experiment": "goal-selection-v0.1", "tasks": len(tasks),
                           "budget": BUDGET, "stepBudget": STEP_BUDGET, "arms": {}, "pairs": {},
                           "freeChoiceOnlyProofs": []}
    for arm in arms:
        units = [r for r in rows if r["arm"] == arm]
        ran = [r for r in units if "result" in r]
        expansions = [e for r in ran for e in r["result"]["expansions"]]
        typed = [e for e in expansions if e.get("orderDuplicateTyped") is not None]
        multi = [e for e in expansions if e["goals"] > 1 and e.get("coupled") is not None]
        valid = sum(e["valid"] for e in expansions)
        exact = sum(e["exactDuplicates"] for e in expansions)
        multiset = sum(e["multisetDuplicates"] for e in expansions)
        order = sum(bool(e["orderDuplicate"]) for e in expansions)
        typed_order = sum(bool(e["orderDuplicateTyped"]) for e in typed)
        coupled = sum(bool(e["coupled"]) for e in multi)
        out["arms"][arm] = {
            "tasksPosed": sum(bool(r.get("constructed")) for r in units), "completed": len(ran),
            "missing": len(tasks) - len(units), "errors": sum(bool(r.get("error")) for r in units),
            "abandoned": sum(bool(r.get("abandoned")) for r in units),
            "proved": sum(bool(r["result"]["proof"]) for r in ran), "expansions": len(expansions),
            "steps": sum(r["result"]["steps"] for r in ran), "validChildren": valid,
            "orderDuplicates": order, "orderFraction": fraction(order, len(expansions)),
            "typedOrderDuplicates": typed_order, "typedOrderSupport": len(typed),
            "typedOrderFraction": fraction(typed_order, len(typed)),
            "exactDuplicates": exact, "exactFraction": fraction(exact, valid),
            "multisetDuplicates": multiset, "multisetFraction": fraction(multiset, valid),
            "distinctTypedMultisets": sum(r["result"]["distinctTypedMultisets"] for r in ran),
            "coupledMultiGoalStates": coupled, "exportedMultiGoalStates": len(multi),
            "coupledFraction": fraction(coupled, len(multi)),
            "exportFailures": sum(r["result"]["exportFailures"] for r in ran)}
    for a, b in itertools.combinations(arms, 2):
        paired = [key for key in sorted(keys)
                  if "result" in by_unit.get((*key, a), {}) and "result" in by_unit.get((*key, b), {})]
        comparison = {"pairedCompleted": len(paired)}
        for measure in ("equalExpansions", "equalSteps"):
            def proved(key: tuple[str, str], arm: str) -> bool:
                result = by_unit[(*key, arm)]["result"]
                return bool(result["proof"]) and (measure == "equalExpansions" or arm == "first" or
                                                  (result["stepsAtProof"] is not None and
                                                   result["stepsAtProof"] <= STEP_BUDGET))
            a_only = sum(proved(key, a) and not proved(key, b) for key in paired)
            b_only = sum(proved(key, b) and not proved(key, a) for key in paired)
            comparison[measure] = {"aOnly": a_only, "bOnly": b_only,
                                   "pAGreater": sign_test(a_only, b_only), "pBGreater": sign_test(b_only, a_only)}
        out["pairs"][f"{a}:{b}"] = comparison
    for row in rows:
        baseline = by_unit.get((*task_key(row), "first"), {}).get("result")
        if row["arm"] != "first" and row.get("result", {}).get("proof") and baseline is not None \
                and not baseline["proof"]:
            out["freeChoiceOnlyProofs"].append({"module": row["module"], "declaration": row["declaration"],
                                               "arm": row["arm"], "proof": row["result"]["proof"],
                                               "stepsAtProof": row["result"]["stepsAtProof"]})
    out["freeChoiceOnlyProofs"].sort(key=unit_key)
    return out


def report(summary: dict[str, Any]) -> str:
    lines = ["# Goal-selection search v0.1", "", f"Candidate tasks: {summary['tasks']}; budget: {BUDGET} expansions.",
             "", "| Arm | Posed | Completed | Proved | Expansions | Steps | Text order fraction | Typed order fraction |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for arm, entry in summary["arms"].items():
        lines.append(f"| {arm} | {entry['tasksPosed']} | {entry['completed']} | {entry['proved']} | "
                     f"{entry['expansions']} | {entry['steps']} | {entry['orderFraction']} | {entry['typedOrderFraction']} |")
    lines += ["", "Typed fractions use exported support; unknown keys do not count as nonduplicates.",
              "Distinct typed multisets are summed within searches, whose task environments differ.",
              "Pairwise comparisons use tasks with completed results in both arms.",
              "At equal steps a free-choice proof must close within 624 candidate applications.",
              "", "## Measures and paired comparisons", "", "```json",
              json.dumps({"arms": summary["arms"], "pairs": summary["pairs"], "C1": summary.get("C1")}, indent=1),
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
            "arms": {"first": "search_harness.whole_state_search, unchanged, with passive measurements",
                     "any": "whole-state breadth-first; positions in order, then menu order; ordered text identity",
                     "anyMultiset": "the same search, deduplicated by joint typed unordered state key"},
            "proposer": list(harness.MENU), "budget": {"expansions": BUDGET, "secondarySteps": STEP_BUDGET},
            "identity": "goal_identity_typed; failed exports and None unordered keys never merge",
            "execution": "each unit in a fresh REPL in its module; resumable; failed units retried",
            "hypotheses": {"primary": "TO BE WRITTEN", "coupling": "TO BE WRITTEN"},
            "checks": {"C1": "every first unit reproduces search-v0.3 menu/whole: posing, proof found, and all expansion records"},
            "analyses": {"pairs": "completed paired tasks; both one-sided exact sign tails, at equal expansions and steps",
                         "typedSupport": "fractions divide by observations with known typed keys or coupling",
                         "distinctTypedMultisets": "sum of distinct keys within each task search",
                         "coupling": "replay every free-choice-only proof and report the chosen position and typed groups"},
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
    return tasks


def artifact_summary(rows: list[dict[str, Any]], tasks: list[dict[str, Any]], arms: list[str]) -> dict[str, Any]:
    return summarize(rows, tasks, arms) | {"C1": replication(rows),
        "resultsSha256": sha256_file(RESULTS), "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in sorted(EXPERIMENT.glob("amendment-*.json"))}}


def run_all(tasks: list[dict[str, Any]], arms: list[str], workers: int) -> list[dict[str, Any]]:
    rows = read_rows(RESULTS) if RESULTS.exists() else []
    done = {unit_key(r) for r in latest_rows(rows) if not r.get("error") and not r.get("abandoned")}
    units = [(task, arm) for task in tasks for arm in arms if (*task_key(task), arm) not in done]

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
                      "expansions": len(result.get("expansions", [])), "steps": result.get("steps"),
                      "stepsAtProof": result.get("stepsAtProof"), "proof": result.get("proof"),
                      "exportFailures": result.get("exportFailures"), "error": row.get("error"),
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
        repl.env = selection.define_exporter(repl, repl.env)
        checks["fastExporterDefined"] = bool(getattr(repl, "typed_fast_export", False))
        response = repl.command("example : 2 + 2 = 4 ∧ 3 * 3 = 9 := by\n  sorry")
        _, proof_state = repl.tactic(int(response["sorries"][0]["proofState"]), "refine ⟨?_, ?_⟩")
        named = selection.export(repl, proof_state)
        plain = gi.export(repl, proof_state)
        checks["namedEqualsPlain"] = named is not None and named == plain
        checks["independentGroups"] = named is not None and gi.groups(named) == [[0], [1]]
        for arm in ARMS:
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


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ("self-test", "dev", "register", "run", "check-committed", "coupling"):
        mode.add_argument("--" + name, action="store_true")
    mode.add_argument("--smoke-first", type=int, metavar="N")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--arms", nargs="+", default=list(ARMS), help="space- or comma-separated arms")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--dev-count", type=int, default=4)
    args = parser.parse_args()
    arms = [a for value in args.arms for a in value.split(",") if a]
    if not arms or len(set(arms)) != len(arms) or any(a not in ARMS for a in arms):
        parser.error("arms must be distinct members of first, any, anyMultiset")
    if args.workers < 1 or not 0 <= args.dev_count <= 10:
        parser.error("workers must be positive and dev-count must be between 0 and 10")
    if (args.self_test or args.dev or args.smoke_first is not None or args.coupling) and args.workers != 1:
        parser.error("smoke, development, and coupling modes require --workers 1")
    if args.self_test:
        return self_test(outside_output(args.output_dir))
    if args.dev:
        return develop(outside_output(args.output_dir), args.dev_count)
    if args.smoke_first is not None:
        if not 1 <= args.smoke_first <= 5:
            parser.error("smoke-first must be between 1 and 5")
        output = outside_output(args.output_dir)
        committed = {task_key(r): r for r in read_rows(SOURCE / "results.jsonl")
                     if r["arm"] == "menu" and r["search"] == "whole" and "result" in r}
        tasks = [t for t in read_json(SOURCE / "tasks.json") if task_key(t) in committed][:args.smoke_first]
        rows = []
        for task in tasks:
            row = run_unit(task, "first")
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
        rows = run_all(tasks, arms, args.workers)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        present = [a for a in ARMS if any(r["arm"] == a for r in rows)]
        summary = artifact_summary(rows, tasks, present)
        write_json(SUMMARY, summary)
        write_lf(REPORT, report(summary))
        print(json.dumps({"goal-selection-run": summary["arms"], "C1": summary["C1"]}))
        return 0
    rows = read_rows(RESULTS)
    summary = read_json(SUMMARY)
    recomputed = artifact_summary(rows, tasks, list(summary["arms"]))
    if summary != recomputed or REPORT.read_text(encoding="utf-8") != report(recomputed):
        raise SystemExit("committed summary or report does not follow from results")
    if summary["C1"]["mismatches"]:
        raise SystemExit("first arm differs from search-v0.3")
    if args.coupling:
        output = outside_output(args.output_dir)
        by_task = {task_key(t): t for t in tasks}
        probes = []
        for proof in summary["freeChoiceOnlyProofs"]:
            row = run_unit(by_task[task_key(proof)], proof["arm"], probe=proof["proof"])
            probes.append(row)
            write_json(output / "coupling.json", probes)
            print(json.dumps(row, ensure_ascii=False), flush=True)
        if not probes:
            write_json(output / "coupling.json", [])
        return 0 if all(r.get("verified") and r.get("probe", {}).get("closed") for r in probes) else 1
    print(f"goal-selection-check-ok: units={len(rows)} first={summary['C1']['matched']}/{summary['C1']['compared']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
