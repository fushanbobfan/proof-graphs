#!/usr/bin/env python3
"""Search v0.13: two fresh sets of draws for the three searches on search-v0.11's held-out tasks.

  python scripts/run_search_replicates_holdout.py --register
  python scripts/run_search_replicates_holdout.py --run [--workers 4]
  python scripts/run_search_replicates_holdout.py --check-committed

search-v0.11's registered test found the coupled-group search ahead of the whole-state search on 591 held-out
tasks, seven tasks to one, in one set of draws, and its significance turns on a task decided in a repeat. This
experiment draws two new sets for the same tasks and runs search-v0.10's three searches in each (whole states,
independent goals, coupled groups; the typed key, 48 expansions), the three searches of a task and set sharing one
candidate stream, so that the comparison is of theorem-level scores over sets, as in search-v0.8 and v0.10, and the
coupling ablation of search-v0.12 is repeated with fully matched candidates. A search whose REPL session is lost is
abandoned (`search_typed_v2`); a repeated unit reuses every candidate set drawn for it before.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import os
import random
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_confirm as rc  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_goals_holdout as v12  # noqa: E402
import run_search_renaming as v7  # noqa: E402
import run_search_typed as rt  # noqa: E402
import search_typed_v2 as guarded  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.13"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = dict(rc.IMPLEMENTATIONS) | {"confirmRunner": Path(rc.__file__).resolve(),
                                              "goalsRunner": Path(v12.__file__).resolve(),
                                              "runner": Path(__file__).resolve()}
INPUTS = {"confirmTasks": rc.TASKS, "confirmResults": rc.RESULTS, "pilotResults": rt.RESULTS}
SEARCHES = ("whole", "goals", "groups")
ORDERS = (("whole", "goals", "groups"), ("goals", "groups", "whole"), ("groups", "whole", "goals"))
REPLICATES = (1, 2)  # search-v0.11's draws are set 0
BUDGET = 48
CHECKPOINTS = (24, 48)
MARGIN = 0.03
ALPHA = 0.05
SEED = 20261014
SIMULATION_RUNS = 4000
MAX_ATTEMPTS = 3
DEFAULT_WORKERS = 4
EXPORT_CEILING = 0.01

QUESTION = ("on search-v0.11's held-out tasks and two new sets of draws, does the coupled-group search score higher "
            "than the whole-state search, by less than three points, and how do the two compare with the "
            "independent-goal search on the same candidates")
HYPOTHESES = {
    "H115": "over the two new sets, the group search's score (the sets in which it proves the task within 48 "
            "expansions) exceeds the whole-state search's on significantly more tasks than the reverse (one-sided "
            "sign test at 0.05 on the tasks whose scores differ)",
    "H116": f"the upper limit of the 95% interval, resampling modules, for the group search's proof rate minus the "
            f"whole-state search's over the two new sets is below {100 * MARGIN:.0f} points",
    "H117": "the group search's score does not exceed the independent-goal search's on significantly more tasks than "
            "the reverse (one-sided sign test on the tasks whose scores differ, Holm's procedure at 0.05 over this "
            "test and H118's)",
    "H118": "the independent-goal search's score exceeds the whole-state search's on significantly more tasks than "
            "the reverse (one-sided sign test on the tasks whose scores differ, Holm's procedure at 0.05 over this "
            "test and H117's)",
}
CHECKS = {"C48": "every unit is final, and no latest row records an error",
          "C49": "the typed export fails on fewer than 1% of the states the searches export",
          "C50": "no candidate set is drawn twice for the same goal and occurrence in a unit, and every set a search "
                 "takes as seeded is one an earlier attempt of the unit drew"}
COMPARISONS = {"groupsOverWhole": ("groups", "whole"), "groupsOverGoals": ("groups", "goals"),
               "goalsOverWhole": ("goals", "whole")}


# ---------------------------------------------------------------- tasks, units and candidates


def unit_key(task: dict[str, Any], replicate: int) -> str:
    return f"{replicate}:{task['declaration']}"


def seeds_for(index: int, replicate: int, drawn: list[dict[str, Any]]) -> dict[str, list[list[str]]]:
    """Every candidate set an earlier attempt of the unit drew, by goal key in occurrence order."""
    mine: dict[str, dict[int, list[str]]] = {}
    for e in drawn:
        if e["index"] == index and e["replicate"] == replicate:
            mine.setdefault(v7.draw_key(e["prompt"]), {})[e["occurrence"]] = e["candidates"]
    seeds = {}
    for goal, by_occurrence in mine.items():
        assert sorted(by_occurrence) == list(range(len(by_occurrence))), "a unit's draws of a goal have a gap"
        seeds[goal] = [by_occurrence[n] for n in range(len(by_occurrence))]
    return seeds


# ---------------------------------------------------------------- running


def read_rows() -> list[dict[str, Any]]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def read_draws() -> list[dict[str, Any]]:
    if not DRAWS.exists():
        return []
    return [json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def write_draws(entries: list[dict[str, Any]], level: int) -> None:
    temporary = DRAWS.with_name(DRAWS.name + ".tmp")
    temporary.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries)
                                        .encode("utf-8"), compresslevel=level, mtime=0))
    os.replace(temporary, DRAWS)


def run_unit(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """One task in one set: the three searches in a rotating order, sharing one candidate stream."""
    draws = v8.ReplicateDraws(task["seeds"])
    unit = {k: v for k, v in task.items() if k not in ("seeds", "replicate", "attempt")}
    rows = []
    for position, search in enumerate(ORDERS[(task["index"] + task["replicate"]) % len(ORDERS)]):
        row = guarded.run_one(unit, search, draws.proposer(search), BUDGET)
        rows.append(row | {"index": task["index"], "replicate": task["replicate"], "attempt": task["attempt"],
                           "position": position,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"index": task["index"], "declaration": task["declaration"], "replicate": task["replicate"],
            "attempt": task["attempt"]} | e for e in draws.log]
    return rows, log


def unit_in_child(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """run_unit in a fresh Python process, as search-v0.11 runs its units."""
    with tempfile.TemporaryDirectory() as tmp:
        given, taken = Path(tmp) / "task.json", Path(tmp) / "unit.json"
        given.write_text(json.dumps(task, ensure_ascii=False), encoding="utf-8")
        done = subprocess.run([sys.executable, "-B", str(Path(__file__).resolve()), "--unit", str(given), str(taken)],
                              cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
                              env=dict(os.environ, PYTHONUTF8="1", PYTHONIOENCODING="utf-8"),
                              creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        if done.returncode != 0 or not taken.exists():
            reason = (done.stderr.strip().splitlines() or [""])[-1]
            raise RuntimeError(f"unit process exited with {done.returncode}: {reason[:200]}")
        out = json.loads(taken.read_text(encoding="utf-8"))
    return out["rows"], out["log"]


def child_main(given: Path, taken: Path) -> int:
    prover.ENDPOINT = deep.ENDPOINT
    prover.MODEL_LOG = None
    rows, log = run_unit(json.loads(given.read_text(encoding="utf-8")))
    taken.write_text(json.dumps({"rows": rows, "log": log}, ensure_ascii=False), encoding="utf-8")
    return 0


def unit_done(rows: list[dict[str, Any]]) -> bool:
    """search-v0.11's attempt rule for a unit of three searches."""
    latest = {r["search"]: r for r in rows}
    if set(latest) != set(SEARCHES):
        return False
    attempts = max(sum(1 for r in rows if r["search"] == s) for s in SEARCHES)
    clean = sum(1 for r in rows if r["search"] == SEARCHES[0] and not r.get("error"))
    if any(r.get("error") for r in latest.values()):
        return attempts >= MAX_ATTEMPTS
    if any(r.get("abandoned") or r.get("constructed") is False for r in latest.values()):
        return clean >= 2
    return True


def by_unit(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for r in rows:
        grouped.setdefault(f"{r['replicate']}:{r['declaration']}", []).append(r)
    return grouped


def done_units(rows: list[dict[str, Any]]) -> set[str]:
    return {k for k, rs in by_unit(rows).items() if unit_done(rs)}


def run_pass(tasks: list[dict[str, Any]], workers: int) -> int:
    rows = read_rows()
    done = done_units(rows)
    attempts = {k: max(sum(1 for r in rs if r["search"] == s) for s in SEARCHES) for k, rs in by_unit(rows).items()}
    draws_log = read_draws()
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded_unit(task: dict[str, Any], replicate: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        attempt = attempts.get(unit_key(task, replicate), 0) + 1
        try:
            deep.admit()
            with lock:
                seeds = seeds_for(task["index"], replicate, draws_log)
            return unit_in_child(task | {"replicate": replicate, "attempt": attempt, "seeds": seeds})
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s, "index": task["index"],
                     "replicate": replicate, "attempt": attempt, "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)} for s in SEARCHES], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        unit_rows, unit_draws = result
        with lock:  # the draws first, so that a repeat after an interruption still finds them
            draws_log.extend(unit_draws)
            write_draws(draws_log, 6)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                for row in unit_rows:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            print(json.dumps({"task": unit_rows[0]["declaration"][:40], "set": unit_rows[0]["replicate"],
                              "attempt": unit_rows[0]["attempt"],
                              "searches": {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                                         bool((r.get("result") or {}).get("proof"))) for r in unit_rows},
                              "draws": len(unit_draws), "error": unit_rows[0].get("error"),
                              "at": time.strftime("%H:%M:%S")}, ensure_ascii=False), flush=True)

    # Set 1 for every task before set 2, so that an interrupted run leaves whole sets.
    todo = [(t, r) for r in REPLICATES for t in tasks if unit_key(t, r) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        pending = {pool.submit(guarded_unit, t, r) for t, r in todo}
        while pending:
            finished, pending = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                record(future.result())
    write_draws(sorted(draws_log, key=lambda e: (e["replicate"], e["index"], e["attempt"], v7.draw_key(e["prompt"]),
                                                 e["occurrence"])), 9)
    return len(todo)


def run_all(tasks: list[dict[str, Any]], workers: int) -> None:
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    for _ in range(MAX_ATTEMPTS + 1):
        if run_pass(tasks, workers) == 0:
            return
    if len(done_units(read_rows())) < len(tasks) * len(REPLICATES):
        raise SystemExit("some units are not final after the passes allowed")


# ---------------------------------------------------------------- power, from search-v0.10's patterns over sets


def pilot_patterns() -> list[tuple[tuple[bool, bool], ...]]:
    """Per task stated in all of search-v0.10's searches, per set: (group search proves, whole-state search proves)."""
    rows = (json.loads(l) for l in rt.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip())
    latest = {(r["replicate"], r["declaration"], r["search"]): r for r in rows}  # amendment rows come last
    tasks = sorted({d for (_, d, _) in latest
                    if all((latest.get((k, d, s)) or {}).get("constructed") for k in range(3) for s in SEARCHES)})
    return [tuple((deep.proved_within(latest[(k, d, "groups")], BUDGET), deep.proved_within(latest[(k, d, "whole")],
                                                                                         BUDGET)) for k in range(3))
            for d in tasks]


def simulate_power(n: int, patterns: list[tuple[tuple[bool, bool], ...]], rng: random.Random) -> dict[str, Any]:
    """Each simulated task takes the outcomes of a random search-v0.10 task in two of its three sets."""
    significant = 0
    differences = []
    for _ in range(SIMULATION_RUNS):
        more = fewer = total = 0
        for _ in range(n):
            pattern = rng.choice(patterns)
            sets = rng.sample(range(3), len(REPLICATES))
            d = sum(pattern[k][0] for k in sets) - sum(pattern[k][1] for k in sets)
            more += d > 0
            fewer += d < 0
            total += d
        p = v8.sign_upper(more, more + fewer)
        significant += p is not None and p < ALPHA
        differences.append(total / (n * len(REPLICATES)))
    differences.sort()
    return {"tasks": n, "signTestPower": round(significant / SIMULATION_RUNS, 3),
            "medianDifferencePoints": round(100 * differences[len(differences) // 2], 2)}


# ---------------------------------------------------------------- summary


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    latest = {(r["replicate"], r["declaration"], r["search"]): r for r in rows}
    module_of = {t["declaration"]: t["module"] for t in tasks}
    stated = [t["declaration"] for t in tasks
              if all((latest.get((k, t["declaration"], s)) or {}).get("constructed") for k in REPLICATES
                     for s in SEARCHES)]
    proved = {s: {k: {c: {x for x in stated if deep.proved_within(latest.get((k, x, s)), c)} for c in CHECKPOINTS}
                  for k in REPLICATES} for s in SEARCHES}
    scores = {s: {x: sum(x in proved[s][k][BUDGET] for k in REPLICATES) for x in stated} for s in SEARCHES}
    by_module: dict[str, list[str]] = {}
    for x in stated:
        by_module.setdefault(module_of[x], []).append(x)
    pairs = {}
    for name, (first, second) in COMPARISONS.items():
        d = {x: scores[first][x] - scores[second][x] for x in stated}
        more, fewer = sum(v > 0 for v in d.values()), sum(v < 0 for v in d.values())
        pairs[name] = {"tasksFirstMore": more, "tasksSecondMore": fewer,
                       "signTestFirstMore": v8.sign_upper(more, more + fewer),
                       "meanRateDifference": sum(d.values()) / (len(d) * len(REPLICATES)) if d else None,
                       "moduleInterval95": deep.module_interval(
                           by_module, lambda xs, d=d: sum(d[x] for x in xs) / (len(xs) * len(REPLICATES)),
                           random.Random(SEED)) if d else None,
                       "perSet": {str(k): {"firstOnly": len(proved[first][k][BUDGET] - proved[second][k][BUDGET]),
                                           "secondOnly": len(proved[second][k][BUDGET] - proved[first][k][BUDGET])}
                                  for k in REPLICATES}}
    tests = v8.holm({"groupsOverGoals": pairs["groupsOverGoals"]["signTestFirstMore"],
                     "goalsOverWhole": pairs["goalsOverWhole"]["signTestFirstMore"]}, ALPHA)
    ran = [u for u in latest.values() if u.get("result")]
    attempts = sum(u["result"].get("exportAttempts", 0) for u in ran)
    failures = sum(u["result"].get("exportFailures", 0) for u in ran)
    whole = [latest[(k, x, "whole")]["result"] for k in REPLICATES for x in stated
             if (latest.get((k, x, "whole")) or {}).get("result")]
    marks = [deep.flags(res, 0, BUDGET) for res in whole]
    grouped = [u["result"] for u in ran if u["search"] == "groups"]
    # C50: one set per goal and occurrence in a unit; a seeded set is one an earlier attempt of the unit drew.
    seen: set[tuple] = set()
    repeated_draws = 0
    for e in draws_log:
        key = (e["replicate"], e["index"], v7.draw_key(e["prompt"]), e["occurrence"])
        repeated_draws += key in seen
        seen.add(key)
    by_unit_draws: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for e in draws_log:
        by_unit_draws.setdefault((e["replicate"], e["index"]), []).append(e)
    seeded = faithful = 0
    for u in ran:
        prior = [e for e in by_unit_draws.get((u["replicate"], u["index"]), []) if e["attempt"] < u["attempt"]]
        known = {v12.goal_hash(k): len(v) for k, v in seeds_for(u["index"], u["replicate"], prior).items()}
        for e in u["result"].get("expansions", []):
            draw = e.get("draw") or {}
            if draw.get("source") == "seeded":
                seeded += 1
                faithful += draw.get("n", 0) < known.get(draw.get("goal"), 0)
    done = len(done_units(rows)) == len(tasks) * len(REPLICATES)
    errors = sum(1 for u in latest.values() if u.get("error"))
    upper = (pairs["groupsOverWhole"]["moduleInterval95"] or [None, None])[1]
    out = {
        "experiment": "search-v0.13", "preregistrationSha256": sha256_file(PREREG), "tasks": len(tasks),
        "stated": len(stated),
        "proved": {s: {str(k): {str(c): len(v) for c, v in proved[s][k].items()} for k in REPLICATES} for s in SEARCHES},
        "provedTasks": {s: {str(k): sorted(proved[s][k][BUDGET]) for k in REPLICATES} for s in SEARCHES},
        "pairs": pairs, "holm": tests,
        "duplicates": {"goalShare": deep.share(marks, 2) if marks else None,
                       "orderShare": deep.share(marks, 1) if marks else None},
        "groups": {"several": sum(r["groups"]["several"] for r in grouped),
                   "proofsThroughSeveral": sum(1 for r in grouped if r.get("proof") and r.get("groupsInProof"))},
        "entangled": sum(u["result"].get("entangled", 0) for u in ran if u["search"] == "goals"),
        "draws": {"new": len(draws_log)}, "errors": errors,
        "abandoned": sum(1 for u in latest.values() if u.get("abandoned")),
        "attempts": {"rows": len(rows), "repeatedUnits": sum(1 for rs in by_unit(rows).values()
                                                             if len(rs) > len(SEARCHES))},
    }
    out["hypotheses"] = {
        "H115": {"p": pairs["groupsOverWhole"]["signTestFirstMore"],
                 "holds": (pairs["groupsOverWhole"]["signTestFirstMore"] or 1.0) < ALPHA},
        "H116": {"upper": upper, "holds": upper is not None and upper < MARGIN},
        "H117": {"p": tests["groupsOverGoals"]["p"], "adjusted": tests["groupsOverGoals"]["adjusted"],
                 "holds": not tests["groupsOverGoals"]["rejected"]},
        "H118": {"p": tests["goalsOverWhole"]["p"], "adjusted": tests["goalsOverWhole"]["adjusted"],
                 "holds": bool(tests["goalsOverWhole"]["rejected"])},
    }
    out["checks"] = {"C48": {"final": done, "errors": errors, "holds": done and errors == 0},
                     "C49": {"attempts": attempts, "failures": failures,
                             "holds": attempts > 0 and failures < EXPORT_CEILING * attempts},
                     "C50": {"repeatedDraws": repeated_draws, "seeded": seeded, "fromEarlierAttempts": faithful,
                             "holds": repeated_draws == 0 and seeded == faithful}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# Two new sets of draws for the three searches on the held-out tasks (search v0.13)", "",
             f"Tasks: {s['tasks']}; stated in all six searches: {s['stated']}. Proved: {s['proved']}.", ""]
    for name, p in s["pairs"].items():
        lines.append(f"- {name}: tasks first more {p['tasksFirstMore']}, second more {p['tasksSecondMore']}; one-sided "
                     f"sign test {p['signTestFirstMore']}; mean difference {p['meanRateDifference']}; module interval "
                     f"{p['moduleInterval95']}.")
    lines += ["", "## Hypotheses", ""]
    for key, e in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, e in s["checks"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def registration_payload(tasks: list[dict[str, Any]], power: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.13", "question": QUESTION,
        "kind": "a replication on new draws of search-v0.11's held-out comparison, whose result was known at "
                "registration, with the independent-goal search added; search-v0.12 was running, and only its first "
                "four rows had been read, to check that its units completed",
        "tasks": {"rule": "search-v0.11's tasks whose latest rows are constructed in both its searches, in its order "
                          "(search-v0.12's tasks)", "count": len(tasks), "tasksSha256": sha256_file(TASKS)},
        "inputs": {name: sha256_file(path) for name, path in INPUTS.items()},
        "searches": "search-v0.10's three searches (search_typed: whole states, independent goals, coupled groups), "
                    "the typed key throughout, breadth-first, 48 expansions, each in a fresh REPL and run through "
                    "search_typed_v2 so that a lost session abandons it",
        "sets": "two new sets of draws, numbered 1 and 2 (search-v0.11's draws are set 0); in each, a task's three "
                "searches run one after another in an order that rotates with the task's index and the set, sharing "
                "one candidate stream: the nth time a search expands a goal it receives the nth candidate set drawn "
                "for that goal in the task and set, keyed by the goal's printed text without its case tag and with "
                "metavariable numbers erased; every set of the first set of draws is run before the second",
        "proposer": f"BFS-Prover-V2-7B in Q8_0 as in search-v0.11, served on port {deep.PORT}: {v8.SAMPLES} completions "
                    f"at temperature {v8.TEMPERATURE}, at most {v8.MAX_TOKENS} tokens, the first goal followed by "
                    f"':::', duplicates dropped",
        "budget": {"expansions": BUDGET, "checkpoints": list(CHECKPOINTS), "tacticWallClockSeconds": 60},
        "execution": f"each unit (a task in a set) in its own Python process; {DEFAULT_WORKERS} units at a time, each "
                     f"started only while at least {deep.START_GATE_GB:g} GB of commit charge is left and "
                     f"{deep.START_SPACING:g} s after the previous start; search-v0.11's attempt rule (a unit that "
                     f"raised is repeated up to {MAX_ATTEMPTS} attempts, one in which a search was not constructed or "
                     f"was abandoned is repeated once, and the latest row of each search counts), a repeat reusing "
                     f"every candidate set drawn for the unit before",
        "analysis": "over the tasks stated in all six searches, a search's score on a task is the number of the two new "
                    "sets in which it proves the task within 48 expansions; each comparison counts the tasks whose "
                    "scores differ, by direction, and gives the mean difference in proof rate with a 95% percentile "
                    f"interval resampling modules ({deep.BOOTSTRAP} resamples); search-v0.11's set and search-v0.12's "
                    "goal search are pooled with the new sets only descriptively",
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": "H115 by a one-sided sign test at 0.05; H116 by the upper limit of the interval resampling modules; "
                 "H117 and H118 by one-sided sign tests with Holm's procedure at 0.05 over the two",
        "power": power,
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on these tasks: scripts/test_search_replicates_holdout.py tests "
                                               "the units, the rotation, the attempt rule with its candidate bank, the "
                                               "power simulation and the summary without Lean; the unit process was "
                                               "run once on one of search-v0.10's tasks (NFA.nil_mem_acceptsFrom) in a "
                                               "new set, while search-v0.12 ran: each search proved it in 2 "
                                               "expansions, the first drawing 2 sets and the other two sharing them",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def main() -> int:
    if sys.argv[1:2] == ["--unit"]:
        return child_main(Path(sys.argv[2]), Path(sys.argv[3]))
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--register", "--run", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    parser.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    args = parser.parse_args()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        tasks = v12.held_out_tasks()
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        power = simulate_power(len(tasks), pilot_patterns(), random.Random(SEED))
        power |= {"pilot": "search-v0.10's per-task outcomes of the group and whole-state searches within 48 "
                           "expansions in its three sets; each simulated task takes a random pilot task's outcomes in "
                           "two random sets of its three", "runs": SIMULATION_RUNS, "informationOnly": True}
        write_lf(PREREG, json.dumps(registration_payload(tasks, power), indent=1, sort_keys=True, ensure_ascii=False)
                 + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        print(json.dumps(power, indent=1))
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("the tasks changed since registration")
    for name, path in IMPLEMENTATIONS.items():
        if name != "runner" and prereg["implementationSha256"][name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration")
    for name, path in INPUTS.items():
        if prereg["inputs"][name] != sha256_file(path):
            raise SystemExit(f"input {name} changed since registration")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))
    if args.run:
        run_all(tasks, args.workers)
        summary = summarize(read_rows(), read_draws(), tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))
        return 0
    if not RESULTS.exists():
        print("search-v0.13: registered, no results yet")
        return 0
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(read_rows(), read_draws(), tasks))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    print(f"search-v0.13-check-ok: rows={len(read_rows())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
