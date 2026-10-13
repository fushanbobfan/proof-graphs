#!/usr/bin/env python3
"""Search v0.12: the independent-goal search on search-v0.11's held-out tasks, with search-v0.11's candidates.

  python scripts/run_search_goals_holdout.py --register
  python scripts/run_search_goals_holdout.py --run [--workers 4]
  python scripts/run_search_goals_holdout.py --check-committed

search-v0.11 found the coupled-group search ahead of the whole-state search on 591 held-out tasks, and no proof that
decides the comparison passes through a group of several goals; whether coupling changes what the group search does
before a proof is found is open. This experiment runs the third search of search-v0.10, the independent-goal search
(`search_typed.and_or_search`, the typed key, 48 expansions), on those 591 tasks with search-v0.11's candidates: the
nth time it expands a goal it receives the nth candidate set search-v0.11 drew for that goal in the task, keyed by
the goal's printed text as in every shared-draw experiment, and fresh draws beyond the recorded sets. Its rows are
paired with search-v0.11's rows of the same tasks: groups against goals separates coupling from searching goals, and
goals against whole states repeats search-v0.10's comparison on held-out theorems. A search whose REPL session is
lost is abandoned (`search_typed_v2`), and a repeated unit reuses every candidate set drawn for it before.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import hashlib
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
import run_search_renaming as v7  # noqa: E402
import search_typed_v2 as guarded  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.12"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = dict(rc.IMPLEMENTATIONS) | {"confirmRunner": Path(rc.__file__).resolve(),
                                              "runner": Path(__file__).resolve()}
INPUTS = {"confirmTasks": rc.TASKS, "confirmResults": rc.RESULTS, "confirmDraws": rc.DRAWS,
          "confirmSummary": rc.SUMMARY, "confirmPreregistration": rc.PREREG}
SEARCH = "goals"
PAIRED = ("whole", "groups")  # search-v0.11's searches, whose rows this experiment's rows are paired with
BUDGET = 48
CHECKPOINTS = (24, 48)
ALPHA = 0.05
SHARE_MARGIN = 0.01  # H114: below one point, the group search's estimated gain over whole states in search-v0.11
SEED = 20261013
MAX_ATTEMPTS = 3
DEFAULT_WORKERS = 4
EXPORT_CEILING = 0.01

QUESTION = ("on search-v0.11's held-out tasks and with its candidates, does the coupled-group search prove more than "
            "the independent-goal search, and the independent-goal search more than the whole-state search, at 48 "
            "expansions")
HYPOTHESES = {
    "H112": "the coupled-group search (search-v0.11's rows) does not prove significantly more tasks than the "
            "independent-goal search within 48 expansions (one-sided sign test on the tasks exactly one of them "
            "proves, Holm's procedure at 0.05 over this test and H113's)",
    "H113": "the independent-goal search proves significantly more tasks than the whole-state search (search-v0.11's "
            "rows) within 48 expansions (one-sided sign test on the tasks exactly one of them proves, Holm's procedure "
            "at 0.05 over this test and H112's)",
    "H114": "the upper limit of the 95% interval (Newcombe's hybrid score interval for paired proportions) for the "
            "group search's proof rate minus the independent-goal search's is below 1 point, about the gain "
            "search-v0.11 estimated for the group search over the whole-state search",
}
CHECKS = {"C45": "every unit is final, and no latest row records an error",
          "C46": "the typed export fails on fewer than 1% of the states the search exports",
          "C47": "every candidate set the search takes as seeded is one search-v0.11 recorded, or an earlier attempt "
                 "of the unit drew, for that goal and occurrence in the task"}


# ---------------------------------------------------------------- tasks and candidates


def held_out_tasks() -> list[dict[str, Any]]:
    """search-v0.11's tasks stated in both its searches (its latest rows constructed), in its order."""
    rows = rc.read_rows()
    latest = {(r["declaration"], r["search"]): r for r in rows}
    tasks = json.loads(rc.TASKS.read_text(encoding="utf-8"))
    return [t for t in tasks if all((latest.get((t["declaration"], s)) or {}).get("constructed") for s in PAIRED)]


def group_sets(entries: list[dict[str, Any]], what: str) -> dict[int, dict[str, list[list[str]]]]:
    """Candidate sets per task index and goal key, in occurrence order; each goal's occurrences must be contiguous."""
    grouped: dict[int, dict[str, dict[int, list[str]]]] = {}
    for e in entries:
        grouped.setdefault(e["index"], {}).setdefault(v7.draw_key(e["prompt"]), {})[e["occurrence"]] = e["candidates"]
    out: dict[int, dict[str, list[list[str]]]] = {}
    for index, goals in grouped.items():
        for goal, by_occurrence in goals.items():
            assert sorted(by_occurrence) == list(range(len(by_occurrence))), f"{what}: gap in a goal's draws"
            out.setdefault(index, {})[goal] = [by_occurrence[n] for n in range(len(by_occurrence))]
    return out


def recorded_sets() -> dict[int, dict[str, list[list[str]]]]:
    return group_sets(rc.read_draws(), "search-v0.11")


def seeds_for(index: int, recorded: dict[int, dict[str, list[list[str]]]],
              drawn: list[dict[str, Any]]) -> dict[str, list[list[str]]]:
    """search-v0.11's sets for the task, then the sets this experiment drew for it in earlier attempts, which continue
    each goal's occurrences where search-v0.11's stop."""
    seeds = {goal: [list(c) for c in sets] for goal, sets in recorded.get(index, {}).items()}
    mine: dict[str, dict[int, list[str]]] = {}
    for e in drawn:
        if e["index"] == index:
            mine.setdefault(v7.draw_key(e["prompt"]), {})[e["occurrence"]] = e["candidates"]
    for goal, by_occurrence in mine.items():
        have = seeds.setdefault(goal, [])
        for n in sorted(by_occurrence):
            assert n == len(have), "an earlier attempt's draws do not continue the recorded ones"
            have.append(by_occurrence[n])
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
    """One task: the independent-goal search, its candidate stream seeded with the task's recorded sets."""
    draws = v8.ReplicateDraws(task["seeds"])
    unit = {k: v for k, v in task.items() if k != "seeds"}
    row = guarded.run_one(unit, SEARCH, draws.proposer(SEARCH), BUDGET)
    row |= {"index": task["index"], "attempt": task["attempt"],
            "draws": dict(draws.counts.get(SEARCH, {"seeded": 0, "shared": 0, "drawn": 0}))}
    log = [{"index": task["index"], "declaration": task["declaration"], "attempt": task["attempt"]} | e
           for e in draws.log]
    return [row], log


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
    """search-v0.11's attempt rule for one search: a unit that raised is repeated up to MAX_ATTEMPTS attempts; one
    whose search was abandoned or not constructed is repeated once; the latest row counts."""
    if not rows:
        return False
    latest = rows[-1]
    if latest.get("error"):
        return len(rows) >= MAX_ATTEMPTS
    if latest.get("abandoned") or latest.get("constructed") is False:
        return sum(1 for r in rows if not r.get("error")) >= 2
    return True


def done_tasks(rows: list[dict[str, Any]]) -> set[str]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for r in rows:
        grouped.setdefault(r["declaration"], []).append(r)
    return {d for d, rs in grouped.items() if unit_done(rs)}


def run_pass(tasks: list[dict[str, Any]], recorded: dict[int, dict[str, list[list[str]]]], workers: int) -> int:
    rows = read_rows()
    done = done_tasks(rows)
    attempts = {}
    for r in rows:
        attempts[r["declaration"]] = attempts.get(r["declaration"], 0) + 1
    draws_log = read_draws()  # every draw made so far, in every attempt: the bank a repeated unit reuses
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded_unit(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        attempt = attempts.get(task["declaration"], 0) + 1
        try:
            deep.admit()
            with lock:
                seeds = seeds_for(task["index"], recorded, draws_log)
            return unit_in_child(task | {"attempt": attempt, "seeds": seeds})
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": SEARCH,
                     "index": task["index"], "attempt": attempt, "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)}], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        unit_rows, unit_draws = result
        with lock:  # the draws first, so that a repeat after an interruption still finds them
            draws_log.extend(unit_draws)
            write_draws(draws_log, 6)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                for row in unit_rows:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            row = unit_rows[0]
            print(json.dumps({"task": row["declaration"][:40], "attempt": row["attempt"],
                              "expansions": len((row.get("result") or {}).get("expansions", [])),
                              "proved": bool((row.get("result") or {}).get("proof")), "draws": row.get("draws"),
                              "error": row.get("error"), "abandoned": row.get("abandoned"),
                              "at": time.strftime("%H:%M:%S")}, ensure_ascii=False), flush=True)

    todo = [t for t in tasks if t["declaration"] not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        pending = {pool.submit(guarded_unit, t) for t in todo}
        while pending:
            finished, pending = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                record(future.result())
    write_draws(sorted(draws_log, key=lambda e: (e["index"], e["attempt"], v7.draw_key(e["prompt"]), e["occurrence"])), 9)
    return len(todo)


def run_all(tasks: list[dict[str, Any]], workers: int) -> None:
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    recorded = recorded_sets()
    for _ in range(MAX_ATTEMPTS + 1):
        if run_pass(tasks, recorded, workers) == 0:
            return
    if len(done_tasks(read_rows())) < len(tasks):
        raise SystemExit("some units are not final after the passes allowed")


# ---------------------------------------------------------------- summary


def goal_hash(key: str) -> str:
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:16]


def pair(first: set[str], second: set[str], stated: list[str], by_module: dict[str, list[str]]) -> dict[str, Any]:
    a, b, c = len(first & second), len(first - second), len(second - first)
    d = len(stated) - a - b - c
    lower, upper = rc.newcombe(a, b, c, d)
    diff = {x: int(x in first) - int(x in second) for x in stated}
    return {"cells": {"both": a, "firstOnly": b, "secondOnly": c, "neither": d},
            "difference": (b - c) / len(stated), "newcombe95": [lower, upper],
            "moduleInterval95": deep.module_interval(by_module, lambda xs: sum(diff[x] for x in xs) / len(xs),
                                                     random.Random(SEED)),
            "signTestFirstMore": v8.sign_upper(b, b + c)}


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    latest = {r["declaration"]: r for r in rows}
    confirm = {(r["declaration"], r["search"]): r for r in rc.read_rows()}
    module_of = {t["declaration"]: t["module"] for t in tasks}
    stated = [t["declaration"] for t in tasks if (latest.get(t["declaration"]) or {}).get("constructed")]
    proved = {SEARCH: {c: {x for x in stated if deep.proved_within(latest.get(x), c)} for c in CHECKPOINTS}}
    for s in PAIRED:
        proved[s] = {c: {x for x in stated if deep.proved_within(confirm.get((x, s)), c)} for c in CHECKPOINTS}
    by_module: dict[str, list[str]] = {}
    for x in stated:
        by_module.setdefault(module_of[x], []).append(x)
    g, o, w = proved["groups"][BUDGET], proved[SEARCH][BUDGET], proved["whole"][BUDGET]
    pairs = {"groupsOverGoals": pair(g, o, stated, by_module), "goalsOverWhole": pair(o, w, stated, by_module),
             "groupsOverWhole": pair(g, w, stated, by_module)}
    tests = v8.holm({"groupsOverGoals": pairs["groupsOverGoals"]["signTestFirstMore"],
                     "goalsOverWhole": pairs["goalsOverWhole"]["signTestFirstMore"]}, ALPHA)
    ran = [u for u in latest.values() if u.get("result")]
    attempts = sum(u["result"].get("exportAttempts", 0) for u in ran)
    failures = sum(u["result"].get("exportFailures", 0) for u in ran)
    # C47: a seeded set is one search-v0.11 recorded, or one an earlier attempt of the unit drew, for that goal key
    # and occurrence.
    recorded = recorded_sets()
    by_index: dict[int, list[dict[str, Any]]] = {}
    for e in draws_log:
        by_index.setdefault(e["index"], []).append(e)
    seeded = faithful = 0
    for u in ran:
        prior = [e for e in by_index.get(u["index"], []) if e["attempt"] < u["attempt"]]
        known = {goal_hash(k): len(v) for k, v in seeds_for(u["index"], recorded, prior).items()}
        for e in u["result"].get("expansions", []):
            draw = e.get("draw") or {}
            if draw.get("source") == "seeded":
                seeded += 1
                faithful += draw.get("n", 0) < known.get(draw.get("goal"), 0)
    sources = {k: sum((u.get("draws") or {}).get(k, 0) for u in latest.values()) for k in ("seeded", "shared", "drawn")}
    done = len(done_tasks(rows)) == len(tasks)
    errors = sum(1 for u in latest.values() if u.get("error"))
    upper = pairs["groupsOverGoals"]["newcombe95"][1]
    out = {
        "experiment": "search-v0.12", "preregistrationSha256": sha256_file(PREREG), "tasks": len(tasks),
        "stated": len(stated),
        "proved": {s: {str(c): len(v) for c, v in proved[s].items()} for s in proved},
        "provedTasks": {s: {str(c): sorted(v) for c, v in proved[s].items()} for s in proved},
        "pairs": pairs, "holm": tests,
        "entangled": sum(u["result"].get("entangled", 0) for u in ran),
        "draws": {"sources": sources, "new": len(draws_log)},
        "errors": errors, "abandoned": sum(1 for u in latest.values() if u.get("abandoned")),
        "attempts": {"rows": len(rows), "repeatedUnits": len(rows) - len(latest)},
    }
    out["hypotheses"] = {
        "H112": {"p": tests["groupsOverGoals"]["p"], "adjusted": tests["groupsOverGoals"]["adjusted"],
                 "holds": not tests["groupsOverGoals"]["rejected"]},
        "H113": {"p": tests["goalsOverWhole"]["p"], "adjusted": tests["goalsOverWhole"]["adjusted"],
                 "holds": bool(tests["goalsOverWhole"]["rejected"])},
        "H114": {"upper": upper, "holds": upper is not None and upper < SHARE_MARGIN},
    }
    out["checks"] = {"C45": {"final": done, "errors": errors, "holds": done and errors == 0},
                     "C46": {"attempts": attempts, "failures": failures,
                             "holds": attempts > 0 and failures < EXPORT_CEILING * attempts},
                     "C47": {"seeded": seeded, "recorded": faithful, "holds": seeded == faithful}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# The independent-goal search on search-v0.11's held-out tasks (search v0.12)", "",
             f"Tasks: {s['tasks']}; stated: {s['stated']}. Proved: {s['proved']}.", ""]
    for name, p in s["pairs"].items():
        lines.append(f"- {name}: cells {p['cells']}; difference {p['difference']}; Newcombe 95% {p['newcombe95']}; "
                     f"module interval {p['moduleInterval95']}; one-sided sign test {p['signTestFirstMore']}.")
    lines += ["", "## Hypotheses", ""]
    for key, e in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, e in s["checks"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.12", "question": QUESTION,
        "kind": "an ablation on search-v0.11's tasks and candidates, whose results were known at registration: the "
                "third search of search-v0.10, paired with search-v0.11's two",
        "tasks": {"rule": "search-v0.11's tasks whose latest rows are constructed in both its searches, in its order",
                  "count": len(tasks), "tasksSha256": sha256_file(TASKS)},
        "inputs": {name: sha256_file(path) for name, path in INPUTS.items()},
        "search": "search_typed.and_or_search, search-v0.10's independent-goal search: single goals merged by the "
                  "typed key, a candidate that changes another goal discarded as entangled; breadth-first, 48 "
                  "expansions, in a fresh REPL, run through search_typed_v2 so that a lost session abandons it",
        "candidates": "the nth time the search expands a goal it receives the nth candidate set drawn for that goal in "
                      "the task, keyed by the goal's printed text without its case tag and with metavariable numbers "
                      "erased (search_harness.canonical_goal): first the sets search-v0.11 recorded for the task, in "
                      "their order, then the sets this experiment drew for the task in earlier attempts, then fresh "
                      "draws, made as in search-v0.11 and logged",
        "proposer": f"BFS-Prover-V2-7B in Q8_0 as in search-v0.11, served on port {deep.PORT}: {v8.SAMPLES} completions "
                    f"at temperature {v8.TEMPERATURE}, at most {v8.MAX_TOKENS} tokens, the first goal followed by "
                    f"':::', duplicates dropped",
        "budget": {"expansions": BUDGET, "checkpoints": list(CHECKPOINTS), "tacticWallClockSeconds": 60},
        "execution": f"each task's unit in its own Python process; {DEFAULT_WORKERS} units at a time, each started only "
                     f"while at least {deep.START_GATE_GB:g} GB of commit charge is left and {deep.START_SPACING:g} s "
                     f"after the previous start; search-v0.11's attempt rule (a unit that raised is repeated up to "
                     f"{MAX_ATTEMPTS} attempts, one whose search was not constructed or was abandoned is repeated once, "
                     f"and the latest row counts), a repeat reusing every candidate set drawn for the unit before",
        "pairing": "over the tasks this search states, its latest row against search-v0.11's latest rows of the same "
                   "task: proved within 48 expansions by both, by one only, or by neither",
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": "H112 and H113 by one-sided sign tests on the tasks exactly one of the two searches proves, with "
                 "Holm's procedure at 0.05 over the two; H114 by the upper limit of Newcombe's 95% hybrid score "
                 "interval; percentile intervals resampling modules are reported beside them and do not decide",
        "limits": "search-v0.11's two searches ran on 2026-10-10 to 12 and this search runs later, on the same machine, "
                  "REPL, Mathlib and model; where it reaches a goal or an occurrence search-v0.11 did not draw, its "
                  "candidates are fresh samples, so the pairing matches candidates only where the searches meet",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on these tasks: scripts/test_search_goals_holdout.py tests the "
                                               "seeding, the attempt rule with its candidate bank, and the summary "
                                               "without Lean; the unit process was run once on one of search-v0.10's "
                                               "tasks (Polynomial.monomial_mem_lifts), seeded with the sets "
                                               "search-v0.10 recorded for its first goal only so that later "
                                               "expansions drew from the server: proved in 6 expansions, 1 seeded "
                                               "and 5 drawn sets, no export failure",
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
        tasks = held_out_tasks()
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
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
        print("search-v0.12: registered, no results yet")
        return 0
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(read_rows(), read_draws(), tasks))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    print(f"search-v0.12-check-ok: rows={len(read_rows())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
