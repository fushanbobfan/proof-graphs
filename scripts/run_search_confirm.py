#!/usr/bin/env python3
"""Search v0.11: a confirmatory comparison of whole-state and coupled-group search on held-out theorems.

  python scripts/run_search_confirm.py --register
  python scripts/run_search_confirm.py --run [--workers 4]
  python scripts/run_search_confirm.py --check-committed

Every step-prover comparison so far ran on the same 200 tasks of the second Mathlib slice, of which 169 can be posed,
and none found a significant difference between searching whole states and searching goals or goal groups. This
experiment takes the next tasks of the same seeded order of that slice's candidates, which no experiment has used,
and compares the two searches of search-v0.10 (the typed key throughout) at 48 expansions, with fresh draws shared by
the two searches of a task. The registered decision is whether a gain of three points or more for the group search
is excluded. The number of tasks is fixed at registration by a stated rule: by simulation from search-v0.10's paired
outcomes at 48 expansions, the smallest of the candidate sizes for which the 95% interval's upper limit falls below
three points in at least 80% of simulated runs, or every remaining candidate if none does.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import math
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
import run_holdout as holdout  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_typed as rt  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import read_gz_lines, sha256_file, write_lf  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.11"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = dict(rt.IMPLEMENTATIONS) | {"typedRunner": rt.IMPLEMENTATIONS["runner"],
                                              "runner": Path(__file__).resolve()}
SEARCHES = ("whole", "groups")
BUDGET = 48
CHECKPOINTS = (24, 48)
FIRST = holdout.SEARCH_TASKS
SIZES = (480, 560, 640, 720)  # candidate numbers of tasks; every remaining candidate if none reaches TARGET
TARGET = 0.80
POSABLE = 169 / 200  # the share of search-v0.9's tasks stated in both of its searches under the same attempt rule
SIMULATION_RUNS = 4000
MARGIN = 0.03
DUPLICATE_CEILING = 0.10
ALPHA = 0.05
BOOTSTRAP = 2000
SEED = 20261010
MAX_ATTEMPTS = 3
DEFAULT_WORKERS = 4

QUESTION = ("on theorems no experiment has used, does a coupled-group search prove more than a whole-state search, "
            "both with the typed key and the step prover at 48 expansions, and is a gain of three points excluded")
HYPOTHESES = {
    "H109": "the group search does not prove significantly more tasks than the whole-state search (one-sided sign "
            "test on the tasks exactly one of them proves, p >= 0.05)",
    "H110": f"the upper limit of the 95% interval (Newcombe's hybrid score interval for paired proportions) for the "
            f"group search's proof rate minus the whole-state search's is below {100 * MARGIN:.0f} points",
    "H111": f"goal duplicates under the typed key are below {DUPLICATE_CEILING:.0%} of the whole-state search's "
            "expansions",
}
CHECKS = {"C43": "every unit is final, and no latest row records an error",
          "C44": "the typed export fails on fewer than 1% of the states the searches export"}


def remaining_candidates() -> list[dict[str, Any]]:
    """holdout-v0.1's seeded order of the slice's candidates, after the FIRST it drew."""
    records = read_gz_lines(holdout.EXTRACTION)
    rows = [json.loads(l) for l in (holdout.EXPERIMENT / "counts.jsonl").read_text(encoding="utf-8").splitlines()
            if l.strip()]
    candidates = holdout.candidates(records, rows)
    order = list(range(len(candidates)))
    random.Random(holdout.SEED).shuffle(order)
    first = [candidates[i] for i in order[:FIRST]]
    used = json.loads(holdout.TASKS.read_text(encoding="utf-8"))
    assert [(t["module"], t["declaration"]) for t in first] == [(t["module"], t["declaration"]) for t in used]
    return [candidates[i] | {"draw": FIRST + rank, "index": rank} for rank, i in enumerate(order[FIRST:])]


# ---------------------------------------------------------------- sample size, from search-v0.10


def pilot_cells() -> dict[str, int]:
    """search-v0.10's paired outcomes of the group and whole-state searches within 48 expansions, one pair per task
    stated in all its searches and set of draws: both prove, groups only, whole only, neither."""
    summary = json.loads(rt.SUMMARY.read_text(encoding="utf-8"))
    assert summary["checks"]["C40"]["holds"], "search-v0.10 must be complete before the sample size is fixed"
    proved = summary["provedTasks48"]
    cells = {"both": 0, "groupsOnly": 0, "wholeOnly": 0, "neither": 0}
    for r in range(rt.REPLICATES):
        g, w = set(proved["groups"][str(r)]), set(proved["whole"][str(r)])
        cells["both"] += len(g & w)
        cells["groupsOnly"] += len(g - w)
        cells["wholeOnly"] += len(w - g)
        cells["neither"] += summary["stated"] - len(g | w)
    return cells


def simulate(n: int, cells: dict[str, int], rng: random.Random) -> dict[str, Any]:
    """Paired outcomes for n tasks drawn from the pilot's cell probabilities, SIMULATION_RUNS times."""
    total = sum(cells.values())
    weights = [cells[k] / total for k in ("both", "groupsOnly", "wholeOnly", "neither")]
    below = within = significant = 0
    halves = []
    for _ in range(SIMULATION_RUNS):
        counts = [0, 0, 0, 0]
        for k in rng.choices(range(4), weights, k=n):
            counts[k] += 1
        a, b, c, d = counts
        lower, upper = newcombe(a, b, c, d)
        below += upper < MARGIN
        within += lower > -MARGIN and upper < MARGIN
        p = v8.sign_upper(b, b + c)
        significant += p is not None and p < ALPHA
        halves.append((upper - lower) / 2)
    halves.sort()
    return {"posable": n, "upperBelowMargin": round(below / SIMULATION_RUNS, 3),
            "withinMargin": round(within / SIMULATION_RUNS, 3), "signTestPower": round(significant / SIMULATION_RUNS, 3),
            "medianHalfWidthPoints": round(100 * halves[len(halves) // 2], 2)}


def sample_size(available: int) -> dict[str, Any]:
    """The registered rule: the smallest size in SIZES whose simulated chance that the upper limit falls below MARGIN
    is at least TARGET, under the pilot's cells; every remaining candidate if none reaches it."""
    cells = pilot_cells()
    rng = random.Random(SEED)
    sizes = [s for s in SIZES if s < available] + [available]
    table = {str(s): simulate(round(POSABLE * s), cells, rng) for s in sizes}
    chosen = next((s for s in sizes if table[str(s)]["upperBelowMargin"] >= TARGET), available)
    null_cells = dict(cells, groupsOnly=(cells["groupsOnly"] + cells["wholeOnly"]) / 2,
                      wholeOnly=(cells["groupsOnly"] + cells["wholeOnly"]) / 2)
    return {"pilot": "search-v0.10 within 48 expansions, the group and whole-state searches, one pair per task and set "
                     "of draws stated in all its searches", "pilotCells": cells,
            "rule": f"the smallest of {list(SIZES)} tasks, or all {available} remaining candidates, for which the "
                    f"upper limit of the 95% Newcombe interval is below {100 * MARGIN:.0f} points in at least "
                    f"{TARGET:.0%} of {SIMULATION_RUNS:,} simulated runs, drawing each task's paired outcome from the "
                    f"pilot's cell shares; posable tasks taken as {POSABLE:.3f} of those drawn (search-v0.9's share)",
            "simulation": table, "chosen": chosen,
            "noDifference": simulate(round(POSABLE * chosen), null_cells, rng)}


def draw_tasks(count: int) -> list[dict[str, Any]]:
    return remaining_candidates()[:count]


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
    draws = v8.ReplicateDraws({})
    rows = []
    order = SEARCHES if task["index"] % 2 == 0 else SEARCHES[::-1]
    for position, search in enumerate(order):
        row = rt.run_one(task, search, draws.proposer(search), BUDGET)
        rows.append(row | {"index": task["index"], "position": position,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"index": task["index"], "declaration": task["declaration"]} | e for e in draws.log]
    return rows, log


def unit_in_child(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """run_unit in a fresh Python process. search-v0.10's runner, which runs its units in its own threads, grew by
    about 0.85 GB a unit (13 to 28 GB in 41 minutes). Run one at a time in one process, the same searches leave
    nothing behind once their rows are dropped, and keeping their rows holds 0.14 GB for the first 256-expansion
    search and 0.02 GB for each further one; so most of the growth comes from what the runner adds (units side by
    side, heavier tasks, hundreds of kept units), which these measurements do not separate. A unit's own process
    returns all of its memory when it exits, whatever the cause. Scheduling only: the unit is the same."""
    with tempfile.TemporaryDirectory() as tmp:
        given, taken = Path(tmp) / "task.json", Path(tmp) / "unit.json"
        given.write_text(json.dumps(task, ensure_ascii=False), encoding="utf-8")
        done = subprocess.run([sys.executable, "-B", str(Path(__file__).resolve()), "--unit", str(given), str(taken)],
                              cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
                              env=dict(os.environ, PYTHONUTF8="1", PYTHONIOENCODING="utf-8"),
                              creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        if done.returncode != 0 or not taken.exists():
            reason = (done.stderr.strip().splitlines() or [""])[-1]  # the exception's own line
            raise RuntimeError(f"unit process exited with {done.returncode}: {reason[:200]}")
        out = json.loads(taken.read_text(encoding="utf-8"))
    return out["rows"], out["log"]


def child_main(given: Path, taken: Path) -> int:
    """The `--unit` entry: one unit, with the prover's endpoint as the runner sets it, written to `taken`."""
    prover.ENDPOINT = deep.ENDPOINT
    prover.MODEL_LOG = None
    rows, log = run_unit(json.loads(given.read_text(encoding="utf-8")))
    taken.write_text(json.dumps({"rows": rows, "log": log}, ensure_ascii=False), encoding="utf-8")
    return 0


def unit_done(rows: list[dict[str, Any]]) -> bool:
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


def done_tasks(rows: list[dict[str, Any]]) -> set[str]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for r in rows:
        grouped.setdefault(r["declaration"], []).append(r)
    return {d for d, rs in grouped.items() if unit_done(rs)}


def run_pass(tasks: list[dict[str, Any]], workers: int) -> int:
    done = done_tasks(read_rows())
    draws_log = [e for e in read_draws() if e["declaration"] in done]
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            deep.admit()
            return unit_in_child(task)
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s, "index": task["index"],
                     "constructed": None, "error": message, "seconds": round(time.monotonic() - started, 1)}
                    for s in SEARCHES], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        unit_rows, unit_draws = result
        with lock:
            draws_log.extend(unit_draws)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                for row in unit_rows:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            write_draws(draws_log, 6)
            print(json.dumps({"task": unit_rows[0]["declaration"][:40],
                              "searches": {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                                         bool((r.get("result") or {}).get("proof"))) for r in unit_rows},
                              "draws": len(unit_draws), "error": unit_rows[0].get("error"),
                              "at": time.strftime("%H:%M:%S")}, ensure_ascii=False), flush=True)

    todo = [t for t in tasks if t["declaration"] not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        pending = {pool.submit(guarded, t) for t in todo}
        while pending:  # a recorded unit's future is let go, so its rows do not stay in memory
            finished, pending = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                record(future.result())
    draws_log.sort(key=lambda e: e["index"])
    write_draws(draws_log, 9)
    return len(todo)


def run_all(tasks: list[dict[str, Any]], workers: int) -> None:
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    for _ in range(MAX_ATTEMPTS + 1):
        if run_pass(tasks, workers) == 0:
            return
    if len(done_tasks(read_rows())) < len(tasks):
        raise SystemExit("some units are not final after the passes allowed")


# ---------------------------------------------------------------- summary


def wilson(x: int, n: int, z: float = 1.959964) -> tuple[float, float]:
    p = x / n
    centre = (p + z * z / (2 * n)) / (1 + z * z / n)
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return centre - half, centre + half


def newcombe(a: int, b: int, c: int, d: int) -> tuple[float, float]:
    """Newcombe's hybrid score interval (method 10) for the paired difference (a + b - a - c) / n."""
    n = a + b + c + d
    p1, p2 = (a + b) / n, (a + c) / n
    l1, u1 = wilson(a + b, n)
    l2, u2 = wilson(a + c, n)
    denominator = (a + b) * (c + d) * (a + c) * (b + d)
    phi = (a * d - b * c) / math.sqrt(denominator) if denominator else 0.0
    delta = p1 - p2
    lower = delta - math.sqrt(max(0.0, (p1 - l1) ** 2 - 2 * phi * (p1 - l1) * (u2 - p2) + (u2 - p2) ** 2))
    upper = delta + math.sqrt(max(0.0, (u1 - p1) ** 2 - 2 * phi * (u1 - p1) * (p2 - l2) + (p2 - l2) ** 2))
    return lower, upper


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    latest = {(r["declaration"], r["search"]): r for r in rows}
    module_of = {t["declaration"]: t["module"] for t in tasks}
    stated = [t["declaration"] for t in tasks
              if all((latest.get((t["declaration"], s)) or {}).get("constructed") for s in SEARCHES)]
    proved = {s: {c: sorted(x for x in stated if deep.proved_within(latest.get((x, s)), c)) for c in CHECKPOINTS}
              for s in SEARCHES}
    g, w = set(proved["groups"][BUDGET]), set(proved["whole"][BUDGET])
    a, b, c = len(g & w), len(g - w), len(w - g)
    d = len(stated) - a - b - c
    lower, upper = newcombe(a, b, c, d) if stated else (None, None)
    p = v8.sign_upper(b, b + c)
    by_module: dict[str, list[str]] = {}
    for x in stated:
        by_module.setdefault(module_of[x], []).append(x)
    diff = {x: int(x in g) - int(x in w) for x in stated}
    interval = deep.module_interval(by_module, lambda xs: sum(diff[x] for x in xs) / len(xs),
                                    random.Random(SEED)) if stated else None
    whole = [latest[(x, "whole")]["result"] for x in stated if (latest.get((x, "whole")) or {}).get("result")]
    marks = [deep.flags(res, 0, BUDGET) for res in whole]
    goal_share = deep.share(marks, 2) if marks else None
    ran = [u for u in latest.values() if u.get("result")]
    attempts = sum(u["result"].get("exportAttempts", 0) for u in ran)
    failures = sum(u["result"].get("exportFailures", 0) for u in ran)
    done = len(done_tasks(rows)) == len(tasks)
    errors = sum(1 for u in latest.values() if u.get("error"))
    out = {
        "experiment": "search-v0.11", "preregistrationSha256": sha256_file(PREREG), "tasks": len(tasks),
        "stated": len(stated), "proved": {s: {str(k): len(v) for k, v in proved[s].items()} for s in SEARCHES},
        "provedTasks": proved, "cells": {"both": a, "groupsOnly": b, "wholeOnly": c, "neither": d},
        "difference": (b - c) / len(stated) if stated else None, "newcombe95": [lower, upper],
        "moduleInterval95": interval, "signTestGroupsMore": p,
        "duplicates": {"flagged": sum(m[0] for m in marks), "orderShare": deep.share(marks, 1) if marks else None,
                       "goalShare": goal_share},
        "draws": {"new": len(draws_log)}, "errors": errors,
        "abandoned": sum(1 for u in latest.values() if u.get("abandoned")),
    }
    out["hypotheses"] = {
        "H109": {"p": p, "holds": p is None or p >= ALPHA},  # no task proved by one search only: nothing significant
        "H110": {"upper": upper, "holds": upper is not None and upper < MARGIN},
        "H111": {"goalShare": goal_share, "holds": goal_share is not None and goal_share < DUPLICATE_CEILING},
    }
    out["checks"] = {"C43": {"final": done, "errors": errors, "holds": done and errors == 0},
                     "C44": {"attempts": attempts, "failures": failures,
                             "holds": attempts > 0 and failures < 0.01 * attempts}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# Whole states and coupled goal groups on held-out theorems (search v0.11)", "",
             f"Tasks: {s['tasks']}; stated in both searches: {s['stated']}.", "",
             f"Proved: {s['proved']}; cells {s['cells']}; difference {s['difference']}; Newcombe 95% {s['newcombe95']}; "
             f"module interval {s['moduleInterval95']}; one-sided sign test {s['signTestGroupsMore']}.", "",
             "## Hypotheses", ""]
    for key, e in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, e in s["checks"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


def registration_payload(tasks: list[dict[str, Any]], size: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.11", "question": QUESTION,
        "kind": "confirmatory: the tasks are held out from every earlier experiment, and the implementation is "
                "search-v0.10's, unchanged",
        "tasks": {"rule": f"holdout-v0.1's candidates (one `by` block of 3 to 20 steps under the corrected step "
                          f"counts, not generated) in its seeded order (random.Random({holdout.SEED})): positions "
                          f"{FIRST} to {FIRST + len(tasks) - 1}, after the {FIRST} it drew; no earlier experiment ran "
                          f"them", "count": len(tasks), "tasksSha256": sha256_file(TASKS),
                  "holdoutExtractionSha256": sha256_file(holdout.EXTRACTION)},
        "searches": "search_typed's whole-state and coupled-group searches, as in search-v0.10; breadth-first; each "
                    "task's two searches in fresh REPLs, in alternating order, sharing one set of fresh draws: the nth "
                    "time a search expands a goal it gets the nth set of candidates drawn for that goal in the task",
        "proposer": f"BFS-Prover-V2-7B in Q8_0 as in search-v0.10, served on port {deep.PORT}: {v8.SAMPLES} completions "
                    f"at temperature {v8.TEMPERATURE}, at most {v8.MAX_TOKENS} tokens, the first goal followed by "
                    f"':::', duplicates dropped",
        "budget": {"expansions": BUDGET, "checkpoints": list(CHECKPOINTS), "tacticWallClockSeconds": 60},
        "execution": f"each task's unit in its own Python process; {DEFAULT_WORKERS} units at a time, each started only "
                     f"while at least {deep.START_GATE_GB:g} GB of commit charge is left and {deep.START_SPACING:g} s "
                     f"after the previous start; units resumed by search-v0.10's attempt rule (a unit that raised is "
                     f"repeated up to {MAX_ATTEMPTS} attempts, one in which a search was not constructed or was "
                     f"abandoned is repeated once, and the latest row of each search counts)",
        "sampleSize": size,
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": "H109 by a one-sided sign test at 0.05; H110 by the upper limit of Newcombe's 95% hybrid score "
                 "interval for paired proportions over the tasks stated in both searches; a percentile interval "
                 "resampling modules is reported beside it and does not decide",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on these tasks: the implementation is search-v0.10's, run on its "
                                               "200 tasks before this registration",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def main() -> int:
    if sys.argv[1:2] == ["--unit"]:  # one unit in its own process (unit_in_child)
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
        pool = remaining_candidates()
        size = sample_size(len(pool))
        tasks = draw_tasks(size["chosen"])
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        write_lf(PREREG, json.dumps(registration_payload(tasks, size), indent=1, sort_keys=True, ensure_ascii=False)
                 + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        print(json.dumps(size, indent=1))
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("the tasks changed since registration")
    for name, path in IMPLEMENTATIONS.items():
        if name != "runner" and prereg["implementationSha256"][name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))
    if args.run:
        run_all(tasks, args.workers)
        summary = summarize(read_rows(), read_draws(), tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))
        return 0
    if not RESULTS.exists():
        print("search-v0.11: registered, no results yet")
        return 0
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(read_rows(), read_draws(), tasks))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    print(f"search-v0.11-check-ok: rows={len(read_rows())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
