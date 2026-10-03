#!/usr/bin/env python3
"""Search v0.9: search-v0.8's whole-state and coupled-group searches with 256 expansions instead of 48.

  python scripts/run_search_coupled_deep.py --prefix N
  python scripts/run_search_coupled_deep.py --develop N [--budget B] [--workers W]
  python scripts/run_search_coupled_deep.py --register
  python scripts/run_search_coupled_deep.py --run [--workers 3]
  python scripts/run_search_coupled_deep.py --check-committed

search-v0.8 compared a whole-state search, a search over independent goals, and a search over goals grouped by the
metavariables they share, each with 48 expansions, and no search proved significantly more than another. A review
of the paper asked for one stronger search point, so that the result is not confined to searches that small. This
experiment runs two of those searches, unchanged, with 256 expansions each, on the same 200 tasks and in
search-v0.8's first set of draws: the whole-state search, and the coupled-group search, which removes goal sharing
and, unlike the search over independent goals, keeps a candidate that assigns a metavariable goals share. (The two
goal searches proved the same theorems in search-v0.8 but one; leaving one out saves a third of the REPL time.) A
task's draws are seeded with every set that search-v0.6, search-v0.7, and search-v0.8's first set recorded for it,
and extended by new draws shared by its two searches as before.

The searches are breadth-first and the seeds cover their first 48 expansions, so those expansions repeat
search-v0.8's first set (check C28), and one run gives the measures at 48, 96, 192, and 256 expansions, as
search-v0.2 did for search-v0.1. The prover runs on its own port with the server's prompt cache in RAM switched off,
and three units run at a time, because other programs share the machine's memory. `--prefix` runs the first tasks with 48 expansions and compares them with
search-v0.8; `--develop` runs the searches with fresh draws on theorems outside the corpus and reports the draw
throughput and the memory of the REPL processes.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import ctypes
import gzip
import hashlib
import json
import os
import random
import sys
import threading
import time
import urllib.request
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_holdout as holdout  # noqa: E402
import run_key_replay as keys_replay  # noqa: E402
import run_search_coupled as v8  # noqa: E402
import run_search_paired as v6  # noqa: E402
import run_search_renaming as v7  # noqa: E402
import step_prover as prover  # noqa: E402
from run_linearizations import quantiles, sha256_file, write_lf  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.9"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {name: path for name, path in v8.IMPLEMENTATIONS.items() if name != "runner"} | {
    "searchV08Runner": v8.IMPLEMENTATIONS["runner"], "runner": Path(__file__).resolve()}
SEARCHES, WORDS = ("whole", "groups"), v8.WORDS
PREFIX = v8.BUDGET
assert PREFIX == 48, "search-v0.8 ran 48 expansions"
BUDGET = 256
CHECKPOINTS = (PREFIX, 2 * PREFIX, 4 * PREFIX, BUDGET)
COMPARISONS = {"H87": ("groups", "whole")}
ALPHA = 0.05
ORDER_LIMIT = 0.01
REPLICATION_SHARE = 0.98
COMPLETE_SHARE = 0.99
BOOTSTRAP = 2000
SEED = 20261003
MAX_ATTEMPTS = 3
# The prover is served on its own port, so that a model another program starts on the usual port 8080 can
# neither take this run's requests nor be taken for the prover.
PORT = 8091
ENDPOINT = f"http://127.0.0.1:{PORT}/v1/completions"


def server_alive() -> bool:
    """Whether the server on PORT answers and serves the prover's weights."""
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{PORT}/v1/models", timeout=5) as response:
            listing = json.loads(response.read().decode("utf-8"))
    except Exception:  # noqa: BLE001
        return False
    return any(Path(m.get("id", "")).name == Path(v8.MODEL_PATH).name for m in listing.get("data", []))


# ---------------------------------------------------------------- draws


def seeds() -> dict[int, dict[str, list[list[str]]]]:
    """Per task and goal, in occurrence order: the sets that seeded search-v0.8's first set (search-v0.6's and
    search-v0.7's recorded draws), then that set's new draws."""
    sets = keys_replay.recorded_draws()
    extra: dict[int, dict[str, dict[int, list[str]]]] = {}
    for entry in v8.read_draws():
        if entry["replicate"] == 0:
            extra.setdefault(entry["index"], {}).setdefault(v7.draw_key(entry["prompt"]), {})[entry["occurrence"]] = \
                entry["candidates"]
    for index, goals in extra.items():
        for goal, by_occurrence in goals.items():
            have = sets.setdefault(index, {}).setdefault(goal, [])
            for n in sorted(by_occurrence):
                assert n == len(have), "search-v0.8's first-set draws of a goal do not extend its seeds"
                have.append(by_occurrence[n])
    return sets


def seeds_digest(sets: dict[int, dict[str, list[list[str]]]]) -> str:
    text = json.dumps({str(i): sets[i] for i in sorted(sets)}, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":"))
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_draws() -> list[dict[str, Any]]:
    if not DRAWS.exists():
        return []
    return [json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def write_draws(entries: list[dict[str, Any]], level: int) -> None:
    """Written beside the log and moved over it, so that an interruption never leaves a truncated log."""
    temporary = DRAWS.with_name(DRAWS.name + ".tmp")
    temporary.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries)
                                        .encode("utf-8"), compresslevel=level, mtime=0))
    os.replace(temporary, DRAWS)


# ---------------------------------------------------------------- running


def units() -> list[dict[str, Any]]:
    return v6.execution_order(v6.tasks())


def run_unit(task: dict[str, Any], sets: dict[str, list[list[str]]],
             budget: int = BUDGET) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """search-v0.8's unit with its two searches: each in a fresh REPL, the whole-state search first on tasks of even
    index and the coupled-group search first on odd, sharing the task's draws."""
    draws = v8.ReplicateDraws(sets)
    rows = []
    order = SEARCHES if task["index"] % 2 == 0 else SEARCHES[::-1]
    for position, search in enumerate(order):
        row = v8.run_one(task, search, draws.proposer(search), budget)
        rows.append(row | {"replicate": 0, "index": task["index"], "position": position,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"replicate": 0, "index": task["index"], "declaration": task["declaration"]} | e for e in draws.log]
    return rows, log


START_GATE_GB = 15.0
START_SPACING = 45.0
_start_lock = threading.Lock()


def admit() -> None:
    """Holds a unit back until it may start: once the commit charge left exceeds a REPL's (about 7 GB) beyond the
    supervisor's 8 GB floor, and at least START_SPACING seconds after the previous start, by which time that REPL has
    reached the memory of its imports. Scheduling only; what a unit computes does not depend on it."""
    _start_lock.acquire()
    while (left := _commit_available_gb()) is not None and left < START_GATE_GB:
        time.sleep(30)
    threading.Timer(START_SPACING, _start_lock.release).start()


def gated_unit(task: dict[str, Any], sets: dict[str, list[list[str]]],
               budget: int = BUDGET) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    admit()
    return run_unit(task, sets, budget)


def read_rows() -> list[dict[str, Any]]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def unit_done(rows: list[dict[str, Any]]) -> bool:
    """Whether a task's attempts so far are final. Every attempt appends one row per search, and the latest rows
    count. An attempt that raised is repeated, up to MAX_ATTEMPTS attempts in all; an attempt in which a search
    was not constructed or was abandoned by a REPL timeout is repeated once."""
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


def run_pass(workers: int, sets: dict[int, dict[str, list[list[str]]]]) -> int:
    """One pass over the tasks not yet final; returns how many units it ran. The new draws of an attempt that is
    not final are dropped, so a repeated unit draws afresh beyond the seeds."""
    rows = read_rows()
    done = done_tasks(rows)
    draws_log = [e for e in read_draws() if e["declaration"] in done]
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            return gated_unit(task, sets.get(task["index"], {}))
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s, "replicate": 0,
                     "index": task["index"], "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)} for s in SEARCHES], []

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

    todo = [t for t in units() if t["declaration"] not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t) for t in todo]
        for future in concurrent.futures.as_completed(futures):
            record(future.result())
    draws_log.sort(key=lambda e: e["index"])
    write_draws(draws_log, 9)
    return len(todo)


def run_all(workers: int) -> None:
    sets = seeds()
    for _ in range(MAX_ATTEMPTS + 1):
        if run_pass(workers, sets) == 0:
            return
    if len(done_tasks(read_rows())) < len(units()):
        raise SystemExit("some units are not final after the passes allowed")


# ---------------------------------------------------------------- summary


def latest_rows(rows: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    return {(r["declaration"], r["search"]): r for r in rows}


def first_set_of_v8() -> dict[tuple[str, str], dict[str, Any]]:
    rows = [json.loads(l) for l in v8.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    return {(r["declaration"], r["search"]): r for r in rows if r.get("replicate") == 0}


def proved_within(unit: dict[str, Any] | None, limit: int) -> bool:
    result = (unit or {}).get("result") or {}
    return bool(result.get("proof")) and len(result.get("expansions", [])) <= limit


def plain(expansions: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Expansion records without the source of their draw, which differs by design: what search-v0.8 drew is
    seeded here."""
    out = []
    for e in expansions:
        e = dict(e)
        if isinstance(e.get("draw"), dict):
            e["draw"] = {k: v for k, v in e["draw"].items() if k != "source"}
        out.append(e)
    return out


def replicates(unit: dict[str, Any], old: dict[str, Any]) -> bool:
    """Whether a search's first 48 expansions, and its proof if it found one within them, are search-v0.8's."""
    new = unit["result"]
    proof = new["proof"] if len(new["expansions"]) <= PREFIX else None
    return plain(new["expansions"][:PREFIX]) == plain(old["result"]["expansions"]) and proof == old["result"]["proof"]


def module_interval(by_module: dict[str, list[str]], statistic: Callable[[list[str]], float],
                    rng: random.Random) -> list[float]:
    """95% percentile interval of a statistic over tasks, resampling modules."""
    modules = sorted(by_module)
    values = []
    for _ in range(BOOTSTRAP):
        chosen = [x for m in (rng.choice(modules) for _ in modules) for x in by_module[m]]
        values.append(statistic(chosen))
    values.sort()
    return [round(values[int(0.025 * BOOTSTRAP)], 6), round(values[int(0.975 * BOOTSTRAP) - 1], 6)]


def flags(result: dict[str, Any], lo: int, hi: int) -> tuple[int, int, int]:
    """Whole-state expansions lo..hi with an exported key: how many, order duplicates, goal duplicates."""
    marks = [(e["orderDuplicate"], e["goalDuplicate"]) for e in result["expansions"][lo:hi]
             if e.get("orderDuplicate") is not None]
    return len(marks), sum(1 for o, _ in marks if o), sum(1 for _, g in marks if g)


def share(values: list[tuple[int, int, int]], position: int) -> float:
    return sum(v[position] for v in values) / max(1, sum(v[0] for v in values))


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]]) -> dict[str, Any]:
    task_list = v6.tasks()
    module_of = {t["declaration"]: t["module"] for t in task_list}
    latest = latest_rows(rows)

    def unit(t: dict[str, Any], s: str) -> dict[str, Any] | None:
        return latest.get((t["declaration"], s))

    stated = [t for t in task_list if all((u := unit(t, s)) is not None and u.get("constructed") for s in SEARCHES)]
    names = [t["declaration"] for t in stated]

    def grouped(declarations: list[str]) -> dict[str, list[str]]:
        out: dict[str, list[str]] = {}
        for x in declarations:
            out.setdefault(module_of[x], []).append(x)
        return out

    proved = {s: {c: sorted(t["declaration"] for t in stated if proved_within(unit(t, s), c)) for c in CHECKPOINTS}
              for s in SEARCHES}
    rng = random.Random(SEED)
    pairs: dict[str, Any] = {}
    for name, (first, second) in COMPARISONS.items():
        a, b = set(proved[first][BUDGET]), set(proved[second][BUDGET])
        d = {x: int(x in a) - int(x in b) for x in names}
        higher, lower = len(a - b), len(b - a)
        pairs[name] = {"first": first, "second": second, "tasksFirstMore": higher, "tasksSecondMore": lower,
                       "signTestFirstMore": v8.sign_upper(higher, higher + lower),
                       "rateDifference": round(sum(d.values()) / len(d), 6) if d else None,
                       "interval95": module_interval(grouped(names), lambda xs: sum(d[x] for x in xs) / len(xs), rng)
                       if d else None,
                       "checkpoints": {c: {"firstOnly": len(set(proved[first][c]) - set(proved[second][c])),
                                           "secondOnly": len(set(proved[second][c]) - set(proved[first][c]))}
                                       for c in CHECKPOINTS}}
    tests = {name: {"p": pairs[name]["signTestFirstMore"],
                    "rejected": pairs[name]["signTestFirstMore"] is not None and pairs[name]["signTestFirstMore"] <= ALPHA}
             for name in COMPARISONS}

    whole = {t["declaration"]: unit(t, "whole")["result"] for t in stated if (unit(t, "whole") or {}).get("result")}
    past = sorted(x for x, r in whole.items() if len(r["expansions"]) > PREFIX)
    early = {x: flags(whole[x], 0, PREFIX) for x in past}
    late = {x: flags(whole[x], PREFIX, BUDGET) for x in past}

    def growth(xs: list[str]) -> float:
        return share([late[x] for x in xs], 2) - share([early[x] for x in xs], 2)

    goal_sharing = {"searches": len(past), "earlyFlagged": sum(v[0] for v in early.values()),
                    "lateFlagged": sum(v[0] for v in late.values()),
                    "earlyShare": round(share(list(early.values()), 2), 6),
                    "lateShare": round(share(list(late.values()), 2), 6),
                    "difference": round(growth(past), 6) if past else None,
                    "interval95": module_interval(grouped(past), growth, rng) if past else None}
    goal_sharing["holds"] = bool(past) and goal_sharing["interval95"][0] > 0
    totals = {x: flags(r, 0, BUDGET) for x, r in whole.items()}

    def order_share(xs: list[str]) -> float:
        return share([totals[x] for x in xs], 1)

    order = {"searches": len(totals), "flagged": sum(v[0] for v in totals.values()),
             "orderDuplicates": sum(v[1] for v in totals.values()),
             "share": round(order_share(sorted(totals)), 6) if totals else None,
             "interval95": module_interval(grouped(sorted(totals)), order_share, rng) if totals else None,
             "limit": ORDER_LIMIT}
    order["holds"] = bool(totals) and order["interval95"][1] < ORDER_LIMIT
    by_checkpoint = {c: {"flagged": sum(flags(r, 0, c)[0] for r in whole.values()),
                         "orderShare": round(share([flags(r, 0, c) for r in whole.values()], 1), 6),
                         "goalShare": round(share([flags(r, 0, c) for r in whole.values()], 2), 6),
                         "expansions": sum(min(c, len(r["expansions"])) for r in whole.values())}
                     for c in CHECKPOINTS}

    ran = {s: [u for t in stated if (u := unit(t, s)) is not None and "result" in u] for s in SEARCHES}
    outcome: dict[str, Any] = {}
    for s in SEARCHES:
        results = [u["result"] for u in ran[s]]
        outcome[s] = {"proved": {c: len(proved[s][c]) for c in CHECKPOINTS},
                      "newProofs": sorted(set(proved[s][BUDGET]) - set(proved[s][PREFIX])),
                      "exhausted": sum(1 for r in results if not r["proof"] and len(r["expansions"]) < BUDGET),
                      "capped": sum(1 for r in results if not r["proof"] and len(r["expansions"]) >= BUDGET),
                      "abandoned": sum(1 for t in stated if (unit(t, s) or {}).get("abandoned")),
                      "expansionsToProof": quantiles([float(len(r["expansions"])) for r in results if r["proof"]])}
    costs: dict[str, Any] = {}
    for s in SEARCHES:
        units_ = ran[s]
        repl_costs = {k: {"calls": sum(u["costs"][k]["calls"] for u in units_),
                          "seconds": round(sum(u["costs"][k]["seconds"] for u in units_), 1)}
                      for k in ("tactic", "export", "harness", "command")} if units_ else {}
        costs[s] = {"units": len(units_), "expansions": sum(len(u["result"]["expansions"]) for u in units_),
                    "draws": {k: sum((u.get("draws") or {}).get(k, 0) for u in units_)
                              for k in ("seeded", "shared", "drawn")},
                    "completionTokens": sum(e.get("completionTokens", 0) for e in draws_log if e["search"] == s),
                    "promptTokens": sum(e.get("promptTokens", 0) for e in draws_log if e["search"] == s),
                    "repl": repl_costs, "searchSeconds": quantiles([float(u["result"]["seconds"]) for u in units_]),
                    "fastExport": sum(1 for u in units_ if u.get("fastExport")),
                    "exportFailures": sum(u["result"].get("exportFailures", 0) for u in units_),
                    "rejected": sum(u["result"].get("rejected", 0) for u in units_)}
    mechanisms = {
        "groupsOutside": sum(u["result"]["outside"] for u in ran["groups"]),
        "groupsMade": {k: sum(u["result"]["groups"][k] for u in ran["groups"]) for k in ("single", "several")},
        "groupSearchesWithSeveral": sum(1 for u in ran["groups"] if u["result"]["groups"]["several"] > 0),
        "proofsThroughGroups": sum(1 for u in ran["groups"] if u["result"]["proof"] and u["result"]["groupsInProof"]),
        "wholeProofsWithLaterDraws": sum(1 for u in ran["whole"] if u["result"]["proof"] and any(
            d is not None and d.get("n", 0) >= 1 for d in u["result"].get("proofDraws", []))),
        "groupMerges": {k: sum(u["result"]["merges"][k] for u in ran["groups"]) for k in
                        ("arrivals", "new", "identical", "renamed", "reused", "checks", "refused")}}

    old = first_set_of_v8()
    compared = [(key, u) for key, u in sorted(latest.items())
                if (u or {}).get("result") and (old.get(key) or {}).get("result")]
    differing = [f"{d} / {s}" for (d, s), u in compared if not replicates(u, old[(d, s)])]
    c28 = {"compared": len(compared), "matched": len(compared) - len(differing), "differing": differing,
           "holds": bool(compared) and len(compared) - len(differing) >= REPLICATION_SHARE * len(compared)}
    sets = seeds()
    seen: set[tuple[int, str, int]] = set()
    repeated = overlapping = 0
    for entry in draws_log:
        key = (entry["index"], v7.draw_key(entry["prompt"]), entry["occurrence"])
        repeated += key in seen
        seen.add(key)
        overlapping += entry["occurrence"] < len(sets.get(entry["index"], {}).get(key[1], []))
    constructed = [u for s in SEARCHES for u in ran[s]]
    complete = sum(1 for e in draws_log if len(e["replies"]) == v8.SAMPLES)
    out: dict[str, Any] = {
        "experiment": "search-v0.9", "preregistrationSha256": sha256_file(PREREG),
        "stated": len(stated), "tasks": len(task_list),
        "proved": {s: {c: len(v) for c, v in proved[s].items()} for s in SEARCHES}, "provedTasks": proved,
        "outcome": outcome, "pairs": pairs, "tests": tests, "goalSharing": goal_sharing, "orderDuplicates": order,
        "byCheckpoint": by_checkpoint, "costs": costs, "mechanisms": mechanisms,
        "errors": sum(1 for r in latest.values() if r.get("error")),
        "abandoned": sum(1 for r in latest.values() if r.get("abandoned")),
        "attempts": len(rows) // len(SEARCHES),
        "C28": c28,
        "C29": {"draws": len(draws_log), "repeated": repeated, "overlappingSeeds": overlapping,
                "holds": repeated == 0 and overlapping == 0},
        "C30": {"units": len(constructed), "fastExport": sum(1 for u in constructed if u.get("fastExport")),
                "holds": bool(constructed) and sum(1 for u in constructed if u.get("fastExport"))
                >= COMPLETE_SHARE * len(constructed)},
        "C31": {"draws": len(draws_log), "complete": complete,
                "holds": complete >= COMPLETE_SHARE * len(draws_log)},
    }
    out["hypotheses"] = {name: {"supported": tests[name]["rejected"]} for name in COMPARISONS} | {
        "H88": {"supported": goal_sharing["holds"]}, "H89": {"supported": order["holds"]}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    c = [str(x) for x in CHECKPOINTS]
    lines = ["# Whole states and coupled goal groups with 256 expansions (search v0.9)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             f"Tasks: {s['tasks']}; stated in both searches: {s['stated']}; unit attempts: {s['attempts']}; "
             f"errors: {s['errors']}; abandoned searches: {s['abandoned']}.", "",
             "| Search | " + " | ".join(f"proved by {x}" for x in c) + " | frontier emptied | budget used up |",
             "| --- |" + " ---: |" * (len(c) + 2)]
    for search in SEARCHES:
        o = s["outcome"][search]
        lines.append(f"| {search} | " + " | ".join(str(o["proved"][x]) for x in c)
                     + f" | {o['exhausted']} | {o['capped']} |")
    lines += ["", "| Hypothesis | Pair | Tasks first more | Tasks second more | One-sided p | Rate difference "
                  "(95% interval) | Supported |", "| --- | --- | ---: | ---: | ---: | --- | --- |"]
    for name in COMPARISONS:
        p = s["pairs"][name]
        lines.append(f"| {name} | {p['first']} > {p['second']} | {p['tasksFirstMore']} | {p['tasksSecondMore']} | "
                     f"{p['signTestFirstMore']} | {p['rateDifference']} {p['interval95']} | "
                     f"{s['hypotheses'][name]['supported']} |")
    lines += ["", "| Discordant tasks (groups only / whole only) | " + " | ".join(c) + " |",
              "| --- |" + " ---: |" * len(c),
              "| H87's pair | " + " | ".join(f"{s['pairs']['H87']['checkpoints'][x]['firstOnly']} / "
                                         f"{s['pairs']['H87']['checkpoints'][x]['secondOnly']}" for x in c) + " |"]
    g, o = s["goalSharing"], s["orderDuplicates"]
    lines += ["", f"H88 (goal sharing grows past 48 expansions): goal-duplicate share {g['earlyShare']} in the first 48 "
                  f"expansions and {g['lateShare']} after them, over the {g['searches']} whole-state searches that ran "
                  f"past 48; difference {g['difference']}, 95% interval {g['interval95']}; supported: "
                  f"{s['hypotheses']['H88']['supported']}.",
              f"H89 (order duplicates under {o['limit']:.0%}): {o['orderDuplicates']} of {o['flagged']} whole-state "
              f"expansions, share {o['share']}, 95% interval {o['interval95']}; supported: "
              f"{s['hypotheses']['H89']['supported']}.", "",
              "| Whole-state expansions up to | Expansions | Order duplicates | Goal duplicates |",
              "| ---: | ---: | ---: | ---: |"]
    for x in c:
        b = s["byCheckpoint"][x]
        lines.append(f"| {x} | {b['expansions']} | {b['orderShare']} | {b['goalShare']} |")
    lines += ["", "## Cost", "", "| Search | Expansions | Draws (seeded / shared / new) | Completion tokens | REPL "
                                   "calls (tactic / export / harness) | Median search seconds |",
              "| --- | ---: | --- | ---: | --- | ---: |"]
    for search in SEARCHES:
        k = s["costs"][search]
        d, r = k["draws"], k["repl"]
        lines.append(f"| {search} | {k['expansions']} | {d['seeded']} / {d['shared']} / {d['drawn']} | "
                     f"{k['completionTokens']} | {r['tactic']['calls']} / {r['export']['calls']} / "
                     f"{r['harness']['calls']} | {(k['searchSeconds'] or {}).get('median')} |")
    m = s["mechanisms"]
    lines += ["", f"Mechanisms: coupled-group candidates discarded as coupled outside their group {m['groupsOutside']}; "
                  f"groups of several goals made {m['groupsMade']['several']}, in {m['groupSearchesWithSeveral']} "
                  f"searches, proofs through one {m['proofsThroughGroups']}; whole-state proofs using a goal's later "
                  f"draw {m['wholeProofsWithLaterDraws']}.",
              f"C28: {s['C28']['matched']} of {s['C28']['compared']} searches repeat search-v0.8's first set in their "
              f"first 48 expansions ({s['C28']['holds']}). C29: {s['C29']['repeated']} repeated occurrences and "
              f"{s['C29']['overlappingSeeds']} draws of seeded occurrences among {s['C29']['draws']} new draws "
              f"({s['C29']['holds']}). C30: fast export in {s['C30']['fastExport']} of {s['C30']['units']} searches "
              f"({s['C30']['holds']}). C31: {s['C31']['complete']} of {s['C31']['draws']} new draws with all "
              f"{v8.SAMPLES} completions ({s['C31']['holds']}).", "", "## Interpretation boundary", "",
              "One quantized open-weights prover at one sampling setting, breadth-first search, and one set of draws,",
              "on the theorems of one Mathlib slice. Identity is syntactic on instantiated Lean expressions; goals",
              "equal up to definitional unfolding stay apart."]
    write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration and entry points


def registration_payload() -> dict[str, Any]:
    sets = seeds()
    return {
        "experiment": "search-v0.9",
        "question": "with 256 expansions instead of search-v0.8's 48, does a search over metavariable-coupled goal groups prove "
                    "more than a search over whole states, and how do goal sharing and order duplicates change with "
                    "the budget",
        "tasks": {"source": "holdout-v0.1/tasks.json", "sourceSha256": sha256_file(holdout.TASKS), "count": 200,
                  "order": "search-v0.6's: the 140 tasks search-v0.5 did not run, then its 60"},
        "proposer": f"as search-v0.5 to v0.8: BFS-Prover-V2-7B in Q8_0, {v8.SAMPLES} completions at temperature "
                    f"{v8.TEMPERATURE}, at most {v8.MAX_TOKENS} tokens, the first goal followed by ':::', duplicates "
                    f"dropped; served by llama.cpp (build 11193) with 32 slots as for search-v0.8, on its own port and "
                    f"with the server's prompt cache in RAM switched off (--cache-ram 0) to bound its memory, which "
                    f"changes neither the prompts nor the sampling",
        "draws": {"set": "search-v0.8's first set (replicate 0), continued",
                  "seeds": "per task and printed goal, in occurrence order: the sets of search-v0.6 and search-v0.7 "
                           "that seeded search-v0.8's first set, then that set's new draws "
                           f"({sum(len(v) for g in sets.values() for v in g.values()):,} sets for "
                           f"{len(sets)} tasks)",
                  "seedsSha256": seeds_digest(sets),
                  "seedSources": {"searchV06Draws": sha256_file(v7.SEED_DRAWS), "searchV07Draws": sha256_file(v7.DRAWS),
                                  "searchV08Draws": sha256_file(v8.DRAWS), "searchV08Results": sha256_file(v8.RESULTS)},
                  "sharing": "within a task, the draws are shared by its two searches as in search-v0.6 to v0.8: "
                             "the n-th expansion of a printed goal gets the n-th set for it, seeded or drawn anew by "
                             "whichever search first needs it"},
        "searches": {"whole": "search_faithful.whole_state_search, unchanged from search-v0.8",
                     "groups": "search_faithful.coupled_search, unchanged from search-v0.8",
                     "leftOut": "search-v0.8's search over independent goals, which proved the same theorems as the "
                                "group search in each set except one theorem in one set; leaving it out saves a third "
                                "of the REPL time",
                     "identity": "goal_identity.py's export through the tactic defined once per task environment, "
                                 "as in search-v0.8",
                     "order": "the whole-state search first on tasks of even index, the group search first on odd"},
        "budget": {"expansionsPerSearch": BUDGET, "checkpoints": list(CHECKPOINTS), "tacticWallClockSeconds": 60,
                   "heartbeats": 40000},
        "execution": "a unit is one task: its two searches in turn, each in a fresh REPL; at most three units at a "
                     "time, since other programs share the machine's memory: a unit starts only while at least "
                     f"{START_GATE_GB:g} GB of commit charge is left and {START_SPACING:g} s after the previous start, "
                     "and a supervisor stops the runner while less than 8 GB is left (units in flight leave no rows "
                     "and run again); a unit that "
                     "raises is recorded as two error rows and run again, up to three attempts; a unit in which a "
                     "search was not constructed, for any reason, or was abandoned by a REPL timeout runs once more; "
                     "the latest attempt counts, and the new draws of earlier attempts are dropped; every row of "
                     "every attempt is kept",
        "measures": {"proved": "tasks whose search finds a proof that re-verifies from the statement, by each "
                               "checkpoint: a breadth-first search that proves a theorem within c expansions is the "
                               "search with budget c",
                     "stated": "tasks constructed in both searches; a search abandoned by a REPL timeout counts "
                               "as not proving its task, as in search-v0.8",
                     "frontier": "per search, the searches whose frontier emptied before the budget and those that "
                                 "used it up",
                     "sharing": "in the whole-state search, the shares of expansions that are order duplicates and "
                                "goal duplicates (faithful keys, as search-v0.8 recorded them), by checkpoint",
                     "cost": "expansions, draws (seeded, shared, new) and their tokens, REPL calls and seconds by "
                             "kind, search seconds",
                     "mechanisms": "as search-v0.8: outside-coupled discards, groups of several goals made and used "
                                   "in proofs, whole-state proofs through a goal's later draw"},
        "hypotheses": {
            **{name: f"the {WORDS[a]} proves more tasks than the {WORDS[b]} at {BUDGET} expansions: one-sided sign "
                     f"test at {ALPHA:g} on the stated tasks exactly one of the two proves"
               for name, (a, b) in COMPARISONS.items()},
            "H88": "goal sharing grows with the budget: in the whole-state searches that run past 48 expansions, the "
                   "share of goal duplicates among the expansions after the 48th exceeds the share among the first "
                   "48 (pooled over those searches); supported if the 95% interval of the difference, resampling "
                   f"modules ({BOOTSTRAP:,} resamples, seed {SEED}), lies above 0",
            "H89": f"order duplicates stay rare: over all expansions of the whole-state searches, the share of "
                   f"order duplicates is below {ORDER_LIMIT:.0%}; supported if the upper end of its 95% interval, "
                   f"resampling modules, is below {ORDER_LIMIT:.0%}"},
        "decisionRule": "each hypothesis is decided on its own: H87 by its sign test, H88 and H89 by their intervals; "
                        "a significant difference in the other direction than H87's would be reported, not tested",
        "analyses": {"interval": "the 95% percentile interval of the per-task difference in proof rate between the "
                                 f"two searches, resampling modules ({BOOTSTRAP:,} resamples, seed {SEED}, drawn in "
                                 "the order H87, H88, H89)",
                     "checkpoints": "proofs and discordant tasks at 48, 96, 192, and 256 expansions, reported without "
                                    "tests"},
        "power": "search-v0.8's first set differed on 2 tasks between these searches; if the larger budget "
                 "leaves the discordant tasks few, only a large effect can be detected: a one-sided p of at most 0.05 "
                 "takes at least 5 discordant tasks, all in one direction, or 7 against 1; the decisions are reported "
                 "whichever way they come out",
        "checks": {"C28": f"at least {REPLICATION_SHARE:.0%} of the searches stated here and in search-v0.8's first "
                          "set repeat its first 48 expansions and, where it found one within them, its proof",
                   "C29": "no goal occurrence has two new draws within a task, and no new draw replaces a seeded "
                          "one",
                   "C30": f"at least {COMPLETE_SHARE:.0%} of the searches export through the defined tactic",
                   "C31": f"at least {COMPLETE_SHARE:.0%} of the new draws have all {v8.SAMPLES} completions"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsSeenBeforeRegistration": "every earlier experiment, including search-v0.8 in full; the development "
                                         "runs below; no search of this registration had run on a corpus task "
                                         "beyond 48 expansions",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


DEVELOPMENT_CHECKS: list[str] = [
    "offline: the summary computed from search-v0.8's first set, read as if it were this run's rows, gives that set's "
    "proofs (whole states 40, groups 42 of the 164 tasks constructed in both) and C28 for every compared search",
    "--prefix 4, with the seeds and 48 expansions, the three searches of an earlier version of this runner: on the first "
    "four tasks of the run, the three constructed tasks repeated search-v0.8's first set in all nine searches, "
    "expansions and outcomes, without a new draw; PolishSpace.Equiv.measurableEquiv was constructed in no search, as in "
    "search-v0.8",
    "--develop 6 --budget 384 --workers 6, fresh draws on search-v0.8's development theorems: six REPLs importing at "
    "once left 0.6 GB of commit charge (a REPL holds 4 to 7 GB, the server 12 GB, growing by 2 GB with its prompt cache "
    "in RAM); a REPL's memory hardly grew with its candidate tactics (6.6 GB at 63 and at 160, 4.3 GB at 130 and at "
    "287, 6.2 GB at 63 and at 145); draws ran at 380 to 390 an hour with three units running; a watchdog stopped the "
    "run when other programs took the commit charge left below 5 GB",
    "--develop 6 --budget 256 --workers 3, the two searches, the server's prompt cache off (11.4 GB): stopped by the "
    "watchdog after five minutes, at 283 draws an hour, when other programs took the commit charge left below 8 GB with "
    "two REPLs running; hence at most three units at a time, the start gate, and the supervisor's floor"]


def _commit_available_gb() -> float | None:
    """The commit charge still available (Windows), in GB."""

    class Status(ctypes.Structure):
        _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                    ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                    ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                    ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                    ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]

    try:
        status = Status()
        status.dwLength = ctypes.sizeof(Status)
        if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):  # type: ignore[attr-defined]
            return None
        return round(status.ullAvailPageFile / 2 ** 30, 1)
    except Exception:  # noqa: BLE001 - not on Windows
        return None


class MemorySampler(threading.Thread):
    """Every 15 s: the private bytes and working sets of this process's REPL descendants, and the commit left."""

    def __init__(self) -> None:
        super().__init__(daemon=True)
        self.stopped = threading.Event()
        self.peak = {"replPrivateGB": 0.0, "largestReplPrivateGB": 0.0, "replWorkingSetGB": 0.0,
                     "runnerPrivateGB": 0.0, "minCommitAvailableGB": None}

    def run(self) -> None:
        import psutil

        me = psutil.Process()
        while not self.stopped.wait(15):
            private = working = largest = 0.0
            for child in me.children(recursive=True):
                try:
                    if child.name().lower().startswith("repl"):
                        info = child.memory_info()
                        private += info.private / 2 ** 30
                        working += info.rss / 2 ** 30
                        largest = max(largest, info.private / 2 ** 30)
                except psutil.Error:
                    continue
            commit = _commit_available_gb()
            p = self.peak
            p["replPrivateGB"] = round(max(p["replPrivateGB"], private), 1)
            p["replWorkingSetGB"] = round(max(p["replWorkingSetGB"], working), 1)
            p["largestReplPrivateGB"] = round(max(p["largestReplPrivateGB"], largest), 1)
            p["runnerPrivateGB"] = round(max(p["runnerPrivateGB"], me.memory_info().private / 2 ** 30), 1)
            if commit is not None:
                p["minCommitAvailableGB"] = commit if p["minCommitAvailableGB"] is None \
                    else min(p["minCommitAvailableGB"], commit)


def development_tasks(count: int) -> list[dict[str, Any]]:
    """Hard theorems of the first slice outside the corpus, as search-v0.8's development chose them (seed 7)."""
    v3 = ROOT / "experiments" / "search-v0.3"
    proved: dict[str, bool] = {}
    for line in (v3 / "results.jsonl").read_text(encoding="utf-8").splitlines():
        row = json.loads(line) if line.strip() else {}
        if row.get("constructed") and "result" in row:
            proved[row["declaration"]] = proved.get(row["declaration"], False) or bool(row["result"]["proof"])
    corpus = {t["declaration"] for t in v6.tasks()}
    candidates = [t for t in json.loads((v3 / "tasks.json").read_text(encoding="utf-8"))
                  if t["declaration"] not in corpus and proved.get(t["declaration"]) is False]
    return [t | {"index": i} for i, t in enumerate(random.Random(7).sample(candidates, count))]


class TrackedRepl(v8.sf.CountingRepl):
    """search-v0.8's counting REPL, listed while alive so that the development status can read its calls."""

    live: list["TrackedRepl"] = []

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        TrackedRepl.live.append(self)


def development_status(started: float, completions: list[int], stopped: threading.Event) -> None:
    """Every five minutes: completions per hour, and each live REPL's candidate tactics and private memory."""
    import psutil

    while not stopped.wait(300):
        repls = []
        for repl in list(TrackedRepl.live):
            process_ = repl.process
            if process_ is None or process_.poll() is not None:
                continue
            try:
                private = sum(c.memory_info().private for c in psutil.Process(process_.pid).children(recursive=True)
                              if c.name().lower().startswith("repl")) / 2 ** 30
            except psutil.Error:
                continue
            repls.append({"tactics": repl.costs["tactic"]["calls"], "privateGB": round(private, 2)})
        hours = (time.monotonic() - started) / 3600
        print(json.dumps({"status": time.strftime("%H:%M:%S"), "completionsPerHour": round(completions[0] / hours),
                          "drawsPerHour": round(completions[0] / hours / v8.SAMPLES, 1), "repls": repls,
                          "commitAvailableGB": _commit_available_gb()}), flush=True)


def develop(count: int, budget: int, workers: int) -> int:
    """The three searches with fresh draws on development theorems, `workers` units at a time, with the draw
    throughput and the memory of the REPL processes."""
    if not server_alive():
        raise SystemExit(f"no prover server on 127.0.0.1:{PORT}")
    prover.MODEL_LOG = None
    completions = [0]
    single = v8.completion

    def counted(prompt: str) -> dict[str, Any] | None:
        reply = single(prompt)
        completions[0] += 1
        return reply

    v8.completion = counted
    v8.sf.CountingRepl = TrackedRepl
    sampler = MemorySampler()
    sampler.start()
    started = time.monotonic()
    threading.Thread(target=development_status, args=(started, completions, sampler.stopped), daemon=True).start()
    drawn = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(gated_unit, task, {}, budget) for task in development_tasks(count)]
        for future in concurrent.futures.as_completed(futures):
            rows, log = future.result()
            drawn += len(log)
            hours = (time.monotonic() - started) / 3600
            for row in rows:
                result = row.get("result") or {}
                print(json.dumps({"task": row["declaration"][:40], "search": row["search"],
                                  "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                                  "draws": row["draws"], "seconds": result.get("seconds"),
                                  "abandoned": row.get("abandoned"), "constructed": row.get("constructed"),
                                  "fast": row.get("fastExport")}, ensure_ascii=False), flush=True)
            print(json.dumps({"unitDone": rows[0]["declaration"][:40], "unitDraws": len(log),
                              "elapsedHours": round(hours, 2), "drawsPerHour": round(drawn / hours, 1),
                              "completeDraws": sum(1 for e in log if len(e["replies"]) == v8.SAMPLES),
                              "memoryPeak": sampler.peak}), flush=True)
    sampler.stopped.set()
    return 0


def prefix(count: int) -> int:
    """The first tasks of the run with 48 expansions in the seeded set, compared with search-v0.8's first set."""
    sets = seeds()
    old = first_set_of_v8()
    for task in units()[:count]:
        rows, log = run_unit(task, sets.get(task["index"], {}), PREFIX)
        for row in rows:
            o = old.get((row["declaration"], row["search"]))
            same = None
            if row.get("result") and (o or {}).get("result"):
                same = replicates(row, o)
            print(json.dumps({"task": row["declaration"][:40], "search": row["search"],
                              "expansions": len((row.get("result") or {}).get("expansions", [])),
                              "proof": bool((row.get("result") or {}).get("proof")), "repeatsV08": same,
                              "draws": row["draws"]}, ensure_ascii=False), flush=True)
        print(json.dumps({"task": task["declaration"], "newDraws": len(log)}), flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prefix", type=int, metavar="N")
    mode.add_argument("--develop", type=int, metavar="N")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--budget", type=int, default=BUDGET, help="with --develop")
    args = parser.parse_args()
    prover.ENDPOINT = ENDPOINT  # read by search-v0.8's completion at each request
    if args.prefix:
        return prefix(args.prefix)
    if args.develop:
        return develop(args.develop, args.budget, args.workers)
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if args.run:
        for name, path in IMPLEMENTATIONS.items():
            if prereg["implementationSha256"][name] != sha256_file(path):
                raise SystemExit(f"implementation {name} changed since registration")
        if prereg["draws"]["seedsSha256"] != seeds_digest(seeds()):
            raise SystemExit("the seeds differ from the registered ones")
        if not server_alive():
            raise SystemExit(f"no prover server on 127.0.0.1:{PORT}")
        run_all(args.workers)
        summary = json.loads(json.dumps(summarize(read_rows(), read_draws())))
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.9-run": summary["hypotheses"], "proved": summary["proved"]}))
        return 0
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["drawsSha256"] != sha256_file(DRAWS):
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = json.loads(json.dumps(summarize(read_rows(), read_draws())))
    for key in ("proved", "outcome", "pairs", "tests", "goalSharing", "orderDuplicates", "byCheckpoint", "costs",
                "mechanisms", "C28", "C29", "C30", "C31", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.9-check-ok: attempts={summary['attempts']} newDraws={summary['C29']['draws']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
