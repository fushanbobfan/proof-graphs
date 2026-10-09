#!/usr/bin/env python3
"""Search v0.10: search-v0.8 and search-v0.9 again, with goal identity from the typed key.

  python scripts/run_search_typed.py --develop N [--budget B]
  python scripts/run_search_typed.py --register
  python scripts/run_search_typed.py --run [--workers 4]
  python scripts/run_search_typed.py --check-committed

search-v0.8 compared a whole-state search, a search over independent goals, and a search over goals coupled by
metavariables, each with 48 expansions in three sets of draws; search-v0.9 ran the first and third with 256
expansions in the first set. Both identified goals by the expression key of `goal_identity`, whose known defects the
typed key of `goal_identity_typed` corrects. This experiment reruns both with every identity decision made by the
typed key (`search_typed`): the whole-state search's drops, the goal search's merges and its check that a candidate
left the carried goals unchanged, and the group search's partition and merges. Each set's draws are seeded with every
candidate set recorded for it before (search-v0.8's draws, and in the first set also search-v0.6's, v0.7's and
v0.9's), so that where the two keys decide alike the searches repeat the earlier ones, and the prover is asked only
for goals the typed searches reach anew. In the first set the whole-state and group searches run 256 expansions,
whose first 48 are their 48-expansion searches, and the goal search 48; in the other sets all three run 48. This is a
correction and sensitivity study of search-v0.8 and v0.9, not a fresh confirmation. At each identity decision the
searches also record whether the expression key had met the state or goal before: an audit of that key on the typed
searches' own trajectories.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import hashlib
import json
import os
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_coupled as v8  # noqa: E402
import run_search_coupled_deep as deep  # noqa: E402
import run_search_paired as v6  # noqa: E402
import run_search_renaming as v7  # noqa: E402
import search_typed as st  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402
from search_harness import State  # noqa: E402

ROOT = v8.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.10"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "typed": ROOT / "scripts" / "search_typed.py", "faithful": ROOT / "scripts" / "search_faithful.py",
    "identityTyped": ROOT / "scripts" / "goal_identity_typed.py", "identity": ROOT / "scripts" / "goal_identity.py",
    "selection": ROOT / "scripts" / "search_goal_selection.py", "renaming": ROOT / "scripts" / "renaming.py",
    "draws": ROOT / "scripts" / "common_draws.py", "prover": ROOT / "scripts" / "step_prover.py",
    "harness": ROOT / "scripts" / "search_harness.py", "repl": ROOT / "scripts" / "lean_repl.py",
    "searchV08Runner": ROOT / "scripts" / "run_search_coupled.py",
    "searchV09Runner": ROOT / "scripts" / "run_search_coupled_deep.py", "runner": Path(__file__).resolve(),
}
REPLICATES = v8.REPLICATES
SEARCHES = v8.SEARCHES
PREFIX, DEEP = v8.BUDGET, deep.BUDGET
CHECKPOINTS = deep.CHECKPOINTS
FUNCTIONS: dict[str, Callable[..., dict[str, Any]]] = {
    "whole": st.whole_state_search, "goals": st.and_or_search, "groups": st.coupled_search}
COMPARISONS = {"groupsOverGoals": ("groups", "goals"), "groupsOverWhole": ("groups", "whole"),
               "goalsOverWhole": ("goals", "whole")}
ALPHA = 0.05
BOOTSTRAP = 2000
SEED = 20261009
MAX_ATTEMPTS = 3
AGREEMENT = 0.99
TOLERANCE = 2
EXPORT_CEILING = 0.01

QUESTION = ("do search-v0.8's comparison of whole-state, independent-goal, and coupled-group searches at 48 "
            "expansions, and search-v0.9's comparison of the whole-state and group searches at 256, come out the same "
            "when every identity decision is made by the typed key instead of the expression key")
HYPOTHESES = {
    "H103": "at 48 expansions over the three sets of draws, no comparison of two searches is significant after Holm's "
            "adjustment (one-sided sign tests on the tasks whose scores, the sets in which a search proves the task, "
            "differ, as registered in search-v0.8), as in search-v0.8",
    "H104": "at 256 expansions in the first set, the group search does not prove significantly more than the "
            "whole-state search (one-sided sign test, p >= 0.05), as in search-v0.9",
    "H105": f"where both keys exported, the typed and expression keys agree on at least {AGREEMENT:.0%} of the "
            "whole-state searches' decisions whether a generated state had been generated before",
    "H106": f"in every set, each search proves within {TOLERANCE} tasks of what it proved with the expression key at the "
            "same budget (search-v0.8 at 48 expansions, search-v0.9 at 256)",
}
CHECKS = {
    "C40": "every unit is final, and no latest row records an error",
    "C41": f"the typed export fails on fewer than {EXPORT_CEILING:.0%} of the states the searches export",
}


def budget_of(replicate: int, search: str) -> int:
    return DEEP if replicate == 0 and search in deep.SEARCHES else PREFIX


# ---------------------------------------------------------------- draws


def _extend(sets: dict[int, dict[str, list[list[str]]]], entries: list[dict[str, Any]], what: str) -> None:
    grouped: dict[int, dict[str, dict[int, list[str]]]] = {}
    for entry in entries:
        grouped.setdefault(entry["index"], {}).setdefault(v7.draw_key(entry["prompt"]), {})[entry["occurrence"]] = \
            entry["candidates"]
    for index, goals in grouped.items():
        for goal, by_occurrence in goals.items():
            have = sets.setdefault(index, {}).setdefault(goal, [])
            for n in sorted(by_occurrence):
                assert n == len(have), f"{what}'s draws of a goal do not extend the earlier ones"
                have.append(by_occurrence[n])


def seeds() -> dict[int, dict[int, dict[str, list[list[str]]]]]:
    """Per set, task, and goal, in occurrence order: every candidate set recorded for that set before."""
    out: dict[int, dict[int, dict[str, list[list[str]]]]] = {0: deep.seeds()}
    _extend(out[0], deep.read_draws(), "search-v0.9")
    recorded = v8.read_draws()
    for replicate in range(1, REPLICATES):
        out[replicate] = {}
        _extend(out[replicate], [e for e in recorded if e["replicate"] == replicate], "search-v0.8")
    return out


def read_draws() -> list[dict[str, Any]]:
    if not DRAWS.exists():
        return []
    return [json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def write_draws(entries: list[dict[str, Any]], level: int) -> None:
    temporary = DRAWS.with_name(DRAWS.name + ".tmp")
    temporary.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries)
                                        .encode("utf-8"), compresslevel=level, mtime=0))
    os.replace(temporary, DRAWS)


# ---------------------------------------------------------------- running


def run_one(task: dict[str, Any], search: str, propose: Callable[[State], list[str]], budget: int) -> dict[str, Any]:
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = st.TypedCountingRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = st.TypedSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            result = FUNCTIONS[search](repl, made.proof_state, [made.goal], propose, budget,
                                       verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "typedFastExport": getattr(repl, "typed_fast_export", False),
                           "fastExport": getattr(repl, "fast_export", False),
                           "pickGoalDefined": getattr(repl, "pick_goal_defined", False),
                           "costs": repl.cost_summary(),
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout", "costs": repl.cost_summary(),
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_unit(replicate: int, task: dict[str, Any],
             sets: dict[str, list[list[str]]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """One task in one set: the three searches in turn, in search-v0.8's rotating order, sharing the set's draws."""
    draws = v8.ReplicateDraws(sets)
    rows = []
    for position, search in enumerate(v8.search_order(task["index"], replicate)):
        budget = budget_of(replicate, search)
        row = run_one(task, search, draws.proposer(search), budget)
        rows.append(row | {"replicate": replicate, "index": task["index"], "position": position, "budget": budget,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"replicate": replicate, "index": task["index"], "declaration": task["declaration"]} | e for e in draws.log]
    return rows, log


def units() -> list[tuple[int, dict[str, Any]]]:
    order = v6.execution_order(v6.tasks())
    return [(r, t) for r in range(REPLICATES) for t in order]


def read_rows() -> list[dict[str, Any]]:
    if not RESULTS.exists():
        return []
    return [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]


def unit_done(rows: list[dict[str, Any]]) -> bool:
    """search-v0.9's rule for one (set, task): the latest row of each search counts; an attempt that raised is
    repeated up to MAX_ATTEMPTS attempts, one in which a search was not constructed or was abandoned once."""
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


def done_units(rows: list[dict[str, Any]]) -> set[tuple[int, str]]:
    grouped: dict[tuple[int, str], list[dict[str, Any]]] = {}
    for r in rows:
        grouped.setdefault((r["replicate"], r["declaration"]), []).append(r)
    return {key for key, rs in grouped.items() if unit_done(rs)}


def run_pass(workers: int, sets: dict[int, dict[int, dict[str, list[list[str]]]]]) -> int:
    rows = read_rows()
    done = done_units(rows)
    draws_log = [e for e in read_draws() if (e["replicate"], e["declaration"]) in done]
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded(replicate: int, task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            deep.admit()
            return run_unit(replicate, task, sets[replicate].get(task["index"], {}))
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s,
                     "replicate": replicate, "index": task["index"], "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)} for s in SEARCHES], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        unit_rows, unit_draws = result
        with lock:
            draws_log.extend(unit_draws)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                for row in unit_rows:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            write_draws(draws_log, 6)
            print(json.dumps({"replicate": unit_rows[0]["replicate"], "task": unit_rows[0]["declaration"][:40],
                              "searches": {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                                         bool((r.get("result") or {}).get("proof"))) for r in unit_rows},
                              "draws": len(unit_draws), "error": unit_rows[0].get("error"),
                              "at": time.strftime("%H:%M:%S")}, ensure_ascii=False), flush=True)

    todo = [(r, t) for r, t in units() if (r, t["declaration"]) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, r, t) for r, t in todo]
        for future in concurrent.futures.as_completed(futures):
            record(future.result())
    draws_log.sort(key=lambda e: (e["replicate"], e["index"]))
    write_draws(draws_log, 9)
    return len(todo)


def run_all(workers: int) -> None:
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    sets = seeds()
    for _ in range(MAX_ATTEMPTS + 1):
        if run_pass(workers, sets) == 0:
            return
    if len(done_units(read_rows())) < len(units()):
        raise SystemExit("some units are not final after the passes allowed")


# ---------------------------------------------------------------- summary


def proved_within(unit: dict[str, Any] | None, limit: int) -> bool:
    return deep.proved_within(unit, limit)


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]]) -> dict[str, Any]:
    task_list = v6.tasks()
    module_of = {t["declaration"]: t["module"] for t in task_list}
    latest = {(r["replicate"], r["declaration"], r["search"]): r for r in rows}

    def unit(r: int, decl: str, s: str) -> dict[str, Any] | None:
        return latest.get((r, decl, s))

    stated = [t["declaration"] for t in task_list
              if all((u := unit(r, t["declaration"], s)) is not None and u.get("constructed")
                     for r in range(REPLICATES) for s in SEARCHES)]
    by_module: dict[str, list[str]] = {}
    for x in stated:
        by_module.setdefault(module_of[x], []).append(x)
    rng = random.Random(SEED)
    proved = {s: {r: sorted(x for x in stated if proved_within(unit(r, x, s), PREFIX)) for r in range(REPLICATES)}
              for s in SEARCHES}
    scores = {s: {x: sum(x in proved[s][r] for r in range(REPLICATES)) for x in stated} for s in SEARCHES}
    pairs: dict[str, Any] = {}
    for name, (first, second) in COMPARISONS.items():
        d = {x: scores[first][x] - scores[second][x] for x in stated}
        higher, lower = sum(v > 0 for v in d.values()), sum(v < 0 for v in d.values())
        pairs[name] = {"first": first, "second": second, "tasksFirstMore": higher, "tasksSecondMore": lower,
                       "signTestFirstMore": v8.sign_upper(higher, higher + lower),
                       "meanRateDifference": round(sum(d.values()) / (len(d) * REPLICATES), 6) if d else None,
                       "interval95": deep.module_interval(
                           by_module, lambda xs: sum(d[x] for x in xs) / (len(xs) * REPLICATES), rng) if d else None,
                       "perReplicate": {r: {"firstOnly": len(set(proved[first][r]) - set(proved[second][r])),
                                            "secondOnly": len(set(proved[second][r]) - set(proved[first][r]))}
                                        for r in range(REPLICATES)}}
    tests = v8.holm({name: pairs[name]["signTestFirstMore"] for name in COMPARISONS}, ALPHA)

    deep_proved = {s: {c: sorted(x for x in stated if proved_within(unit(0, x, s), c)) for c in CHECKPOINTS}
                   for s in deep.SEARCHES}
    a, b = set(deep_proved["groups"][DEEP]), set(deep_proved["whole"][DEEP])
    d256 = {x: int(x in a) - int(x in b) for x in stated}
    p256 = v8.sign_upper(len(a - b), len(a - b) + len(b - a))
    deep_pair = {"groupsOnly": len(a - b), "wholeOnly": len(b - a), "signTestGroupsMore": p256,
                 "rateDifference": round(sum(d256.values()) / len(d256), 6) if d256 else None,
                 "interval95": deep.module_interval(by_module, lambda xs: sum(d256[x] for x in xs) / len(xs), rng)
                 if d256 else None}

    ran = [u for u in latest.values() if u.get("result")]

    def audit(field: str, searches: tuple[str, ...]) -> dict[str, Any]:
        total = {"agree": 0, "typedOnly": 0, "expressionOnly": 0, "unexported": 0}
        for u in ran:
            if u["search"] in searches:
                for k in total:
                    total[k] += (u["result"].get(field) or {}).get(k, 0)
        decided = total["agree"] + total["typedOnly"] + total["expressionOnly"]
        return total | {"agreement": total["agree"] / decided if decided else None}

    drops = audit("dropsAgainstExpressionKey", ("whole",))
    merges = audit("mergesAgainstExpressionKey", ("goals", "groups"))
    carried = {k: sum((u["result"].get("carriedChecks") or {}).get(k, 0) for u in ran)
               for k in ("typed", "printed", "disagree")}
    attempts = sum(u["result"].get("exportAttempts", 0) for u in ran)
    failures = sum(u["result"].get("exportFailures", 0) for u in ran)

    old8 = {(r["replicate"], r["declaration"], r["search"]): r
            for r in (json.loads(l) for l in v8.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip())}
    old9 = deep.latest_rows(deep.read_rows())
    migration: dict[str, Any] = {"budget48": {}, "budget256": {}}
    within = True
    for r in range(REPLICATES):
        for s in SEARCHES:
            both = [x for x in stated if (old8.get((r, x, s)) or {}).get("constructed")]
            now = {x for x in both if proved_within(unit(r, x, s), PREFIX)}
            before = {x for x in both if proved_within(old8.get((r, x, s)), PREFIX)}
            within &= abs(len(now) - len(before)) <= TOLERANCE
            migration["budget48"][f"{r}:{s}"] = {"tasks": len(both), "typed": len(now), "expression": len(before),
                                                 "gained": sorted(now - before), "lost": sorted(before - now)}
    for s in deep.SEARCHES:
        both = [x for x in stated if (old9.get((x, s)) or {}).get("constructed")]
        now = {x for x in both if proved_within(unit(0, x, s), DEEP)}
        before = {x for x in both if proved_within(old9.get((x, s)), DEEP)}
        within &= abs(len(now) - len(before)) <= TOLERANCE
        migration["budget256"][s] = {"tasks": len(both), "typed": len(now), "expression": len(before),
                                     "gained": sorted(now - before), "lost": sorted(before - now)}

    def shares(results: list[dict[str, Any]], limit: int) -> dict[str, Any]:
        marks = [deep.flags(res, 0, limit) for res in results]
        return {"flagged": sum(m[0] for m in marks), "orderShare": round(deep.share(marks, 1), 6),
                "goalShare": round(deep.share(marks, 2), 6)}

    whole48 = [unit(r, x, "whole")["result"] for r in range(REPLICATES) for x in stated
               if (unit(r, x, "whole") or {}).get("result")]
    old_whole48 = [old8[(r, x, "whole")]["result"] for r in range(REPLICATES) for x in stated
                   if (old8.get((r, x, "whole")) or {}).get("result")]
    whole256 = [unit(0, x, "whole")["result"] for x in stated if (unit(0, x, "whole") or {}).get("result")]
    old_whole256 = [old9[(x, "whole")]["result"] for x in stated if (old9.get((x, "whole")) or {}).get("result")]
    duplicates = {"typed48": shares(whole48, PREFIX), "expression48": shares(old_whole48, PREFIX),
                  "typed256": {c: shares(whole256, c) for c in CHECKPOINTS},
                  "expression256": {c: shares(old_whole256, c) for c in CHECKPOINTS}}
    groups = [u for u in ran if u["search"] == "groups"]
    mechanisms = {"groupsMade": {k: sum(u["result"]["groups"][k] for u in groups) for k in ("single", "several")},
                  "proofsThroughGroups": sum(1 for u in groups if u["result"]["proof"] and u["result"]["groupsInProof"]),
                  "entangled": sum(u["result"].get("entangled", 0) for u in ran if u["search"] == "goals"),
                  "outside": sum(u["result"].get("outside", 0) for u in groups)}
    costs = {s: {"units": sum(1 for u in ran if u["search"] == s),
                 "draws": {k: sum((u.get("draws") or {}).get(k, 0) for u in ran if u["search"] == s)
                           for k in ("seeded", "shared", "drawn")},
                 "repl": {k: {"calls": sum(u["costs"][k]["calls"] for u in ran if u["search"] == s),
                              "seconds": round(sum(u["costs"][k]["seconds"] for u in ran if u["search"] == s), 1)}
                          for k in ("tactic", "export", "harness", "command")},
                 "searchSeconds": quantiles([float(u["result"]["seconds"]) for u in ran if u["search"] == s])}
             for s in SEARCHES}
    all_done = len(done_units(rows)) == len(units())
    errors = sum(1 for u in latest.values() if u.get("error"))
    out: dict[str, Any] = {
        "experiment": "search-v0.10", "preregistrationSha256": sha256_file(PREREG),
        "tasks": len(task_list), "stated": len(stated),
        "proved48": {s: {r: len(v) for r, v in proved[s].items()} for s in SEARCHES}, "provedTasks48": proved,
        "proved256": {s: {c: len(v) for c, v in deep_proved[s].items()} for s in deep.SEARCHES},
        "pairs48": pairs, "tests48": tests, "pair256": deep_pair,
        "audit": {"drops": drops, "merges": merges, "carriedChecks": carried,
                  "typedExports": {"attempts": attempts, "failures": failures}},
        "migration": migration, "duplicates": duplicates, "mechanisms": mechanisms, "costs": costs,
        "draws": {"new": len(draws_log), "completionTokens": sum(e.get("completionTokens", 0) for e in draws_log)},
        "errors": errors, "abandoned": sum(1 for u in latest.values() if u.get("abandoned")),
        "attempts": len(rows) // len(SEARCHES),
    }
    out["hypotheses"] = {
        "H103": {"tests": tests, "holds": not any(t["rejected"] for t in tests.values())},
        "H104": {"p": p256, "holds": p256 is None or p256 >= ALPHA},
        "H105": {"agreement": drops["agreement"],
                 "holds": drops["agreement"] is not None and drops["agreement"] >= AGREEMENT},
        "H106": {"holds": within},
    }
    out["checks"] = {
        "C40": {"final": all_done, "errors": errors, "holds": all_done and errors == 0},
        "C41": {"attempts": attempts, "failures": failures,
                "holds": attempts > 0 and failures < EXPORT_CEILING * attempts},
    }
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# Searches with the typed key (search v0.10)", "",
             f"Frozen in `preregistration.json` (SHA-256 `{s['preregistrationSha256']}`).", "",
             f"Tasks: {s['tasks']}; stated in all nine searches: {s['stated']}; unit attempts: {s['attempts']}.", "",
             "| Search | set 0 | set 1 | set 2 | (48 expansions) |", "|---|---:|---:|---:|---|"]
    for name in SEARCHES:
        p = s["proved48"][name]
        lines.append(f"| {name} | {p[0] if 0 in p else p['0']} | {p[1] if 1 in p else p['1']} | "
                     f"{p[2] if 2 in p else p['2']} | |")
    lines += ["", f"At 256 expansions in set 0: {s['proved256']}; groups only {s['pair256']['groupsOnly']}, whole only "
                  f"{s['pair256']['wholeOnly']}, one-sided p {s['pair256']['signTestGroupsMore']}.", "",
              f"Audit of the expression key: drops {s['audit']['drops']}; merges {s['audit']['merges']}.", "",
              "## Hypotheses", ""]
    for key, entry in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, entry in s["checks"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {CHECKS[key]}.")
    write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration and development


def registration_payload() -> dict[str, Any]:
    sets = seeds()
    return {
        "experiment": "search-v0.10",
        "question": QUESTION,
        "kind": "a correction and sensitivity study of search-v0.8 and search-v0.9, whose results were known when it "
                "was registered; not a fresh confirmation",
        "tasks": {"source": "holdout-v0.1/tasks.json, as in search-v0.6 to search-v0.9",
                  "sourceSha256": sha256_file(v6.holdout.TASKS), "count": len(v6.tasks())},
        "seeds": {"rule": "per set, task, and goal, in occurrence order: set 0 has search-v0.6's and search-v0.7's "
                          "recorded draws, search-v0.8's first set's new draws, and search-v0.9's; sets 1 and 2 have "
                          "search-v0.8's draws of those sets; a goal expanded more often than its seeds cover is drawn "
                          "afresh, shared by the set's searches",
                  "sha256": {str(r): deep.seeds_digest(sets[r]) for r in sets}},
        "comparedResults": {"searchV08Results": sha256_file(v8.RESULTS), "searchV08Draws": sha256_file(v8.DRAWS),
                            "searchV09Results": sha256_file(deep.RESULTS), "searchV09Draws": sha256_file(deep.DRAWS)},
        "searches": "search_typed: search-v0.8's three searches with the typed key for every identity decision; a state "
                    "or goal whose typed export fails is never merged; where an export fails, the check that a "
                    "candidate left the carried goals unchanged falls back to printed goals; groups of several goals "
                    "merge only when their printed goals also agree, since their proofs are reused verbatim; draws "
                    "are keyed by printed goal text, what the prover sees",
        "budgets": {"set0": {"whole": DEEP, "groups": DEEP, "goals": PREFIX}, "sets1and2": PREFIX,
                    "checkpoints": list(CHECKPOINTS),
                    "note": "breadth-first searches with the same draws, so a search's first 48 expansions are its "
                            "48-expansion search"},
        "proposer": "BFS-Prover-V2-7B as in search-v0.8, served on port 8091 as in search-v0.9; 16 samples per draw at "
                    "temperature 1.0, 64 tokens",
        "execution": "each (set, task) unit in search-v0.8's rotating order of searches, each search in a fresh REPL "
                     "whose environment defines the typed and the expression exporters after its imports (and "
                     "pick_goal where missing); set 0 first; four units at a time, started only while enough commit "
                     "charge is left; units resumed by search-v0.9's attempt rule",
        "measures": {"proved": "tasks proved within a budget, over the tasks stated in all nine searches",
                     "scores": "per task and search, the number of sets in which the search proves it at 48",
                     "audit": "at each whole-state drop decision and each goal arrival, whether the typed key and the "
                              "expression key had each met the state or goal before",
                     "migration": "tasks proved under each key, per set and search, with the tasks gained and lost",
                     "duplicates": "order and goal duplicates of the whole-state search under the typed key, beside "
                                   "search-v0.8's and v0.9's under the expression key"},
        "hypotheses": HYPOTHESES,
        "checks": CHECKS,
        "tests": "H103 by one-sided sign tests on task scores under Holm's procedure at 0.05, as search-v0.8 registered; "
                 "H104 by a one-sided sign test at 0.05; intervals resample modules and do not decide",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


DEVELOPMENT_CHECKS = [
    "the hypotheses, checks, and measures above were written before any development run",
    "--develop 2 --budget 4 ran the three typed searches on search-v0.9's first two development theorems (hard "
    "theorems of the first slice outside the corpus) with fresh draws: in every session both exporters and the needed "
    "pick_goal were defined, no export failed, and every search was constructed; it printed the audit counts on these "
    "two theorems (all 50 decisions agreed); no unit of the corpus was run",
]


def develop(count: int, budget: int) -> int:
    """The three typed searches on search-v0.9's development theorems (outside the corpus), fresh draws."""
    if not deep.server_alive():
        raise SystemExit(f"the prover does not answer on port {deep.PORT}")
    prover.ENDPOINT = deep.ENDPOINT
    for task in deep.development_tasks(count):
        draws = v8.ReplicateDraws({})
        for search in SEARCHES:
            started = time.monotonic()
            row = run_one(task, search, draws.proposer(search), budget)
            result = row.get("result") or {}
            print(json.dumps({"task": task["declaration"][:40], "search": search, "constructed": row.get("constructed"),
                              "typedFastExport": row.get("typedFastExport"), "fastExport": row.get("fastExport"),
                              "expansions": len(result.get("expansions", [])),
                              "exportFailures": result.get("exportFailures"),
                              "audit": result.get("dropsAgainstExpressionKey") or result.get("mergesAgainstExpressionKey"),
                              "abandoned": row.get("abandoned"), "seconds": round(time.monotonic() - started, 1)}),
                  flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--develop", type=int)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--budget", type=int, default=4)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.develop:
        return develop(args.develop, args.budget)
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    for name, path in IMPLEMENTATIONS.items():
        if name != "runner" and prereg["implementationSha256"][name] != sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        run_all(args.workers)
        rows, draws_log = read_rows(), read_draws()
        summary = summarize(rows, draws_log)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}))
        return 0
    if not RESULTS.exists():
        print("search-v0.10: registered, no results yet")
        return 0
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(read_rows(), read_draws()))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    print(f"search-v0.10-check-ok: rows={len(read_rows())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
