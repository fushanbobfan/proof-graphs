#!/usr/bin/env python3
"""Search v0.7: the two searches with goals and states identified up to renaming, beside search-v0.6's two.

  python scripts/run_search_renaming.py --develop N [--budget B]
  python scripts/run_search_renaming.py --replay-check N
  python scripts/run_search_renaming.py --register
  python scripts/run_search_renaming.py --run [--workers 8]
  python scripts/run_search_renaming.py --check-committed

In search-v0.6, with BFS-Prover-V2-7B as the proposer and its draws shared, the AND-OR search proved 41 theorems
and the whole-state search 39, and four fifths of the goal sharing the whole-state search met was between goals
that differ only in the names of their hypotheses, which a search keyed on printed goals cannot merge. This
experiment adds the two searches of `search_renaming.py`: a whole-state search that drops states alike up to
renaming (LEAN-GitHub's deduplication), and an AND-OR search that merges goals alike up to renaming behind a
verified renaming step. With search-v0.6's two searches they form a two-by-two design: states or goals, printed or
up to renaming.

All four run on the holdout slice's 200 tasks with the draws shared, and seeded with search-v0.6's: the n-th time
a search expands a goal it gets the n-th set drawn for that goal in the task, the sets search-v0.6 drew first, then
new ones, drawn by whichever search needs them first. Draws are independent samples, so a set drawn earlier is
distributed as one drawn now, and search-v0.6's two searches, run again, replay it exactly if Lean does: no new
draw, the same outcome. That replay is a registered check, and it makes the renaming searches' comparison with
search-v0.6's paired under the same draws. Each unit is one task: the two replays, then the two renaming searches
in an order that alternates from task to task, each in a fresh REPL.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common_draws  # noqa: E402
import run_holdout as holdout  # noqa: E402
import run_search_keys as rsk  # noqa: E402
import run_search_paired as v6  # noqa: E402
import search_harness as harness  # noqa: E402
import search_keys as keys  # noqa: E402
import search_renaming as renamed  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402
from search_harness import State, canonical_goal  # noqa: E402

ROOT = holdout.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.7"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
SEED_DRAWS, SEED_RESULTS = v6.DRAWS, v6.RESULTS
IMPLEMENTATIONS = {
    "renaming": ROOT / "scripts" / "renaming.py", "searchRenaming": ROOT / "scripts" / "search_renaming.py",
    "draws": ROOT / "scripts" / "common_draws.py", "prover": ROOT / "scripts" / "step_prover.py",
    "keys": ROOT / "scripts" / "search_keys.py", "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py", "runner": Path(__file__).resolve(),
}
MODEL_PATH = v6.MODEL_PATH
SAMPLES, TEMPERATURE, MAX_TOKENS, BUDGET = v6.SAMPLES, v6.TEMPERATURE, v6.MAX_TOKENS, v6.BUDGET
REPLAYS = ("whole", "andor")
RENAMING = ("wholeRenamed", "andorRenamed")
SEARCHES = REPLAYS + RENAMING
FUNCTIONS: dict[str, Callable[..., dict[str, Any]]] = {
    "whole": keys.whole_state_search, "andor": keys.and_or_search,
    "wholeRenamed": renamed.whole_state_search, "andorRenamed": renamed.and_or_search}
COMPARISONS = {  # hypothesis: (the search predicted to prove more, the other)
    "H54": ("andorRenamed", "whole"), "H55": ("andorRenamed", "andor"),
    "H56": ("andorRenamed", "wholeRenamed"), "H57": ("wholeRenamed", "whole")}
WORDS = {"whole": "whole-state search", "andor": "AND-OR search",
         "wholeRenamed": "whole-state search up to renaming", "andorRenamed": "AND-OR search up to renaming"}
ALPHA = 0.05
KEYS = rsk.KEYS


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def search_order(task: dict[str, Any]) -> tuple[str, ...]:
    return REPLAYS + (RENAMING if task["index"] % 2 == 0 else RENAMING[::-1])


def draw_key(prompt: str) -> str:
    return canonical_goal(prompt[:-len(prover.SEPARATOR)])


def seeds_by_task() -> dict[int, dict[str, list[list[str]]]]:
    """search-v0.6's draws, per task and goal, in the order of their occurrences."""
    grouped: dict[int, dict[str, dict[int, list[str]]]] = {}
    for entry in v6.read_draws():
        sets = grouped.setdefault(entry["index"], {}).setdefault(draw_key(entry["prompt"]), {})
        assert entry["occurrence"] not in sets, "search-v0.6 drew a goal twice for one occurrence"
        sets[entry["occurrence"]] = entry["candidates"]
    out: dict[int, dict[str, list[list[str]]]] = {}
    for index, goals in grouped.items():
        for goal, sets in goals.items():
            assert sorted(sets) == list(range(len(sets))), "search-v0.6's occurrences of a goal are not contiguous"
            out.setdefault(index, {})[goal] = [sets[n] for n in range(len(sets))]
    return out


class SeededDraws(common_draws.CommonDraws):
    """`CommonDraws` whose sets start with search-v0.6's draws for the task; new sets are drawn as before."""

    def __init__(self, seeds: dict[str, list[list[str]]]) -> None:
        super().__init__(SAMPLES, TEMPERATURE, MAX_TOKENS, MODEL_PATH)
        self.sets = {goal: [list(c) for c in sets] for goal, sets in seeds.items()}
        self.seeded = {goal: len(sets) for goal, sets in seeds.items()}

    def proposer(self, search: str) -> Callable[[State], list[str]]:
        occurrences: dict[str, int] = {}
        counts = self.counts.setdefault(search, {"seeded": 0, "shared": 0, "drawn": 0})

        def propose(state: State) -> list[str]:
            if not state.goals:
                return []
            goal = state.goals[0]
            key = canonical_goal(goal)
            n = occurrences.get(key, 0)
            occurrences[key] = n + 1
            sets = self.sets.setdefault(key, [])
            if n < len(sets):
                counts["seeded" if n < self.seeded.get(key, 0) else "shared"] += 1
                return list(sets[n])
            assert n == len(sets), "a search needs its n-th draw of a goal only after its (n-1)-th"
            candidates, entry = self.draw(goal)
            sets.append(candidates)
            counts["drawn"] += 1
            self.log.append(entry | {"search": search, "occurrence": n})
            return list(candidates)
        return propose


def registration_payload(task_list: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.7",
        "question": "with a step-level prover as the proposer and its draws shared, does identifying goals up to the "
                    "names of their hypotheses make a search over goals prove more, and is any gain the goal "
                    "decomposition's or the renaming's",
        "tasks": {"source": "holdout-v0.1/tasks.json", "sourceSha256": sha256_file(holdout.TASKS),
                  "count": len(task_list), "note": "search-v0.6's 200 tasks; every hypothesis is tested on all of "
                                                   "them, and the two sets of search-v0.6 are reported apart"},
        "proposer": "as search-v0.5 and v0.6: BFS-Prover-V2-7B in Q8_0, the first goal pretty-printed and followed by "
                    f"':::', {SAMPLES} completions at temperature {TEMPERATURE}, at most {MAX_TOKENS} tokens each, "
                    "duplicates dropped in order, no menu",
        "draws": "shared by the four searches of a task and seeded with search-v0.6's: the n-th time a search expands "
                 "a goal (canonical_goal of the goal the proposer sees) it gets the n-th set of candidates for that "
                 "goal in this task, first the sets search-v0.6 drew, in their order, then sets drawn anew by "
                 "whichever search first needs them",
        "seedDraws": {"source": "search-v0.6/draws.jsonl.gz", "sha256": sha256_file(SEED_DRAWS)},
        "searches": {
            "names": "whole is the whole-state search, andor the AND-OR search, wholeRenamed the whole-state search "
                     "up to renaming, andorRenamed the AND-OR search up to renaming",
            "whole": "search-v0.6's whole-state search (search_keys.py), unchanged",
            "andor": "search-v0.6's AND-OR search (search_keys.py), unchanged",
            "wholeRenamed": "the whole-state search dropping a child state whose goals agree in order with those of a "
                            "state already generated up to renaming (coarse_goal), not only in print",
            "andorRenamed": "the AND-OR search merging a new goal into an earlier goal alike up to renaming "
                            "(coarse_goal) when a renaming step (rename' for accessible hypotheses, rename_i for "
                            "those printed with a dagger) turns it into that goal, as the REPL checks: the renamed "
                            "goal must print as the earlier one up to the names of the earlier one's inaccessible "
                            "hypotheses; the step precedes the earlier goal's proof in the script"},
        "execution": "each unit is one task: whole and andor, then wholeRenamed and andorRenamed, the latter two in "
                     "this order on tasks of even index and reversed on odd, each in a fresh REPL; the tasks "
                     "search-v0.5 did not run first; a unit that raises is recorded as four error rows and run "
                     "again, with the seeds and fresh new draws, on the next resume; every new draw is committed",
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "measures": {
            "proved": "tasks with a proof that re-verifies from the statement, per search",
            "expansionsToProof": "the expansion at which a search completed its proof",
            "merges": "andorRenamed: goals created by valid candidates, merged into an existing goal by print, merged "
                      "by a renaming (and how many of those print identically after it), renaming checks run and "
                      "refused",
            "renamedDuplicates": "wholeRenamed: child states dropped as duplicates up to renaming but not in print",
            "draws": "per search, the expansions that used a seeded set, a set another search drew here, or a new "
                     "draw"},
        "hypotheses": {
            name: f"over all tasks, the {WORDS[better]} proves more tasks than the {WORDS[other]} (one-sided sign "
                  f"test on the tasks proved by exactly one of them)"
            for name, (better, other) in COMPARISONS.items()} | {
            "H58": "in the AND-OR search up to renaming, over all tasks, more created goals are merged into an "
                   "existing goal by a renaming than by identical print"},
        "decisionRule": f"H54 to H57 are one family, decided by Holm's step-down procedure at family-wise alpha "
                        f"{ALPHA:g}; H58 is a count comparison",
        "power": "search-v0.6's searches proved about a quarter of the 169 statable tasks and differed on two, so "
                 "the discordant tasks of each comparison may be few and the tests have little power; decisions are "
                 "reported whichever way they come out",
        "checks": {"C8": "the whole and andor searches replay search-v0.6: on every task they reach the same outcome "
                         "(proved or not, and after the same number of expansions) and draw nothing new; proofs "
                         "found with a different script are counted, since the AND-OR search's choice between "
                         "proofs completing at once depends on string hashing",
                   "C9": "within a task, no goal has two sets for the same occurrence, seeded sets included"},
        "analyses": {"perSet": "the four counts on search-v0.6's test and replication sets",
                     "bootstrap": "95% percentile intervals of the whole-state duplicate fractions, resampling modules "
                                  "(2,000 resamples, seed 0)",
                     "expansionsToProof": "for each hypothesis's pair, among tasks both prove with different "
                                          "numbers of expansions, how often the first needs fewer"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": [
            "scripts/test_renaming.py: 11 cases of the renaming step on printed goals",
            "scripts/check_renaming_repl.py: 6 cases in a full-Mathlib REPL with a fixed proposer (rename', "
            "rename_i, no step, a swap, a merged goal behind pick_goal, and the whole-state search dropping two "
            "states alike up to renaming), every proof verified from the statement",
            "the four searches with the prover, outside the corpus: at 4 expansions on "
            "AddConstMapClass.map_const_add; at 16 expansions on the first 8 tasks of "
            "search-v0.3's list, stopped after 2 (AddConstMapClass.map_const_add and map_nsmul_add, which all four "
            "proved at the first expansion), then --develop 6 --budget 16 on six theorems of the first slice that "
            "neither of search-v0.3's menu searches proved, drawn with seed 7: all four proved the same three (at "
            "expansions 1, 4, and 1) and none proved the other three; the renaming AND-OR search merged 16 goals "
            "by a renaming on two of them (15 checks, none refused), the renaming whole-state search dropped 7 "
            "states, and no verifier rejected a proof",
            "--replay-check 6: the two replays on the first six stated tasks of the execution order reproduced "
            "search-v0.6's outcomes and scripts on all 12 units (eight of them 48-expansion searches without a "
            "proof) and drew nothing new"],
        "resultsSeenBeforeRegistration": "every earlier experiment, search-v0.6 in full, including its per-task "
                                         "outcomes, which the replays repeat; the development runs above; no "
                                         "renaming search had run on a corpus task",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run_one(task: dict[str, Any], search: str, propose: Callable[[State], list[str]],
            budget: int) -> dict[str, Any]:
    """One search on one task in a fresh REPL (search-v0.6's run_one, with the search function chosen here)."""
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            result = FUNCTIONS[search](repl, made.proof_state, [made.goal], propose, budget,
                                       verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_task(task: dict[str, Any], seeds: dict[str, list[list[str]]], budget: int = BUDGET,
             searches: tuple[str, ...] | None = None) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """The searches of one task with seeded shared draws: their rows, and the task's new draws."""
    draws = SeededDraws(seeds)
    rows = []
    for position, search in enumerate(searches or search_order(task)):
        row = run_one(task, search, draws.proposer(search), budget)
        rows.append(row | {"index": task["index"], "position": position,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"index": task["index"], "declaration": task["declaration"]} | entry for entry in draws.log]
    return rows, log


def unit_key(row: dict[str, Any]) -> tuple[str, str, str]:
    return row["module"], row["declaration"], row["search"]


def read_draws() -> list[dict[str, Any]]:
    if not DRAWS.exists():
        return []
    return [json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def write_draws(entries: list[dict[str, Any]], level: int) -> None:
    DRAWS.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries).encode("utf-8"),
                                    compresslevel=level, mtime=0))


def run_all(task_list: list[dict[str, Any]], workers: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    draws_log = read_draws()
    ok = {(r["declaration"], r["search"]) for r in rows if not r.get("error")}
    done = {t["declaration"] for t in task_list if all((t["declaration"], s) in ok for s in SEARCHES)}
    draws_log = [e for e in draws_log if e["declaration"] in done]  # a task being rerun keeps only its new draws
    seeds = seeds_by_task()
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            return run_task(task, seeds.get(task["index"], {}))
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s,
                     "index": task["index"], "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)} for s in SEARCHES], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        task_rows, task_draws = result
        with lock:
            rows.extend(task_rows)
            draws_log.extend(task_draws)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                for row in task_rows:
                    handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            write_draws(draws_log, 6)
            print(json.dumps({"task": task_rows[0]["declaration"], "index": task_rows[0]["index"],
                              "searches": {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                                         bool((r.get("result") or {}).get("proof")))
                                           for r in task_rows},
                              "draws": len(task_draws), "error": task_rows[0].get("error"),
                              "at": time.strftime("%H:%M:%S")}, ensure_ascii=False), flush=True)

    todo = [t for t in v6.execution_order(task_list) if t["declaration"] not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t) for t in todo]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    write_draws(draws_log, 9)
    latest = {unit_key(r): r for r in rows}
    return list(latest.values()), draws_log


def holm(pvalues: dict[str, float | None], alpha: float) -> dict[str, dict[str, Any]]:
    """Holm's step-down procedure over the whole family; a test without discordant tasks counts as p = 1."""
    tested = sorted((1.0 if p is None else p, name) for name, p in pvalues.items())
    out = {name: {"p": p, "adjusted": None, "rejected": False} for name, p in pvalues.items()}
    running = 0.0
    stopped = False
    for rank, (p, name) in enumerate(tested):
        adjusted = min(1.0, (len(tested) - rank) * p)
        running = max(running, adjusted)
        out[name]["adjusted"] = running
        if not stopped and p <= alpha / (len(tested) - rank):
            out[name]["rejected"] = True
        else:
            stopped = True
    return out


def outcome(unit: dict[str, Any] | None) -> tuple[bool, int] | None:
    """Proved or not, and after how many expansions. The AND-OR search of search_keys settles a goal's parents in
    the order of a Python set of strings, which hashing varies from process to process, so when two proofs of a
    goal complete at once the one it records, and so its script, can differ between runs; its outcome cannot."""
    if unit is None or "result" not in unit:
        return None
    result = unit["result"]
    return bool(result["proof"]), len(result["expansions"])


def set_summary(units: dict[str, list[dict[str, Any] | None]]) -> dict[str, Any]:
    ran = {s: [u for u in units[s] if u is not None and "result" in u] for s in SEARCHES}
    proof_at = {s: {u["declaration"]: len(u["result"]["expansions"]) for u in ran[s] if u["result"]["proof"]}
                for s in SEARCHES}
    pairs = {}
    for name, (first, second) in COMPARISONS.items():
        only_first = set(proof_at[first]) - set(proof_at[second])
        only_second = set(proof_at[second]) - set(proof_at[first])
        both = set(proof_at[first]) & set(proof_at[second])
        differing = [d for d in both if proof_at[first][d] != proof_at[second][d]]
        fewer = sum(1 for d in differing if proof_at[first][d] < proof_at[second][d])
        pairs[name] = {"first": first, "second": second, "firstOnly": len(only_first),
                       "secondOnly": len(only_second), "firstOnlyTasks": sorted(only_first),
                       "secondOnlyTasks": sorted(only_second), "both": len(both),
                       "signTestFirstMore": v6.sign_upper(len(only_first), len(only_first) + len(only_second)),
                       "signTestTwoSided": v6.sign_two_sided(len(only_first), len(only_first) + len(only_second)),
                       "expansionsToProof": {"differing": len(differing), "firstFewer": fewer,
                                             "signTestFirstFewer": v6.sign_upper(fewer, len(differing))}}
    merges = {k: sum(u["result"].get("merges", {}).get(k, 0) for u in ran["andorRenamed"])
              for k in ("arrivals", "new", "printed", "renamed", "renamedExact", "reused", "checks", "refused")}
    return {"tasks": len(units["whole"]),
            "stated": {s: sum(1 for u in units[s] if u is not None and u.get("constructed")) for s in SEARCHES},
            "abandoned": {s: sum(1 for u in units[s] if u is not None and u.get("abandoned")) for s in SEARCHES},
            "errors": {s: sum(1 for u in units[s] if u is not None and u.get("error")) for s in SEARCHES},
            "missing": {s: sum(1 for u in units[s] if u is None) for s in SEARCHES},
            "proved": {s: len(proof_at[s]) for s in SEARCHES},
            "provedTasks": {s: sorted(proof_at[s]) for s in SEARCHES},
            "expansions": {s: sum(len(u["result"]["expansions"]) for u in ran[s]) for s in SEARCHES},
            "seconds": {s: quantiles([float(u["result"]["seconds"]) for u in ran[s]]) for s in SEARCHES},
            "rejected": {s: sum(u["result"].get("rejected", 0) for u in ran[s]) for s in SEARCHES},
            "pairs": pairs, "merges": merges,
            "renamedDuplicates": sum(u["result"].get("renamedDuplicates", 0) for u in ran["wholeRenamed"]),
            "entangled": {s: sum(u["result"].get("entangled", 0) for u in ran[s]) for s in ("andor", "andorRenamed")},
            "draws": {s: {k: sum((u.get("draws") or {}).get(k, 0) for u in ran[s]) for k in ("seeded", "shared", "drawn")}
                      for s in SEARCHES}}


def replay_check(rows: list[dict[str, Any]], task_list: list[dict[str, Any]]) -> dict[str, Any]:
    """C8: the replays against search-v0.6's committed rows."""
    seed_rows = {v6.unit_key(r): r for r in (json.loads(l) for l in SEED_RESULTS.read_text(encoding="utf-8").splitlines()
                                             if l.strip())}
    by_unit = {unit_key(r): r for r in rows}
    compared = differing = drew = scripts = 0
    differences = []
    for task in task_list:
        for search in REPLAYS:
            unit = by_unit.get((task["module"], task["declaration"], search))
            now = outcome(unit)
            before = outcome(seed_rows.get((task["module"], task["declaration"], search)))
            if now is None and before is None:
                continue
            compared += 1
            if now != before:
                differing += 1
                differences.append({"declaration": task["declaration"], "search": search,
                                    "now": None if now is None else list(now),
                                    "before": None if before is None else list(before)})
            elif now is not None and now[0]:
                previous = seed_rows[(task["module"], task["declaration"], search)]["result"]["proof"]
                scripts += unit["result"]["proof"] != previous  # type: ignore[index]
            drew += unit is not None and (unit.get("draws") or {}).get("drawn", 0) > 0
    return {"compared": compared, "differing": differing, "unitsDrawingAnew": drew, "differences": differences,
            "provedWithAnotherScript": scripts, "holds": compared > 0 and differing == 0 and drew == 0}


def summarize(rows: list[dict[str, Any]], task_list: list[dict[str, Any]],
              draws_log: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {unit_key(r): r for r in rows}

    def units(subset: list[dict[str, Any]]) -> dict[str, list[dict[str, Any] | None]]:
        return {s: [by_unit.get((t["module"], t["declaration"], s)) for t in subset] for s in SEARCHES}

    everything = units(task_list)
    overall = set_summary(everything)
    per_set = {name: set_summary(units([t for t in task_list if (t["index"] >= v6.REPLICATION) == (name == "test")]))
               for name in ("test", "replication")}
    whole = {s: [u for u in everything[s] if u is not None and "result" in u] for s in ("whole", "wholeRenamed")}
    keyed = {s: {key: rsk.fractions(whole[s], key) | {"bootstrap": rsk.bootstrap(whole[s], key)} for key in KEYS}
             for s in whole}
    seeds = seeds_by_task()
    seen: set[tuple[int, str, int]] = {(index, goal, n) for index, goals in seeds.items()
                                       for goal, sets in goals.items() for n in range(len(sets))}
    repeats = 0
    for entry in draws_log:
        key = (entry["index"], draw_key(entry["prompt"]), entry["occurrence"])
        repeats += key in seen
        seen.add(key)
    seconds = [u["result"]["seconds"] for s in SEARCHES for u in everything[s] if u is not None and "result" in u]
    tests = holm({name: overall["pairs"][name]["signTestFirstMore"] for name in COMPARISONS}, ALPHA)
    merges = overall["merges"]
    out: dict[str, Any] = {
        "experiment": "search-v0.7", "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
        "overall": overall, "sets": per_set, "wholeKeys": keyed,
        "searchSeconds": quantiles([float(x) for x in seconds]),
        "C8": replay_check(rows, task_list),
        "C9": {"seeded": sum(len(sets) for goals in seeds.values() for sets in goals.values()),
               "drawn": len(draws_log), "repeated": repeats},
        "holm": tests,
    }
    out["hypotheses"] = {name: {"supported": tests[name]["rejected"]} for name in COMPARISONS} | {
        "H58": {"supported": merges["renamed"] > merges["printed"]}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(summary: dict[str, Any]) -> None:
    s = summary
    o = s["overall"]
    lines = ["# Goals and states up to renaming (search v0.7)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             f"Tasks: {o['tasks']}; stated: {o['stated']}; abandoned: {o['abandoned']}; errors: {o['errors']}.", "",
             "| Search | Proved | Expansions | Verifier rejections | Draws (seeded / shared / new) |",
             "| --- | ---: | ---: | ---: | --- |"]
    for search in SEARCHES:
        d = o["draws"][search]
        lines.append(f"| {search} | {o['proved'][search]} | {o['expansions'][search]} | {o['rejected'][search]} | "
                     f"{d['seeded']} / {d['shared']} / {d['drawn']} |")
    lines += ["", "| Hypothesis | Pair | First only | Second only | One-sided p | Holm-adjusted | Supported |",
              "| --- | --- | ---: | ---: | ---: | ---: | --- |"]
    for name in COMPARISONS:
        p, h = o["pairs"][name], s["holm"][name]
        lines.append(f"| {name} | {p['first']} > {p['second']} | {p['firstOnly']} | {p['secondOnly']} | "
                     f"{rsk.fmt(p['signTestFirstMore'], '.3g')} | {rsk.fmt(h['adjusted'], '.3g')} | "
                     f"{s['hypotheses'][name]['supported']} |")
    m = o["merges"]
    lines += ["", f"andorRenamed merges: {m['arrivals']} goals created; {m['printed']} merged by print, {m['renamed']} "
                  f"by a renaming ({m['renamedExact']} printing identically after it, {m['reused']} reusing a checked "
                  f"step); {m['checks']} checks, {m['refused']} refused; {m['new']} new goals. H58 supported: "
                  f"{s['hypotheses']['H58']['supported']}.",
              f"wholeRenamed: {o['renamedDuplicates']} child states dropped as duplicates up to renaming only.", "",
              "| Set | " + " | ".join(SEARCHES) + " |", "| --- |" + " ---: |" * len(SEARCHES)]
    for name, e in s["sets"].items():
        lines.append(f"| {name} ({e['stated']['whole']} stated) | " + " | ".join(str(e["proved"][x]) for x in SEARCHES)
                     + " |")
    c8 = s["C8"]
    lines += ["", f"C8 (replay of search-v0.6): {c8['compared']} units compared, {c8['differing']} differing, "
                  f"{c8['unitsDrawingAnew']} drawing anew; holds: {c8['holds']}.",
              f"C9: {s['C9']['repeated']} repeated occurrences among {s['C9']['seeded']} seeded and "
              f"{s['C9']['drawn']} new draws.", "", "## Duplicates (whole-state searches, all tasks)", "",
              "| Search | Key | Expansions | Order duplicates | Goal duplicates |", "| --- | --- | ---: | ---: | ---: |"]
    for search, table in s["wholeKeys"].items():
        for key in KEYS:
            f = table[key]
            lines.append(f"| {search} | {key} | {f['expansions']} | {f['orderDuplicates']} "
                         f"({rsk.fmt(f['orderFraction'], '.1%')}) | {f['goalDuplicates']} "
                         f"({rsk.fmt(f['goalFraction'], '.1%')}) |")
    lines += ["", "## Interpretation boundary", "",
              "One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the",
              "theorems of one Mathlib slice. Renaming is by position in the printed context and checked in print;",
              "goals equal up to definitional unfolding, or up to the names of bound variables, stay apart."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def develop(count: int, budget: int) -> int:
    """The four searches on `count` tasks of the first slice, outside the corpus, that neither of search-v0.3's
    menu searches proved (so that the searches run deep enough to meet renamed goals), drawn with seed 7."""
    if not prover.server_alive():
        raise SystemExit("no model server on 127.0.0.1:8080")
    prover.MODEL_LOG = None
    v3 = ROOT / "experiments" / "search-v0.3"
    proved: dict[str, bool] = {}
    for line in (v3 / "results.jsonl").read_text(encoding="utf-8").splitlines():
        row = json.loads(line) if line.strip() else {}
        if row.get("constructed") and "result" in row:
            proved[row["declaration"]] = proved.get(row["declaration"], False) or bool(row["result"]["proof"])
    corpus = {t["declaration"] for t in v6.tasks()}
    candidates = [t for t in json.loads((v3 / "tasks.json").read_text(encoding="utf-8"))
                  if t["declaration"] not in corpus and proved.get(t["declaration"]) is False]
    for index, task in enumerate(random.Random(7).sample(candidates, count)):
        task_rows, log = run_task(task | {"index": index}, {}, budget)
        for row in task_rows:
            result = row.get("result") or {}
            print(json.dumps({"task": task["declaration"], "search": row["search"], "draws": row["draws"],
                              "proof": result.get("proof"), "expansions": len(result.get("expansions", [])),
                              "rejected": result.get("rejected"), "merges": result.get("merges"),
                              "renamedDuplicates": result.get("renamedDuplicates")}, ensure_ascii=False), flush=True)
        print(json.dumps({"task": task["declaration"], "drawsLogged": len(log)}), flush=True)
    return 0


def replay_only(count: int) -> int:
    """The two replays on the first `count` stated tasks of the execution order, against search-v0.6."""
    seeds = seeds_by_task()
    seed_rows = [json.loads(l) for l in SEED_RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    stated = {r["declaration"] for r in seed_rows if r.get("constructed")}
    task_list = [t for t in v6.execution_order(v6.tasks()) if t["declaration"] in stated][:count]
    prover.MODEL_LOG = None
    rows = []
    for task in task_list:
        task_rows, log = run_task(task, seeds.get(task["index"], {}), searches=REPLAYS)
        rows += task_rows
        print(json.dumps({"task": task["declaration"], "newDraws": len(log),
                          "searches": {r["search"]: list(outcome(r) or [])[:2] for r in task_rows}}, ensure_ascii=False))
    print(json.dumps({"replayCheck": {k: v for k, v in replay_check(rows, task_list).items()}}, ensure_ascii=False))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--develop", type=int, metavar="N", help="the four searches on N tasks outside the corpus")
    mode.add_argument("--replay-check", type=int, metavar="N", help="the two replays on N corpus tasks")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--budget", type=int, default=4, help="with --develop")
    args = parser.parse_args()

    if args.develop:
        return develop(args.develop, args.budget)
    if args.replay_check:
        return replay_only(args.replay_check)

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload(v6.tasks())
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {payload['tasks']['count']} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["sourceSha256"] != sha256_file(holdout.TASKS):
        raise SystemExit("the holdout tasks changed since registration")
    if prereg["seedDraws"]["sha256"] != sha256_file(SEED_DRAWS):
        raise SystemExit("search-v0.6's draws changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("renaming", "searchRenaming", "draws", "prover", "keys", "harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    task_list = v6.tasks()

    if args.run:
        if not prover.server_alive():
            raise SystemExit("no model server on 127.0.0.1:8080")
        rows, draws_log = run_all(task_list, args.workers)
        order = {(t["module"], t["declaration"], s): i for i, (t, s) in
                 enumerate((t, s) for t in task_list for s in SEARCHES)}
        rows.sort(key=lambda r: order[unit_key(r)])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        draws_log.sort(key=lambda e: e["index"])
        write_draws(draws_log, 9)
        summary = summarize(rows, task_list, draws_log)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.7-run": summary["hypotheses"], "proved": summary["overall"]["proved"],
                          "C8": summary["C8"]["holds"]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()} \
            or summary["drawsSha256"] != sha256_file(DRAWS):
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, task_list, read_draws())
    for key in ("overall", "sets", "wholeKeys", "C8", "C9", "holm", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.7-check-ok: units={len(committed)} newDraws={summary['C9']['drawn']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
