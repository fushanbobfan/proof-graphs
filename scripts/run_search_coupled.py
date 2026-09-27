#!/usr/bin/env python3
"""Search v0.8: states, independent goals, and coupled goal groups, with goal identity from Lean's expressions,
over three sets of draws.

  python scripts/run_search_coupled.py --develop N [--budget B]
  python scripts/run_search_coupled.py --register
  python scripts/run_search_coupled.py --run [--workers 8]
  python scripts/run_search_coupled.py --check-committed

A review of search-v0.6 asked for three things this experiment does together. Goal identity is taken from Lean's
expressions, not printed text (`goal_identity`, `search_faithful`). A dependency-aware search joins the
whole-state and the independent-goal searches: it searches over groups of goals coupled by metavariables, so a
tactic that assigns a metavariable two goals share is kept rather than discarded (`search_faithful.coupled_search`).
And the comparison is repeated over three independent sets of the prover's draws, each shared by the three
searches of a task: the first seeded with search-v0.6's and v0.7's recorded draws, the other two drawn afresh.
Cost is reported beside proofs: draws, completion tokens, REPL calls and time by kind, and wall-clock time.

Each unit is one task in one set of draws: the three searches in turn, in an order that rotates with the task and
the set, each in a fresh REPL whose environment defines the export tactic once (`search_faithful.ExportingSession`).
The sets run one after another, so that the first complete set is usable if a later one is cut short.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import hashlib
import json
import math
import random
import sys
import threading
import time
import urllib.request
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common_draws  # noqa: E402
import run_holdout as holdout  # noqa: E402
import run_key_replay as keys_replay  # noqa: E402
import run_search_paired as v6  # noqa: E402
import run_search_renaming as v7  # noqa: E402
import search_faithful as sf  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402
from search_harness import State, canonical_goal  # noqa: E402

ROOT = v7.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.8"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "faithful": ROOT / "scripts" / "search_faithful.py", "identity": ROOT / "scripts" / "goal_identity.py",
    "renaming": ROOT / "scripts" / "renaming.py", "draws": ROOT / "scripts" / "common_draws.py",
    "prover": ROOT / "scripts" / "step_prover.py", "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py", "runner": Path(__file__).resolve(),
}
SAMPLES, TEMPERATURE, MAX_TOKENS, BUDGET, MODEL_PATH = v7.SAMPLES, v7.TEMPERATURE, v7.MAX_TOKENS, v7.BUDGET, v7.MODEL_PATH
REPLICATES = 3
SEARCHES = ("whole", "goals", "groups")
WORDS = {"whole": "whole-state search", "goals": "independent-goal search", "groups": "coupled-group search"}
FUNCTIONS: dict[str, Callable[..., dict[str, Any]]] = {
    "whole": sf.whole_state_search, "goals": sf.and_or_search, "groups": sf.coupled_search}
COMPARISONS = {"H64": ("groups", "goals"), "H65": ("groups", "whole"), "H66": ("goals", "whole")}
ALPHA = 0.05
BOOTSTRAP = 2000


def completion(prompt: str) -> dict[str, Any] | None:
    """One completion with its token counts (step_prover.one_completion's request, unchanged)."""
    body = {"model": MODEL_PATH, "prompt": prompt, "temperature": TEMPERATURE, "max_tokens": MAX_TOKENS,
            "n": 1, "stop": ["\n\n"]}
    request = urllib.request.Request(prover.ENDPOINT, data=json.dumps(body).encode("utf-8"),
                                     headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(request, timeout=180.0) as response:
            reply = json.loads(response.read().decode("utf-8"))
    except Exception:  # noqa: BLE001 - a failed completion is no candidate, as in step_prover
        return None
    usage = reply.get("usage") or {}
    return {"text": (reply.get("choices") or [{}])[0].get("text", ""),
            "prompt": usage.get("prompt_tokens"), "completion": usage.get("completion_tokens")}


class ReplicateDraws(common_draws.CommonDraws):
    """The draws of one task in one set: shared by its three searches, the first set seeded with the recorded
    draws of search-v0.6 and v0.7. Each new draw is made as before (16 concurrent single completions of the first
    goal followed by ':::', first line of each, duplicates dropped in order) and logged with its token counts."""

    def __init__(self, seeds: dict[str, list[list[str]]]) -> None:
        super().__init__(SAMPLES, TEMPERATURE, MAX_TOKENS, MODEL_PATH)
        self.sets = {goal: [list(c) for c in s] for goal, s in seeds.items()}
        self.seeded = {goal: len(s) for goal, s in seeds.items()}

    def draw(self, goal: str) -> tuple[list[str], dict[str, Any]]:
        prompt = goal.rstrip() + prover.SEPARATOR
        started = time.monotonic()
        with concurrent.futures.ThreadPoolExecutor(max_workers=SAMPLES) as pool:
            replies = [r for r in pool.map(lambda _: completion(prompt), range(SAMPLES)) if r is not None]
        candidates: list[str] = []
        for reply in replies:
            tactic = prover.tactic_of(reply["text"], prompt)
            if tactic is not None and tactic not in candidates:
                candidates.append(tactic)
        return candidates, {"prompt": prompt, "replies": [r["text"] for r in replies], "candidates": candidates,
                            "promptTokens": sum(r["prompt"] or 0 for r in replies),
                            "completionTokens": sum(r["completion"] or 0 for r in replies),
                            "seconds": round(time.monotonic() - started, 2)}

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
                source = "seeded" if n < self.seeded.get(key, 0) else "shared"
                candidates = list(sets[n])
            else:
                assert n == len(sets), "a search needs its n-th draw of a goal only after its (n-1)-th"
                candidates, entry = self.draw(goal)
                sets.append(candidates)
                source = "drawn"
                self.log.append(entry | {"search": search, "occurrence": n})
            counts[source] += 1
            propose.last = {"goal": hashlib.sha256(key.encode("utf-8")).hexdigest()[:16], "n": n,  # type: ignore
                            "source": source}
            return candidates
        return propose


def search_order(index: int, replicate: int) -> tuple[str, ...]:
    shift = (index + replicate) % len(SEARCHES)
    return SEARCHES[shift:] + SEARCHES[:shift]


def units() -> list[tuple[int, dict[str, Any]]]:
    order = v6.execution_order(v6.tasks())
    return [(r, t) for r in range(REPLICATES) for t in order]


def run_one(task: dict[str, Any], search: str, propose: Callable[[State], list[str]], budget: int) -> dict[str, Any]:
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = sf.CountingRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = sf.ExportingSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            result = FUNCTIONS[search](repl, made.proof_state, [made.goal], propose, budget,
                                       verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result, "fastExport": getattr(repl, "fast_export", False),
                           "costs": repl.cost_summary(),
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout", "costs": repl.cost_summary(),
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_unit(replicate: int, task: dict[str, Any], seeds: dict[str, list[list[str]]],
             budget: int = BUDGET) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    draws = ReplicateDraws(seeds)
    rows = []
    for position, search in enumerate(search_order(task["index"], replicate)):
        row = run_one(task, search, draws.proposer(search), budget)
        rows.append(row | {"replicate": replicate, "index": task["index"], "position": position,
                           "draws": dict(draws.counts.get(search, {"seeded": 0, "shared": 0, "drawn": 0}))})
    log = [{"replicate": replicate, "index": task["index"], "declaration": task["declaration"]} | e for e in draws.log]
    return rows, log


def unit_key(row: dict[str, Any]) -> tuple[int, str, str, str]:
    return row["replicate"], row["module"], row["declaration"], row["search"]


def read_draws() -> list[dict[str, Any]]:
    if not DRAWS.exists():
        return []
    return [json.loads(l) for l in gzip.decompress(DRAWS.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def write_draws(entries: list[dict[str, Any]], level: int) -> None:
    DRAWS.write_bytes(gzip.compress("".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries).encode("utf-8"),
                                    compresslevel=level, mtime=0))


def run_all(workers: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    draws_log = read_draws()
    latest: dict[tuple[int, str, str], dict[str, Any]] = {}
    attempts: dict[tuple[int, str, str], int] = {}
    for r in rows:
        key = (r["replicate"], r["declaration"], r["search"])
        latest[key] = r
        attempts[key] = attempts.get(key, 0) + 1
    # Amendment 1: a search not constructed for a reason other than a missing declaration range, or abandoned by a
    # REPL timeout, is an infrastructure failure; its unit runs once more on resume, like a unit that raised.
    ok = {key for key, r in latest.items() if not r.get("error")
          and (attempts[key] > 1 or not (r.get("abandoned") or (r.get("constructed") is False and not r.get("reason"))))}
    done = {(r, t["declaration"]) for r, t in units() if all((r, t["declaration"], s) in ok for s in SEARCHES)}
    draws_log = [e for e in draws_log if (e["replicate"], e["declaration"]) in done]
    seeds = keys_replay.recorded_draws()
    lock = threading.Lock()
    prover.MODEL_LOG = None

    def guarded(replicate: int, task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            return run_unit(replicate, task, seeds.get(task["index"], {}) if replicate == 0 else {})
        except Exception as error:  # noqa: BLE001
            message = f"{type(error).__name__}: {error}"[:300]
            return [{"module": task["module"], "declaration": task["declaration"], "search": s, "replicate": replicate,
                     "index": task["index"], "constructed": None, "error": message,
                     "seconds": round(time.monotonic() - started, 1)} for s in SEARCHES], []

    def record(result: tuple[list[dict[str, Any]], list[dict[str, Any]]]) -> None:
        unit_rows, unit_draws = result
        with lock:
            rows.extend(unit_rows)
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
    write_draws(draws_log, 9)
    latest = {unit_key(r): r for r in rows}
    return list(latest.values()), draws_log


# ---------------------------------------------------------------- summary


def sign_upper(k: int, n: int) -> float | None:
    return None if n == 0 else sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def holm(pvalues: dict[str, float | None], alpha: float) -> dict[str, dict[str, Any]]:
    tested = sorted((1.0 if p is None else p, name) for name, p in pvalues.items())
    out = {name: {"p": p, "adjusted": None, "rejected": False} for name, p in pvalues.items()}
    running, stopped = 0.0, False
    for rank, (p, name) in enumerate(tested):
        running = max(running, min(1.0, (len(tested) - rank) * p))
        out[name]["adjusted"] = running
        if not stopped and p <= alpha / (len(tested) - rank):
            out[name]["rejected"] = True
        else:
            stopped = True
    return out


def summarize(rows: list[dict[str, Any]], draws_log: list[dict[str, Any]]) -> dict[str, Any]:
    task_list = v6.tasks()
    module_of = {t["declaration"]: t["module"] for t in task_list}
    by_unit = {unit_key(r): r for r in rows}
    replicates_run = sorted({r["replicate"] for r in rows})

    def unit(r: int, task: dict[str, Any], s: str) -> dict[str, Any] | None:
        return by_unit.get((r, task["module"], task["declaration"], s))

    stated = [t for t in task_list if all((u := unit(r, t, s)) is not None and u.get("constructed")
                                           for r in replicates_run for s in SEARCHES)]
    proved = {s: {r: sorted(t["declaration"] for t in stated if (unit(r, t, s) or {}).get("result", {}).get("proof"))
                  for r in replicates_run} for s in SEARCHES}
    counts = {s: {t["declaration"]: sum(t["declaration"] in proved[s][r] for r in replicates_run) for t in stated}
              for s in SEARCHES}
    pairs: dict[str, Any] = {}
    rng = random.Random(0)
    modules = sorted({module_of[t["declaration"]] for t in stated})
    by_module: dict[str, list[str]] = {}
    for t in stated:
        by_module.setdefault(module_of[t["declaration"]], []).append(t["declaration"])
    for name, (first, second) in COMPARISONS.items():
        d = {t: counts[first][t] - counts[second][t] for t in counts[first]}
        higher = sum(1 for v in d.values() if v > 0)
        lower = sum(1 for v in d.values() if v < 0)
        draws_ = []
        for _ in range(BOOTSTRAP):
            chosen = [x for m in (rng.choice(modules) for _ in modules) for x in by_module[m]]
            draws_.append(sum(d[x] for x in chosen) / (len(chosen) * max(1, len(replicates_run))))
        draws_.sort()
        pairs[name] = {"first": first, "second": second, "tasksFirstMore": higher, "tasksSecondMore": lower,
                       "signTestFirstMore": sign_upper(higher, higher + lower),
                       "meanRateDifference": round(sum(d.values()) / (len(d) * max(1, len(replicates_run))), 6)
                       if d else None,
                       "interval95": [round(draws_[int(0.025 * BOOTSTRAP)], 6),
                                      round(draws_[int(0.975 * BOOTSTRAP) - 1], 6)] if d else None,
                       "perReplicate": {r: {"firstOnly": len(set(proved[first][r]) - set(proved[second][r])),
                                            "secondOnly": len(set(proved[second][r]) - set(proved[first][r]))}
                                        for r in replicates_run}}
    tests = holm({name: pairs[name]["signTestFirstMore"] for name in COMPARISONS}, ALPHA)
    ran = {s: [u for (r, _, _, s2), u in by_unit.items() if s2 == s and "result" in u] for s in SEARCHES}
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
    whole = ran["whole"]
    flags = [(e["orderDuplicate"], e["goalDuplicate"]) for u in whole for e in u["result"]["expansions"]
             if e["orderDuplicate"] is not None]
    mechanisms = {
        "goalsEntangled": sum(u["result"]["entangled"] for u in ran["goals"]),
        "groupsOutside": sum(u["result"]["outside"] for u in ran["groups"]),
        "groupsMade": {k: sum(u["result"]["groups"][k] for u in ran["groups"]) for k in ("single", "several")},
        "proofsThroughGroups": sum(1 for u in ran["groups"] if u["result"]["proof"] and u["result"]["groupsInProof"]),
        "wholeFaithfulOrder": sum(1 for o, _ in flags if o), "wholeFaithfulGoal": sum(1 for _, g in flags if g),
        "wholeFlagged": len(flags),
        "wholeProofsWithFreshDraws": sum(1 for u in whole if u["result"]["proof"] and any(
            d is not None and d.get("n", 0) >= 1 for d in u["result"].get("proofDraws", []))),
        "merges": {s: {k: sum(u["result"]["merges"][k] for u in ran[s]) for k in
                       ("arrivals", "new", "identical", "renamed", "reused", "checks", "refused")}
                   for s in ("goals", "groups")}}
    seen: set[tuple[int, int, str, int]] = set()
    repeats = 0
    for entry in draws_log:
        key = (entry["replicate"], entry["index"], v7.draw_key(entry["prompt"]), entry["occurrence"])
        repeats += key in seen
        seen.add(key)
    constructed = [u for s in SEARCHES for u in ran[s]]
    out: dict[str, Any] = {
        "experiment": "search-v0.8", "preregistrationSha256": sha256_file(PREREG), "replicates": replicates_run,
        "stated": len(stated), "tasks": len(task_list),
        "proved": {s: {r: len(v) for r, v in proved[s].items()} for s in SEARCHES}, "provedTasks": proved,
        "pooled": {s: sum(counts[s].values()) for s in SEARCHES}, "pairs": pairs, "holm": tests,
        "costs": costs, "mechanisms": mechanisms,
        "errors": sum(1 for r in rows if r.get("error")), "abandoned": sum(1 for r in rows if r.get("abandoned")),
        "C13": {"draws": len(draws_log), "repeated": repeats, "holds": repeats == 0},
        "C14": {"units": len(constructed), "fastExport": sum(1 for u in constructed if u.get("fastExport")),
                "holds": bool(constructed) and sum(1 for u in constructed if u.get("fastExport"))
                >= 0.99 * len(constructed)},
    }
    out["hypotheses"] = {name: {"supported": tests[name]["rejected"]} for name in COMPARISONS}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(s: dict[str, Any]) -> None:
    lines = ["# States, goals, and coupled groups over three sets of draws (search v0.8)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             f"Tasks: {s['tasks']}; stated in every set: {s['stated']}; errors: {s['errors']}; abandoned: "
             f"{s['abandoned']}.", "", "| Search | " + " | ".join(f"set {r}" for r in s["replicates"])
             + " | pooled (task-sets) |", "| --- |" + " ---: |" * (len(s["replicates"]) + 1)]
    for search in SEARCHES:
        lines.append(f"| {search} | " + " | ".join(str(s["proved"][search][r]) for r in s["replicates"])
                     + f" | {s['pooled'][search]} |")
    lines += ["", "| Hypothesis | Pair | Tasks first more | Tasks second more | One-sided p | Holm | Rate difference "
                  "(95% interval) | Supported |", "| --- | --- | ---: | ---: | ---: | ---: | --- | --- |"]
    for name in COMPARISONS:
        p, h = s["pairs"][name], s["holm"][name]
        lines.append(f"| {name} | {p['first']} > {p['second']} | {p['tasksFirstMore']} | {p['tasksSecondMore']} | "
                     f"{p['signTestFirstMore']} | {h['adjusted']} | {p['meanRateDifference']} {p['interval95']} | "
                     f"{s['hypotheses'][name]['supported']} |")
    lines += ["", "## Cost", "", "| Search | Expansions | Draws (seeded / shared / new) | Completion tokens | REPL "
                                   "calls (tactic / export / harness) | Median search seconds |",
              "| --- | ---: | --- | ---: | --- | ---: |"]
    for search in SEARCHES:
        c = s["costs"][search]
        d, r = c["draws"], c["repl"]
        lines.append(f"| {search} | {c['expansions']} | {d['seeded']} / {d['shared']} / {d['drawn']} | "
                     f"{c['completionTokens']} | {r['tactic']['calls']} / {r['export']['calls']} / "
                     f"{r['harness']['calls']} | {(c['searchSeconds'] or {}).get('median')} |")
    m = s["mechanisms"]
    lines += ["", f"Mechanisms: independent-goal candidates discarded as entangled {m['goalsEntangled']}; coupled-group "
                  f"candidates discarded as coupled outside their group {m['groupsOutside']}; groups of several goals "
                  f"made {m['groupsMade']['several']}, proofs through one {m['proofsThroughGroups']}; whole-state "
                  f"proofs using a goal's later draw {m['wholeProofsWithFreshDraws']}.",
              f"C13: {s['C13']['repeated']} repeated occurrences among {s['C13']['draws']} new draws. C14: fast "
              f"export in {s['C14']['fastExport']} of {s['C14']['units']} searches.", "", "## Interpretation boundary",
              "", "One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the",
              "theorems of one Mathlib slice. Identity is syntactic on instantiated Lean expressions; goals equal up",
              "to definitional unfolding stay apart."]
    write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration and entry points


def registration_payload() -> dict[str, Any]:
    return {
        "experiment": "search-v0.8",
        "question": "with goal identity taken from Lean's expressions and the prover's draws repeated three times, "
                    "does a search over metavariable-coupled goal groups prove more than a search over independent "
                    "goals or over whole states",
        "tasks": {"source": "holdout-v0.1/tasks.json", "sourceSha256": sha256_file(holdout.TASKS), "count": 200},
        "proposer": f"as search-v0.5 to v0.7: BFS-Prover-V2-7B in Q8_0, {SAMPLES} completions at temperature "
                    f"{TEMPERATURE}, at most {MAX_TOKENS} tokens, the first goal followed by ':::', duplicates dropped",
        "replicates": {"count": REPLICATES,
                       "0": "seeded with search-v0.6's and search-v0.7's recorded draws (7,731 sets), extended with new "
                            "draws by whichever search needs them first",
                       "1-2": "drawn afresh",
                       "sharing": "within a set, the draws of a task are shared by its three searches as in "
                                  "search-v0.6 (the n-th expansion of a printed goal gets the n-th set drawn for it)",
                       "seedSources": {"searchV06Draws": sha256_file(v7.SEED_DRAWS),
                                       "searchV07Draws": sha256_file(v7.DRAWS)}},
        "searches": {"whole": "search_faithful.whole_state_search: whole states, dropped when their faithful state "
                              "key was generated before",
                     "goals": "search_faithful.and_or_search: single goals merged by faithful goal key, behind a "
                              "renaming step when hypothesis names differ; entangled candidates discarded",
                     "groups": "search_faithful.coupled_search: groups of goals coupled by metavariables; a candidate "
                               "that changes a goal of its own group is kept; a one-goal group merged as in goals, a "
                               "larger one only if it prints identically"},
        "identity": "goal_identity.py's export, defined once per task environment as the tactic pg_export_goals "
                    "(search_faithful.ExportingSession), the run_tac block where the definition fails",
        "execution": "a unit is one task in one set: the three searches in turn, the order rotating with the task "
                     "index plus the set, each in a fresh REPL; the sets run in order; a unit that raises is recorded "
                     "as three error rows and run again, with fresh new draws, on the next resume",
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "measures": {"proved": "tasks with a proof that re-verifies from the statement, per search and set",
                     "perTaskCounts": "for each task, the number of sets in which a search proves it",
                     "cost": "expansions, draws (seeded, shared, new) and their tokens, REPL calls and seconds by "
                             "kind (candidate tactics, exports, harness steps, commands), search seconds",
                     "mechanisms": "entangled discards (goals), outside-coupled discards and groups of several goals "
                                   "made and used in proofs (groups), faithful duplicate shares and proofs through a "
                                   "goal's later draw (whole)"},
        "hypotheses": {name: f"over the tasks stated in every set, the {WORDS[a]} proves more tasks than the "
                             f"{WORDS[b]}: per task, the number of sets in which each proves it; one-sided sign test "
                             f"on the tasks where the numbers differ"
                       for name, (a, b) in COMPARISONS.items()},
        "decisionRule": f"H64 to H66 are one family, decided by Holm's step-down procedure at family-wise alpha {ALPHA:g}",
        "analyses": {"interval": "95% percentile interval of the mean per-task difference in proof rate, resampling "
                                 f"modules ({BOOTSTRAP:,} resamples, seed 0)",
                     "perSet": "each set's counts and discordant tasks"},
        "power": "earlier experiments found few discordant tasks between search designs; three sets give each task "
                 "0 to 3 proofs per search, and the test counts tasks, not task-sets",
        "checks": {"C13": "within a set and task, no goal has two new draws for one occurrence",
                   "C14": "at least 99% of the searches export through the defined tactic"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": [
            "scripts/check_faithful_repl.py: 6 cases in a Mathlib REPL with a fixed proposer: the coupled-group "
            "search proves a theorem whose two goals share a witness (refine, exact 2, rfl), which the "
            "independent-goal search cannot, discarding 2 entangled candidates, and the whole-state search proves "
            "it; goals alike up to bound names and up to hypothesis names are merged; a renamed state is dropped; "
            "every proof verified from the statement",
            "--develop 3 --budget 16: the three searches with the prover in one fresh set of draws on the first "
            "three of search-v0.7's development theorems (outside the corpus; seed 7): all three proved "
            "RCLike.conj_mul (at expansion 1) and FirstOrder.Language.Formula.realize_rel₂ (at 4) and not "
            "ContMDiffAt.iff_comp_isImmersionAtOfComplement; every search exported through the defined tactic with "
            "no failure; no group of several goals arose",
            "measured before registration: the draw throughput of concurrent single completions (840 draws an hour "
            "with 8 draws in flight) against sequential completions of one prompt (537 to 634), which kept the "
            "concurrent requests; and an export's cost as a run_tac block (about 0.5 s) against the defined tactic "
            "(2 to 3 ms)"],
        "resultsSeenBeforeRegistration": "every earlier experiment, including search-v0.7 in full; keys-v0.1 was "
                                         "running and its results had not been read",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def develop(count: int, budget: int) -> int:
    """The three searches with the prover on hard theorems of the first slice outside the corpus (seed 7, as
    search-v0.7's development), in one fresh set of draws."""
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
        rows, log = run_unit(0, task | {"index": index}, {}, budget)
        for row in rows:
            result = row.get("result") or {}
            print(json.dumps({"task": task["declaration"][:40], "search": row["search"], "draws": row["draws"],
                              "proof": result.get("proof"), "expansions": len(result.get("expansions", [])),
                              "costs": row.get("costs"), "fast": row.get("fastExport"),
                              "extra": {k: result.get(k) for k in ("entangled", "outside", "groups", "groupsInProof",
                                                                   "merges", "exportFailures", "rejected")}},
                             ensure_ascii=False), flush=True)
        print(json.dumps({"task": task["declaration"], "drawsLogged": len(log),
                          "tokens": sum(e["completionTokens"] for e in log)}), flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--develop", type=int, metavar="N")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--budget", type=int, default=16, help="with --develop")
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
    for name in ("faithful", "identity", "renaming", "draws", "prover", "harness", "repl"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        if not prover.server_alive():
            raise SystemExit("no model server on 127.0.0.1:8080")
        rows, draws_log = run_all(args.workers)
        order = {(r, t["declaration"], s): i for i, (r, t, s) in
                 enumerate((r, t, s) for r, t in units() for s in SEARCHES)}
        rows.sort(key=lambda r: order.get((r["replicate"], r["declaration"], r["search"]), len(order)))
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        draws_log.sort(key=lambda e: (e["replicate"], e["index"]))
        write_draws(draws_log, 9)
        summary = summarize(rows, draws_log)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.8-run": summary["hypotheses"], "proved": summary["proved"]}))
        return 0
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["drawsSha256"] != sha256_file(DRAWS):
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = json.loads(json.dumps(summarize(committed, read_draws())))
    for key in ("proved", "pooled", "pairs", "holm", "costs", "mechanisms", "C13", "C14", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.8-check-ok: units={len(committed)} newDraws={summary['C13']['draws']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
