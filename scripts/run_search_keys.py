#!/usr/bin/env python3
"""Search v0.4: how goal identity moves the duplicate measures, and a search without one-shot provers.

  python scripts/run_search_keys.py --develop
  python scripts/run_search_keys.py --register
  python scripts/run_search_keys.py --run [--workers 8]
  python scripts/run_search_keys.py --check-committed

Two arms on tasks drawn at random from search-v0.3's 1,347 candidate theorems:

- *keys*: the whole-state search of search-v0.3 (standard menu, 24 expansions) on 300 tasks, recording every
  expanded state's goals under the fine, default, and coarse keys of `search_keys.py`. The search itself
  deduplicates by the default key, as before, so it must reproduce search-v0.3 exactly (C5).
- *hammer-free*: both searches with the menu stripped of its one-shot provers, at 96 expansions, on the first 135
  of the same random order. The AND-OR search sets a goal's proof once (the fix described in `search_keys.py`).
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search as v1  # noqa: E402
import run_search_deep as v2  # noqa: E402
import search_harness as harness  # noqa: E402
import search_keys as keys  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.4"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
SOURCE = ROOT / "experiments" / "search-v0.3"
IMPLEMENTATIONS = {
    "keys": ROOT / "scripts" / "search_keys.py",
    "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py",
    "runner": Path(__file__).resolve(),
}
SEED = 20260926
KEY_TASKS = 300
HAMMER_FREE_TASKS = 135
ARMS = {"keys": {"menu": "standard", "searches": ("whole",), "budget": 24, "tasks": KEY_TASKS},
        "hammerFree": {"menu": "hammer-free", "searches": ("whole", "andor"), "budget": 96,
                       "tasks": HAMMER_FREE_TASKS}}
KEYS = ("fine", "default", "coarse")
SHARING_RATIO = 2.0
FINE_SHARE = 0.8
ALPHA = 0.05
BOOTSTRAP = 2000
CHECK_BUDGET = 4


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def draw_tasks() -> list[dict[str, Any]]:
    """search-v0.3's candidates in a seeded random order; the first KEY_TASKS are the keys arm's tasks and the
    first HAMMER_FREE_TASKS of those the hammer-free arm's."""
    candidates = json.loads((SOURCE / "tasks.json").read_text(encoding="utf-8"))
    order = list(range(len(candidates)))
    random.Random(SEED).shuffle(order)
    return [candidates[i] | {"draw": rank} for rank, i in enumerate(order[:KEY_TASKS])]


def units(tasks: list[dict[str, Any]]) -> list[tuple[dict[str, Any], str, str]]:
    return [(t, arm, s) for arm, spec in ARMS.items() for t in tasks[:spec["tasks"]] for s in spec["searches"]]


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.4",
        "questions": {
            "keys": "do the duplicate measures of search-v0.1 to v0.3 depend on how goals are identified: printed "
                    "text that hides implicit arguments, or text that keeps hypothesis names",
            "hammerFree": "when the menu has no one-shot prover, so that proofs take several steps and searches run "
                          "deep, does a search over goals prove more than a search over whole states"},
        "tasks": {"source": "search-v0.3/tasks.json", "sourceSha256": sha256_file(SOURCE / "tasks.json"),
                  "rule": f"the 1,347 candidates in a random order (Python random.Random({SEED}).shuffle of their "
                          f"indices); the first {KEY_TASKS} for the keys arm and the first {HAMMER_FREE_TASKS} of "
                          "those for the hammer-free arm",
                  "count": len(tasks)},
        "arms": {
            "keys": "the whole-state search of search-v0.3 with the standard 26-tactic menu at 24 expansions, "
                    "recording the keys of every expanded state's goals",
            "hammerFree": f"both searches with the menu without {', '.join(keys.HAMMERS)} "
                          f"({len(keys.MENU_HAMMER_FREE)} tactics: {', '.join(keys.MENU_HAMMER_FREE)}) at 96 "
                          "expansions, recording keys; the AND-OR search sets a goal's proof once"},
        "keys": {"fine": "the goal printed with pp.all (set_option pp.all true in trace_state on the expanded state), "
                         "case tag removed and metavariable numbers erased",
                 "default": "the canonical goal of search-v0.1 to v0.3",
                 "coarse": "the canonical goal with its hypotheses renamed by position in the context",
                 "storage": "the first 16 hexadecimal digits of the SHA-256 of the key's text"},
        "budget": {"tacticWallClockSeconds": 60, "heartbeats": 40000},
        "execution": "every (arm, task, search) unit in a fresh REPL, resumable; an exception raised by a unit is "
                     "recorded as an error row and the unit is run again on the next resume",
        "measures": {
            "orderFraction[key]": "whole-state expansions whose goal multiset under the key was already expanded in "
                                  "another order, over the whole-state expansions whose keys are defined",
            "goalFraction[key]": "whole-state expansions whose first goal's key was already expanded as a first "
                                 "goal, over the same expansions",
            "fineUndefined": "expansions whose fine keys are undefined (the trace failed or did not split into the "
                             "state's goals)",
            "proved": "tasks with a proof that re-verifies from the statement, per search",
            "entangled": "candidates the AND-OR search discarded as entangled"},
        "hypotheses": {
            "H30": f"keys arm: under each of the three keys, the goal-duplicate fraction is at least "
                   f"{SHARING_RATIO:g} times the order-duplicate fraction",
            "H31": f"keys arm: the goal-duplicate fraction under the fine key is at least {FINE_SHARE:g} times the "
                   "goal-duplicate fraction under the default key",
            "H32": f"hammer-free arm: the AND-OR search proves more tasks than the whole-state search (one-sided "
                   f"sign test on the tasks proved by exactly one of them, alpha {ALPHA:g})",
            "H33": f"hammer-free arm: the whole-state search's goal-duplicate fraction under the default key is at "
                   f"least {SHARING_RATIO:g} times its order-duplicate fraction"},
        "checks": {"C5": "for every task of the keys arm, the whole-state search's expansion records (the fields of "
                         "search-v0.3) and proof equal those committed in search-v0.3",
                   "C6": "the default-key duplicate flags recomputed from the recorded digests equal the flags the "
                         "search computed from the texts"},
        "analyses": {
            "bootstrap": f"95% percentile intervals of every fraction by resampling modules with replacement "
                         f"({BOOTSTRAP} resamples, seed 0), since the tasks of one module share context",
            "perTask": "quartiles of the per-task number of goal duplicates, over tasks with at least one expansion",
            "coarseMerges": "hammer-free AND-OR expansions whose goal's coarse key equals that of a goal expanded "
                            "earlier in the same search (goals the search would merge under the coarse key)"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the runner's --develop mode ran both arms at 4 expansions on "
                                               "AddConstMapClass.map_const_add, the first candidate outside the "
                                               "sample, twice: the first time every fine key was undefined, because "
                                               "the REPL reports trace output in a field of its own rather than "
                                               "among the messages, which fine_goals then read; the trace was also "
                                               "inspected on that task's root state and on the two goals that "
                                               "constructor leaves in FirstOrder.Language.BoundedFormula.realize_ex, "
                                               "also outside the sample",
        "resultsSeenBeforeRegistration": "search-v0.3's results under the default key, which the keys arm "
                                         "replicates, as far as its run had progressed (its progress log, and the "
                                         "diagnosis of its one error row); no fine or coarse key and no "
                                         "hammer-free search had been computed on any task of the sample",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run_unit(task: dict[str, Any], arm: str, search: str, budget: int | None = None) -> dict[str, Any]:
    """One search on one task in a fresh REPL (as run_search_deep.run_unit, with the searches of search_keys)."""
    spec = ARMS[arm]
    budget = spec["budget"] if budget is None else budget
    head = {"module": task["module"], "declaration": task["declaration"], "arm": arm, "search": search}
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            proposer = keys.menu_proposer if spec["menu"] == "standard" else keys.hammer_free_proposer
            function = keys.whole_state_search if search == "whole" else keys.and_or_search
            result = function(repl, made.proof_state, [made.goal], proposer, budget,
                              verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def unit_key(row: dict[str, Any]) -> tuple[str, str, str, str]:
    return row["arm"], row["module"], row["declaration"], row["search"]


def run_all(tasks: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    done = {unit_key(r) for r in rows if not r.get("error")}
    lock = threading.Lock()

    def guarded(task: dict[str, Any], arm: str, search: str) -> dict[str, Any]:
        started = time.monotonic()
        try:
            return run_unit(task, arm, search)
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "arm": arm, "search": search,
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}

    def record(row: dict[str, Any]) -> None:
        with lock:
            rows.append(row)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["arm"], row["declaration"], row["search"]],
                              "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                              "abandoned": row.get("abandoned"), "error": row.get("error"),
                              "at": time.strftime("%H:%M:%S")}), flush=True)

    todo = [(t, a, s) for t, a, s in units(tasks) if (a, t["module"], t["declaration"], s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t, a, s) for t, a, s in todo]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    latest = {unit_key(r): r for r in rows}
    return list(latest.values())


def flags(expansions: list[dict[str, Any]], key: str) -> list[tuple[bool, bool] | None]:
    """Order- and goal-duplicate flags of each expansion under a key, as the search computes them for the default
    text; None where the expansion's keys under this key are undefined."""
    multisets: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    firsts: set[str] = set()
    out: list[tuple[bool, bool] | None] = []
    for e in expansions:
        digests = e["keys"][key]
        if digests is None:
            out.append(None)
            continue
        ordered = tuple(digests)
        multiset = tuple(sorted(ordered))
        order = multiset in multisets and ordered not in multisets[multiset]
        goal = (digests[0] if digests else "") in firsts
        multisets.setdefault(multiset, set()).add(ordered)
        firsts.add(digests[0] if digests else "")
        out.append((order, goal))
    return out


def fractions(units_: list[dict[str, Any]], key: str) -> dict[str, Any]:
    order = goal = defined = undefined = 0
    for u in units_:
        for f in flags(u["result"]["expansions"], key):
            if f is None:
                undefined += 1
                continue
            defined += 1
            order += f[0]
            goal += f[1]
    return {"expansions": defined, "undefined": undefined, "orderDuplicates": order, "goalDuplicates": goal,
            "orderFraction": order / defined if defined else None, "goalFraction": goal / defined if defined else None}


def bootstrap(units_: list[dict[str, Any]], key: str) -> dict[str, Any]:
    """Module-clustered percentile intervals of the order and goal fractions."""
    by_module: dict[str, list[tuple[int, int, int]]] = {}
    for u in units_:
        counts = [0, 0, 0]
        for f in flags(u["result"]["expansions"], key):
            if f is not None:
                counts[0] += 1
                counts[1] += f[0]
                counts[2] += f[1]
        by_module.setdefault(u["module"], []).append(tuple(counts))
    modules = sorted(by_module)
    if not modules:
        return {"order": None, "goal": None}
    rng = random.Random(0)
    order_draws, goal_draws = [], []
    for _ in range(BOOTSTRAP):
        total = [0, 0, 0]
        for m in (rng.choice(modules) for _ in modules):
            for c in by_module[m]:
                total = [a + b for a, b in zip(total, c)]
        if total[0]:
            order_draws.append(total[1] / total[0])
            goal_draws.append(total[2] / total[0])

    def interval(draws: list[float]) -> list[float] | None:
        if not draws:
            return None
        draws.sort()
        return [draws[int(0.025 * (len(draws) - 1))], draws[int(0.975 * (len(draws) - 1))]]
    return {"order": interval(order_draws), "goal": interval(goal_draws), "modules": len(modules)}


def sign_test_upper(k: int, n: int) -> float | None:
    if n == 0:
        return None
    return sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def replication(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """C5: the keys arm against search-v0.3's committed whole-state searches."""
    committed = {(r["module"], r["declaration"]): r for r in
                 (json.loads(l) for l in (SOURCE / "results.jsonl").read_text(encoding="utf-8").splitlines()
                  if l.strip()) if r["search"] == "whole" and "result" in r}
    compared, matched, mismatches = 0, 0, []
    for row in rows:
        if row["arm"] != "keys" or "result" not in row:
            continue
        old = committed.get((row["module"], row["declaration"]))
        if old is None:
            continue
        new_exp = [{k: e[k] for k in v2.WHOLE_KEYS} for e in row["result"]["expansions"]]
        old_exp = [{k: e[k] for k in v2.WHOLE_KEYS} for e in old["result"]["expansions"]]
        compared += 1
        if new_exp == old_exp and row["result"]["proof"] == old["result"]["proof"]:
            matched += 1
        else:
            mismatches.append({"declaration": row["declaration"]})
    return {"compared": compared, "matched": matched, "mismatches": mismatches}


def consistency(ran: list[dict[str, Any]]) -> dict[str, int]:
    """C6: the default-key flags from the digests against the search's own flags."""
    checked = differing = 0
    for u in ran:
        if u["search"] != "whole":
            continue
        for e, f in zip(u["result"]["expansions"], flags(u["result"]["expansions"], "default")):
            checked += 1
            differing += f != (e["orderDuplicate"], e["goalDuplicate"])
    return {"expansions": checked, "differing": differing}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {unit_key(r): r for r in rows}
    out: dict[str, Any] = {"experiment": "search-v0.4", "preregistrationSha256": sha256_file(PREREG),
                           "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()}}
    ran_all: list[dict[str, Any]] = []
    for arm, spec in ARMS.items():
        arm_tasks = tasks[:spec["tasks"]]
        units_ = {s: [by_unit.get((arm, t["module"], t["declaration"], s)) for t in arm_tasks]
                  for s in spec["searches"]}
        ran = {s: [u for u in units_[s] if u is not None and "result" in u] for s in spec["searches"]}
        ran_all += [u for s in ran.values() for u in s]
        entry: dict[str, Any] = {
            "tasks": len(arm_tasks),
            "constructed": {s: sum(1 for u in units_[s] if u is not None and u.get("constructed")) for s in units_},
            "abandoned": {s: sum(1 for u in units_[s] if u is not None and u.get("abandoned")) for s in units_},
            "errors": {s: sum(1 for u in units_[s] if u is not None and u.get("error")) for s in units_},
            "missing": {s: sum(1 for u in units_[s] if u is None) for s in units_}}
        whole = ran["whole"]
        entry["whole"] = {key: fractions(whole, key) | {"bootstrap": bootstrap(whole, key)} for key in KEYS}
        per_task = [sum(1 for f in flags(u["result"]["expansions"], "default") if f and f[1])
                    for u in whole if u["result"]["expansions"]]
        entry["perTaskGoalDuplicates"] = quantiles([float(x) for x in per_task])
        entry["proved"] = {s: sorted(u["declaration"] for u in ran[s] if u["result"]["proof"]) for s in ran}
        if "andor" in ran:
            andor = ran["andor"]
            coarse_merges = 0
            for u in andor:
                seen: set[str] = set()
                for e in u["result"]["expansions"]:
                    digest_ = (e["keys"]["coarse"] or [None])[0]
                    coarse_merges += digest_ in seen
                    seen.add(digest_)
            proved_whole, proved_andor = set(entry["proved"]["whole"]), set(entry["proved"]["andor"])
            whole_only, andor_only = proved_whole - proved_andor, proved_andor - proved_whole
            entry["andor"] = {"expansions": sum(len(u["result"]["expansions"]) for u in andor),
                              "entangled": sum(u["result"].get("entangled", 0) for u in andor),
                              "coarseMerges": coarse_merges}
            entry["discordant"] = {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                                   "signTestAndorMore": sign_test_upper(len(andor_only),
                                                                        len(whole_only) + len(andor_only))}
        entry["frontierExhausted"] = {s: sum(1 for u in ran[s] if not u["result"]["proof"]
                                             and len(u["result"]["expansions"]) < spec["budget"]) for s in ran}
        out[arm] = entry
    k, h = out["keys"]["whole"], out["hammerFree"]
    p32 = h["discordant"]["signTestAndorMore"]
    out["hypotheses"] = {
        "H30": {"supported": all(k[key]["orderFraction"] is not None and
                                 k[key]["goalFraction"] >= SHARING_RATIO * k[key]["orderFraction"] for key in KEYS)},
        "H31": {"supported": k["fine"]["goalFraction"] is not None and k["default"]["goalFraction"] is not None
                and k["fine"]["goalFraction"] >= FINE_SHARE * k["default"]["goalFraction"]},
        "H32": {"supported": p32 is not None and p32 < ALPHA},
        "H33": {"supported": h["whole"]["default"]["orderFraction"] is not None and
                h["whole"]["default"]["goalFraction"] >= SHARING_RATIO * h["whole"]["default"]["orderFraction"]}}
    out["C5"] = replication(rows)
    out["C6"] = consistency(ran_all)
    out["resultsSha256"] = sha256_file(RESULTS)
    return out


def fmt(x: float | None, pattern: str) -> str:
    return "n/a" if x is None else format(x, pattern)


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Goal identity and a search without one-shot provers (search v0.4)", "",
             "Definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", ""]
    for arm, title in (("keys", "Keys arm: standard menu, whole-state search, 24 expansions"),
                       ("hammerFree", "Hammer-free arm: 96 expansions")):
        a = summary[arm]
        lines += [f"## {title}", "",
                  f"Tasks: {a['tasks']}; stated: {a['constructed']}; abandoned: {a['abandoned']}; errors: "
                  f"{a['errors']}.", "",
                  "| Key | Expansions | Undefined | Order duplicates | 95% interval | Goal duplicates | 95% interval |",
                  "| --- | ---: | ---: | ---: | --- | ---: | --- |"]
        for key in KEYS:
            f = a["whole"][key]
            b = f["bootstrap"]
            interval = lambda i: "n/a" if i is None else f"{i[0]:.1%} to {i[1]:.1%}"  # noqa: E731
            lines.append(f"| {key} | {f['expansions']} | {f['undefined']} | {f['orderDuplicates']} "
                         f"({fmt(f['orderFraction'], '.1%')}) | {interval(b['order'])} | {f['goalDuplicates']} "
                         f"({fmt(f['goalFraction'], '.1%')}) | {interval(b['goal'])} |")
        lines += ["", "Proved: " + ", ".join(f"{s} {len(v)}" for s, v in a["proved"].items()) + "."]
        if "discordant" in a:
            d = a["discordant"]
            lines += [f"Proved by the whole-state search only: {d['wholeOnly']}; by the AND-OR search only: "
                      f"{d['andorOnly']} (one-sided sign test p = {fmt(d['signTestAndorMore'], '.3g')}). "
                      f"Entangled candidates: {a['andor']['entangled']}; AND-OR expansions of a goal equal under "
                      f"the coarse key to an earlier one: {a['andor']['coarseMerges']}."]
        lines += [f"Searches that exhausted their frontier without a proof: {a['frontierExhausted']}.", ""]
    h, c5, c6 = summary["hypotheses"], summary["C5"], summary["C6"]
    lines += ["## Hypotheses", ""] + [f"- {k}: supported: {v['supported']}." for k, v in h.items()] + [
        "", f"C5 (the keys arm reproduces search-v0.3): {c5['matched']} of {c5['compared']} searches.",
        f"C6 (default-key flags from digests equal the search's): {c6['differing']} of {c6['expansions']} "
        "expansions differ.", "",
        "## Interpretation boundary", "",
        "Breadth-first search with fixed menus on theorems of one Mathlib slice. The keys compare printed goals;",
        "definitional equality is not tested."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--develop", action="store_true", help="both arms on one task outside the sample, budget 4")
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()

    if args.develop:
        candidates = json.loads((SOURCE / "tasks.json").read_text(encoding="utf-8"))
        drawn = {(t["module"], t["declaration"]) for t in draw_tasks()}
        task = next(t for t in candidates if (t["module"], t["declaration"]) not in drawn)
        for arm, search in (("keys", "whole"), ("hammerFree", "whole"), ("hammerFree", "andor")):
            row = run_unit(task, arm, search, CHECK_BUDGET)
            result = row.get("result") or {}
            print(json.dumps({"declaration": row["declaration"], "arm": arm, "search": search,
                              "constructed": row.get("constructed"),
                              "expansions": [e.get("keys") for e in result.get("expansions", [])]}))
        return 0

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        tasks = draw_tasks()
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(tasks)
        payload["tasksSha256"] = sha256_file(TASKS)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("tasks changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("keys", "harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))

    if args.run:
        rows = run_all(tasks, args.workers)
        order = {(a, t["module"], t["declaration"], s): i for i, (t, a, s) in enumerate(units(tasks))}
        rows.sort(key=lambda r: order[unit_key(r)])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows, tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.4-run": summary["hypotheses"], "C5": [summary["C5"]["matched"],
                                                                            summary["C5"]["compared"]],
                          "C6": summary["C6"]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, tasks)
    for key in ("keys", "hammerFree", "hypotheses", "C5", "C6"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.4-check-ok: units={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
