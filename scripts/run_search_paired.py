#!/usr/bin/env python3
"""Search v0.6: the two searches with a step-level prover, sharing their draws.

  python scripts/run_search_paired.py --develop
  python scripts/run_search_paired.py --register
  python scripts/run_search_paired.py --run [--workers 8]
  python scripts/run_search_paired.py --check-committed

search-v0.5 gave the AND-OR search its first lead over the whole-state search (10 theorems against 8) with
BFS-Prover-V2-7B as the proposer, but the proposer samples, so the two searches drew different candidates on the
same goals and two discordant theorems could not separate the design from the draw. This experiment runs the
same searches with the same proposer, on the holdout slice's 200 tasks, with the draws shared between the two
searches of a task (`common_draws.py`): both see identical candidates the first time each meets a goal. The 140
tasks search-v0.5 did not run carry the registered test; the 60 it ran are a replication under the new design.
Each unit is one task: the two searches in turn, each in a fresh REPL, their order alternating from task to
task.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import math
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common_draws  # noqa: E402
import run_holdout as holdout  # noqa: E402
import run_search_keys as rsk  # noqa: E402
import run_search_prover as v5  # noqa: E402
import search_harness as harness  # noqa: E402
import search_keys as keys  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402

ROOT = holdout.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.6"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
DRAWS = EXPERIMENT / "draws.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "draws": ROOT / "scripts" / "common_draws.py", "prover": ROOT / "scripts" / "step_prover.py",
    "keys": ROOT / "scripts" / "search_keys.py", "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py", "runner": Path(__file__).resolve(),
}
MODEL, MODEL_PATH = v5.MODEL, v5.MODEL_PATH
SAMPLES, TEMPERATURE, MAX_TOKENS, BUDGET = v5.SAMPLES, v5.TEMPERATURE, v5.MAX_TOKENS, v5.BUDGET
SEARCHES = ("whole", "andor")
REPLICATION = v5.TASK_LIMIT  # the first 60 tasks of the draw, which search-v0.5 ran
ORDER_CEILING = 0.01
ALPHA = 0.05
KEYS = rsk.KEYS


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def tasks() -> list[dict[str, Any]]:
    """All 200 of holdout-v0.1's tasks in its seeded random order, each with its index in that order."""
    return [t | {"index": i} for i, t in enumerate(json.loads(holdout.TASKS.read_text(encoding="utf-8")))]


def execution_order(task_list: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """The tasks search-v0.5 did not run first, so that the registered test is complete if the run is cut short."""
    return [t for t in task_list if t["index"] >= REPLICATION] + [t for t in task_list if t["index"] < REPLICATION]


def search_order(task: dict[str, Any]) -> tuple[str, str]:
    return SEARCHES if task["index"] % 2 == 0 else SEARCHES[::-1]


def registration_payload(task_list: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.6",
        "question": "with a step-level prover as the proposer and its draws shared between the two searches, does a "
                    "search over goals prove more than a search over whole states",
        "tasks": {"source": "holdout-v0.1/tasks.json", "sourceSha256": sha256_file(holdout.TASKS),
                  "count": len(task_list),
                  "sets": {"test": f"the {len(task_list) - REPLICATION} tasks after the first {REPLICATION} of the "
                                   "draw's seeded random order, which no model search has run",
                           "replication": f"the first {REPLICATION}, which search-v0.5 ran"},
                  "executionOrder": "the test set first, then the replication set"},
        "proposer": "as search-v0.5: BFS-Prover-V2-7B in Q8_0, the first goal pretty-printed and followed by ':::', "
                    f"{SAMPLES} completions at temperature {TEMPERATURE}, at most {MAX_TOKENS} tokens each, "
                    "duplicates dropped in order, no menu",
        "draws": "shared by the two searches of a task (common random numbers): the n-th time a search expands a goal "
                 "it gets the n-th set of candidates drawn for that goal in this task, whichever search drew it "
                 "first; goals identified by canonical_goal; so both searches see identical candidates the first time "
                 "each meets a goal, the AND-OR search (which expands a goal once) only ever uses the first set, and "
                 "the whole-state search draws afresh on each later expansion of a goal",
        "searches": "those of search-v0.4 and v0.5 (search_keys.py), unchanged",
        "execution": "each unit is one task: the two searches in turn, each in a fresh REPL, whole-state first on "
                     "tasks of even index and AND-OR first on odd; a unit that raises is recorded as two error rows "
                     "and run again, both searches with fresh draws, on the next resume; every draw is committed",
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "measures": {
            "proved": "tasks with a proof that re-verifies from the statement, per search and set",
            "expansionsToProof": "the expansion at which a search completed its proof",
            "orderFraction[key]/goalFraction[key]": "as search-v0.4, whole-state search, all tasks",
            "draws": "per search, the expansions that drew candidates and those that used a set already drawn",
            "entangled": "candidates the AND-OR search discarded as entangled"},
        "hypotheses": {
            "H50": "on the test set, the AND-OR search proves more tasks than the whole-state search (one-sided sign "
                   f"test on the tasks proved by exactly one of them, alpha {ALPHA:g})",
            "H51": "on the test set, among the tasks both searches prove with different numbers of expansions, the "
                   f"AND-OR search needs fewer in more than half (one-sided sign test, alpha {ALPHA:g})",
            "H52": f"over all tasks, the whole-state search's order-duplicate fraction under the default key is below "
                   f"{ORDER_CEILING:.0%}",
            "H53": "on the replication set, the AND-OR search proves at least as many tasks as the whole-state "
                   "search (H46 of search-v0.5, under shared draws)"},
        "power": "at search-v0.5's rates about a fifth of the statable tasks are proved, so the test set may yield "
                 "only a handful of discordant tasks and H50 has little power; the decision is reported whichever "
                 "way it comes out",
        "checks": {"C7": "within a task, no goal is drawn twice for the same occurrence"},
        "analyses": {"bootstrap": "95% percentile intervals of the duplicate fractions, resampling modules (2,000 "
                                  "resamples, seed 0)",
                     "discordant": "tasks proved by exactly one search, per set, with a two-sided sign test"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the runner's --develop mode ran both searches with shared draws at 4 "
                                               "expansions on AddConstMapClass.map_const_add, outside the corpus",
        "resultsSeenBeforeRegistration": "every earlier experiment, including search-v0.5 in full: on the "
                                         "replication set its AND-OR search proved 10 tasks and its whole-state "
                                         "search 8, with 2 proved by the AND-OR search alone; no model search had "
                                         "run on the test set",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run_one(task: dict[str, Any], search: str, propose: Any, budget: int) -> dict[str, Any]:
    """One search on one task in a fresh REPL (search-v0.5's run_unit, with the proposer given)."""
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            function = keys.whole_state_search if search == "whole" else keys.and_or_search
            result = function(repl, made.proof_state, [made.goal], propose, budget,
                              verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except ReplTimeout:
        return head | {"constructed": True, "abandoned": "repl timeout",
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()


def run_task(task: dict[str, Any], budget: int = BUDGET) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Both searches of one task with shared draws: their rows, and the task's draws."""
    draws = common_draws.CommonDraws(SAMPLES, TEMPERATURE, MAX_TOKENS, MODEL_PATH)
    order = search_order(task)
    rows = []
    for position, search in enumerate(order):
        row = run_one(task, search, draws.proposer(search), budget)
        rows.append(row | {"index": task["index"], "position": position,
                           "draws": dict(draws.counts.get(search, {"drawn": 0, "shared": 0}))})
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
    # a task being rerun keeps only its new draws
    draws_log = [e for e in draws_log if e["declaration"] in done]
    lock = threading.Lock()
    prover.MODEL_LOG = None  # the draws are logged by CommonDraws, per task

    def guarded(task: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        started = time.monotonic()
        try:
            return run_task(task)
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
            summary = {r["search"]: (len((r.get("result") or {}).get("expansions", [])),
                                     bool((r.get("result") or {}).get("proof"))) for r in task_rows}
            print(json.dumps({"task": task_rows[0]["declaration"], "index": task_rows[0]["index"],
                              "searches": summary, "draws": len(task_draws),
                              "error": task_rows[0].get("error"), "at": time.strftime("%H:%M:%S")},
                             ensure_ascii=False), flush=True)

    todo = [t for t in execution_order(task_list) if t["declaration"] not in done]
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


def sign_upper(k: int, n: int) -> float | None:
    return None if n == 0 else sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def sign_two_sided(k: int, n: int) -> float | None:
    return None if n == 0 else min(1.0, 2 * min(sign_upper(k, n), sign_upper(n - k, n)))


def set_summary(units: dict[str, list[dict[str, Any] | None]]) -> dict[str, Any]:
    ran = {s: [u for u in units[s] if u is not None and "result" in u] for s in SEARCHES}
    proof_at = {s: {u["declaration"]: len(u["result"]["expansions"]) for u in ran[s] if u["result"]["proof"]}
                for s in SEARCHES}
    whole_only = set(proof_at["whole"]) - set(proof_at["andor"])
    andor_only = set(proof_at["andor"]) - set(proof_at["whole"])
    both = set(proof_at["whole"]) & set(proof_at["andor"])
    differing = [d for d in both if proof_at["whole"][d] != proof_at["andor"][d]]
    andor_fewer = sum(1 for d in differing if proof_at["andor"][d] < proof_at["whole"][d])
    return {"tasks": len(units["whole"]),
            "stated": {s: sum(1 for u in units[s] if u is not None and u.get("constructed")) for s in SEARCHES},
            "abandoned": {s: sum(1 for u in units[s] if u is not None and u.get("abandoned")) for s in SEARCHES},
            "errors": {s: sum(1 for u in units[s] if u is not None and u.get("error")) for s in SEARCHES},
            "missing": {s: sum(1 for u in units[s] if u is None) for s in SEARCHES},
            "proved": {s: len(proof_at[s]) for s in SEARCHES},
            "provedTasks": {s: sorted(proof_at[s]) for s in SEARCHES},
            "discordant": {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                           "signTestAndorMore": sign_upper(len(andor_only), len(whole_only) + len(andor_only)),
                           "signTestTwoSided": sign_two_sided(len(andor_only), len(whole_only) + len(andor_only))},
            "bothProved": len(both),
            "expansionsToProof": {"differing": len(differing), "andorFewer": andor_fewer,
                                  "signTestAndorFewer": sign_upper(andor_fewer, len(differing))},
            "entangled": sum(u["result"].get("entangled", 0) for u in ran["andor"]),
            "draws": {s: {k: sum((u.get("draws") or {}).get(k, 0) for u in ran[s]) for k in ("drawn", "shared")}
                      for s in SEARCHES}}


def summarize(rows: list[dict[str, Any]], task_list: list[dict[str, Any]],
              draws_log: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {unit_key(r): r for r in rows}

    def units(subset: list[dict[str, Any]]) -> dict[str, list[dict[str, Any] | None]]:
        return {s: [by_unit.get((t["module"], t["declaration"], s)) for t in subset] for s in SEARCHES}

    test = [t for t in task_list if t["index"] >= REPLICATION]
    replication = [t for t in task_list if t["index"] < REPLICATION]
    everything = units(task_list)
    whole = [u for u in everything["whole"] if u is not None and "result" in u]
    keyed = {key: rsk.fractions(whole, key) | {"bootstrap": rsk.bootstrap(whole, key)} for key in KEYS}
    t, r = set_summary(units(test)), set_summary(units(replication))
    seen: set[tuple[int, str, int]] = set()
    repeats = 0
    for entry in draws_log:
        goal = entry["prompt"][:-len(prover.SEPARATOR)]
        key = (entry["index"], harness.canonical_goal(goal), entry["occurrence"])
        repeats += key in seen
        seen.add(key)
    seconds = [u["result"]["seconds"] for s in SEARCHES for u in everything[s] if u is not None and "result" in u]
    out: dict[str, Any] = {
        "experiment": "search-v0.6", "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
        "test": t, "replication": r, "whole": keyed,
        "searchSeconds": quantiles([float(x) for x in seconds]),
        "C7": {"draws": len(draws_log), "repeated": repeats},
    }
    d = keyed["default"]
    out["hypotheses"] = {
        "H50": {"supported": t["discordant"]["signTestAndorMore"] is not None
                and t["discordant"]["signTestAndorMore"] < ALPHA},
        "H51": {"supported": t["expansionsToProof"]["signTestAndorFewer"] is not None
                and t["expansionsToProof"]["signTestAndorFewer"] < ALPHA},
        "H52": {"supported": d["orderFraction"] is not None and d["orderFraction"] < ORDER_CEILING},
        "H53": {"supported": sum(r["stated"].values()) > 0 and r["proved"]["andor"] >= r["proved"]["whole"]}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["drawsSha256"] = sha256_file(DRAWS) if DRAWS.exists() else None
    return out


def write_report(summary: dict[str, Any]) -> None:
    s = summary
    lines = ["# Both searches with shared draws of a step-level prover (search v0.6)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", ""]
    for name, title in (("test", "Test set (tasks no model search had run)"),
                        ("replication", "Replication set (search-v0.5's tasks)")):
        e = s[name]
        dd, ep = e["discordant"], e["expansionsToProof"]
        lines += [f"## {title}", "",
                  f"Tasks: {e['tasks']}; stated: {e['stated']}; abandoned: {e['abandoned']}; errors: {e['errors']}.",
                  f"Proved: whole {e['proved']['whole']}, AND-OR {e['proved']['andor']}; by one search only: whole "
                  f"{dd['wholeOnly']}, AND-OR {dd['andorOnly']} (one-sided p = {rsk.fmt(dd['signTestAndorMore'], '.3g')}, "
                  f"two-sided p = {rsk.fmt(dd['signTestTwoSided'], '.3g')}).",
                  f"Proved by both: {e['bothProved']}; with different expansions to proof: {ep['differing']}, AND-OR "
                  f"fewer in {ep['andorFewer']} (one-sided p = {rsk.fmt(ep['signTestAndorFewer'], '.3g')}).",
                  f"Entangled candidates: {e['entangled']}. Draws: {e['draws']}.", ""]
    lines += ["## Duplicates (whole-state search, all tasks)", "",
              "| Key | Expansions | Order duplicates | Goal duplicates |", "| --- | ---: | ---: | ---: |"]
    for key in KEYS:
        f = s["whole"][key]
        lines.append(f"| {key} | {f['expansions']} | {f['orderDuplicates']} ({rsk.fmt(f['orderFraction'], '.1%')}) | "
                     f"{f['goalDuplicates']} ({rsk.fmt(f['goalFraction'], '.1%')}) |")
    lines += ["", f"C7: {s['C7']['repeated']} of {s['C7']['draws']} draws repeat a goal and occurrence within a task.",
              "", "## Hypotheses", ""]
    lines += [f"- {k}: supported: {v['supported']}." for k, v in s["hypotheses"].items()]
    lines += ["", "## Interpretation boundary", "",
              "One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the",
              "theorems of one Mathlib slice. Shared draws remove the draw from the comparison of the two searches",
              "on the goals both meet; they do not make the proposer deterministic, so a rerun draws anew."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--develop", action="store_true", help="one task outside the corpus at budget 4")
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()

    if args.develop:
        if not prover.server_alive():
            raise SystemExit("no model server on 127.0.0.1:8080")
        prover.MODEL_LOG = None
        drawn = {t["declaration"] for t in tasks()}
        candidates = json.loads((ROOT / "experiments" / "search-v0.3" / "tasks.json").read_text(encoding="utf-8"))
        task = next(t for t in candidates if t["declaration"] not in drawn) | {"index": 0}
        task_rows, log = run_task(task, 4)
        for row in task_rows:
            result = row.get("result") or {}
            print(json.dumps({"search": row["search"], "position": row["position"], "draws": row["draws"],
                              "proof": result.get("proof"), "expansions": len(result.get("expansions", []))},
                             ensure_ascii=False))
        print(json.dumps({"drawsLogged": len(log)}))
        return 0

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload(tasks())
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {payload['tasks']['count']} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasks"]["sourceSha256"] != sha256_file(holdout.TASKS):
        raise SystemExit("the holdout tasks changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("draws", "prover", "keys", "harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    task_list = tasks()

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
        print(json.dumps({"search-v0.6-run": summary["hypotheses"],
                          "test": {k: summary["test"][k] for k in ("proved", "discordant")},
                          "replication": {k: summary["replication"][k] for k in ("proved", "discordant")}}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()} \
            or summary["drawsSha256"] != sha256_file(DRAWS):
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, task_list, read_draws())
    for key in ("test", "replication", "whole", "C7", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.6-check-ok: units={len(committed)} draws={summary['C7']['draws']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
