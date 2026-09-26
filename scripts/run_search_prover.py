#!/usr/bin/env python3
"""Search v0.5: both searches with a step-level Lean prover as the proposer.

  python scripts/run_search_prover.py --develop
  python scripts/run_search_prover.py --register
  python scripts/run_search_prover.py --run [--workers 4]
  python scripts/run_search_prover.py --check-committed

Every search experiment so far used a proposer too weak for the question the program set out to answer. The menu
proves what it proves with a one-shot prover in one step, and removing those provers (search-v0.4) left searches
that go deep and prove nothing; a search over goals had no room to win. This experiment replaces the proposer
with BFS-Prover-V2-7B, a model trained to emit one Lean tactic for one tactic state, on the tasks of the
holdout slice, where `holdout-v0.1` has already run the menu proposer at 24 expansions. The comparison with
that run is the check that the proposer really is stronger; the comparison between the two searches at 48
expansions is the question.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import json
import math
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_holdout as holdout  # noqa: E402
import run_search_keys as rsk  # noqa: E402
import search_harness as harness  # noqa: E402
import search_keys as keys  # noqa: E402
import step_prover as prover  # noqa: E402
from lean_repl import LeanRepl, ReplTimeout  # noqa: E402
from run_linearizations import find_lake, quantiles, sha256_file, write_lf  # noqa: E402

ROOT = holdout.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.5"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
CALLS = EXPERIMENT / "model-calls.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "prover": ROOT / "scripts" / "step_prover.py", "keys": ROOT / "scripts" / "search_keys.py",
    "harness": ROOT / "scripts" / "search_harness.py", "repl": ROOT / "scripts" / "lean_repl.py",
    "holdoutRunner": ROOT / "scripts" / "run_holdout.py", "runner": Path(__file__).resolve(),
}
MODEL = "BFS-Prover-V2-7B.Q8_0.gguf"
MODEL_PATH = r"D:\ucla\models\gguf\BFS-Prover-V2-7B.Q8_0.gguf"
SAMPLES = 16
TEMPERATURE = 1.0
MAX_TOKENS = 64
BUDGET = 48
BASELINE_BUDGET = 24  # holdout-v0.1's budget, the checkpoint the two proposers are compared at
SEARCHES = ("whole", "andor")
ORDER_CEILING = 0.05
SHARING_RATIO = 2.0
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
    return json.loads(holdout.TASKS.read_text(encoding="utf-8"))


def registration_payload(task_list: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.5",
        "question": "with a proposer trained to propose Lean tactics, does a search over goals prove more than a "
                    "search over whole states, and do the redundancy measures change",
        "tasks": {"source": "holdout-v0.1/tasks.json", "sourceSha256": sha256_file(holdout.TASKS),
                  "count": len(task_list),
                  "rule": "the holdout slice's search tasks, unchanged, so that holdout-v0.1's menu searches on "
                          "the same theorems are the baseline"},
        "proposer": {"model": MODEL, "quantization": "Q8_0 GGUF of ByteDance-Seed/BFS-Prover-V2-7B (Apache-2.0), "
                                                    "base Qwen2.5-Math-7B, served by llama.cpp",
                     "prompt": "the first goal of the state being expanded, pretty-printed by Lean, followed by "
                               "':::' as the model's card specifies; the reply's first line is the tactic",
                     "sampling": f"{SAMPLES} completions at temperature {TEMPERATURE}, at most {MAX_TOKENS} "
                                 "tokens each, duplicates dropped, order preserved; no menu is appended, so the "
                                 "proposer is the model alone",
                     "endpoint": "/v1/completions (the model is a completion model, not a chat model)"},
        "searches": "those of search-v0.4 (search_keys.py): breadth-first whole-state with exact-state "
                    "deduplication, and breadth-first AND-OR over canonical goals with the entanglement rule and "
                    "a goal's proof set once; closing candidates verified inside the search, sorry refused",
        "budget": {"expansionsPerSearch": BUDGET, "baselineCheckpoint": BASELINE_BUDGET,
                   "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "execution": "every (task, search) unit in a fresh REPL, resumable; an exception raised by a unit is "
                     "recorded as an error row and the unit is run again on the next resume; every prompt and "
                     "reply is committed",
        "measures": {
            "proved": "tasks with a proof that re-verifies from the statement, per search, at the baseline "
                      "checkpoint and at the full budget",
            "orderFraction[key]/goalFraction[key]": "as search-v0.4, under the fine, default, and coarse keys",
            "provedAfterBaseline": "tasks whose proof was found after expansion 24",
            "entangled": "candidates the AND-OR search discarded as entangled",
            "modelSeconds": "wall clock spent in the model, per unit"},
        "hypotheses": {
            "H45": f"at {BASELINE_BUDGET} expansions the whole-state search with this proposer proves more tasks "
                   "than holdout-v0.1's menu whole-state search on the same tasks (one-sided sign test on the "
                   f"tasks proved by exactly one of them, alpha {ALPHA:g})",
            "H46": f"at {BUDGET} expansions the AND-OR search proves at least as many tasks as the whole-state "
                   "search",
            "H47": f"the whole-state goal-duplicate fraction under the default key is at least "
                   f"{SHARING_RATIO:g} times its order-duplicate fraction",
            "H48": f"the whole-state order-duplicate fraction under the default key is below {ORDER_CEILING:.0%}",
            "H49": f"at least one search finds a proof after expansion {BASELINE_BUDGET}, so that the budget "
                   "beyond the baseline is used"},
        "analyses": {
            "bootstrap": "95% percentile intervals of every fraction, resampling modules with replacement "
                         "(2,000 resamples, seed 0)",
            "byKey": "the duplicate fractions under all three keys, as search-v0.4",
            "discordant": "tasks proved by exactly one search at the full budget, with a two-sided sign test"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the proposer was benchmarked on three fixed goals written by "
                                               "hand, none from any corpus (a universally quantified identity, a "
                                               "linear inequality, and a list-length equation): 0.3 s for 4 "
                                               "completions and about 1 s for 16, which fixed the sampling "
                                               "parameters; the server caps n at its parallel slot count, so the "
                                               "client batches; no task of this corpus was run",
        "resultsSeenBeforeRegistration": "every earlier search experiment, and holdout-v0.1's counts. Its menu "
                                         "searches on these tasks, the baseline of H45, were still running and "
                                         "no summary, proof count, or row of them had been read",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run_unit(task: dict[str, Any], search: str, budget: int = BUDGET) -> dict[str, Any]:
    """One search on one task in a fresh REPL, with the model proposer."""
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = LeanRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = harness.ModuleSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            propose = prover.proposer(SAMPLES, TEMPERATURE, MAX_TOKENS, MODEL_PATH)
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


def unit_key(row: dict[str, Any]) -> tuple[str, str, str]:
    return row["module"], row["declaration"], row["search"]


def run_all(task_list: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    done = {unit_key(r) for r in rows if not r.get("error")}
    calls: list[dict[str, Any]] = []
    if CALLS.exists():
        calls = [json.loads(l) for l in gzip.decompress(CALLS.read_bytes()).decode("utf-8").splitlines() if l.strip()]
    prover.MODEL_LOG = calls
    lock = threading.Lock()

    def guarded(task: dict[str, Any], search: str) -> dict[str, Any]:
        started = time.monotonic()
        try:
            return run_unit(task, search)
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "search": search,
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}

    def record(row: dict[str, Any]) -> None:
        with lock:
            rows.append(row)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["declaration"], row["search"]],
                              "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                              "error": row.get("error"), "calls": len(calls),
                              "at": time.strftime("%H:%M:%S")}), flush=True)

    todo = [(t, s) for t in task_list for s in SEARCHES if (t["module"], t["declaration"], s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t, s) for t, s in todo]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    CALLS.write_bytes(gzip.compress(
        "".join(json.dumps(c, ensure_ascii=False) + "\n" for c in calls).encode("utf-8"), compresslevel=9, mtime=0))
    latest = {unit_key(r): r for r in rows}
    return list(latest.values())


def proof_expansion(result: dict[str, Any]) -> int | None:
    """The expansion at which the proof was found, 1-based, or None."""
    return len(result["expansions"]) if result.get("proof") else None


def sign_upper(k: int, n: int) -> float | None:
    return None if n == 0 else sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def summarize(rows: list[dict[str, Any]], task_list: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {unit_key(r): r for r in rows}
    units = {s: [by_unit.get((t["module"], t["declaration"], s)) for t in task_list] for s in SEARCHES}
    ran = {s: [u for u in units[s] if u is not None and "result" in u] for s in SEARCHES}
    proved = {s: {u["declaration"] for u in ran[s] if u["result"]["proof"]} for s in SEARCHES}
    at_baseline = {s: {u["declaration"] for u in ran[s] if u["result"]["proof"]
                       and len(u["result"]["expansions"]) <= BASELINE_BUDGET} for s in SEARCHES}
    baseline_rows = [json.loads(l) for l in holdout.SEARCHES.read_text(encoding="utf-8").splitlines() if l.strip()]
    menu_proved = {r["declaration"] for r in baseline_rows
                   if r["search"] == "whole" and (r.get("result") or {}).get("proof")}
    model_only = at_baseline["whole"] - menu_proved
    menu_only = menu_proved - at_baseline["whole"]
    p45 = sign_upper(len(model_only), len(model_only) + len(menu_only))
    whole_only, andor_only = proved["whole"] - proved["andor"], proved["andor"] - proved["whole"]
    whole = ran["whole"]
    keyed = {key: rsk.fractions(whole, key) | {"bootstrap": rsk.bootstrap(whole, key)} for key in KEYS}
    default = keyed["default"]
    after_baseline = sum(1 for s in SEARCHES for u in ran[s]
                         if u["result"]["proof"] and len(u["result"]["expansions"]) > BASELINE_BUDGET)
    model_seconds = [u.get("result", {}).get("seconds", 0) for u in whole]
    out: dict[str, Any] = {
        "experiment": "search-v0.5", "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
        "tasks": len(task_list),
        "constructed": {s: sum(1 for u in units[s] if u is not None and u.get("constructed")) for s in SEARCHES},
        "abandoned": {s: sum(1 for u in units[s] if u is not None and u.get("abandoned")) for s in SEARCHES},
        "errors": {s: sum(1 for u in units[s] if u is not None and u.get("error")) for s in SEARCHES},
        "missing": {s: sum(1 for u in units[s] if u is None) for s in SEARCHES},
        "whole": keyed,
        "proved": {s: len(v) for s, v in proved.items()},
        "provedAtBaseline": {s: len(v) for s, v in at_baseline.items()},
        "menuBaselineProved": len(menu_proved),
        "againstMenu": {"modelOnly": len(model_only), "menuOnly": len(menu_only), "pValue": p45},
        "provedAfterBaseline": after_baseline,
        "andor": {"expansions": sum(len(u["result"]["expansions"]) for u in ran["andor"]),
                  "entangled": sum(u["result"].get("entangled", 0) for u in ran["andor"]),
                  "picks": sum(u["result"].get("picks", 0) for u in ran["andor"])},
        "discordant": {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                       "signTestTwoSided": None if not (whole_only | andor_only) else
                       min(1.0, 2 * min(sign_upper(len(andor_only), len(whole_only) + len(andor_only)),
                                        sign_upper(len(whole_only), len(whole_only) + len(andor_only))))},
        "searchSeconds": quantiles([float(s) for s in model_seconds]),
        "frontierExhausted": {s: sum(1 for u in ran[s] if not u["result"]["proof"]
                                     and len(u["result"]["expansions"]) < BUDGET) for s in SEARCHES},
    }
    out["hypotheses"] = {
        "H45": {"supported": p45 is not None and p45 < ALPHA},
        "H46": {"supported": bool(ran["whole"]) and len(proved["andor"]) >= len(proved["whole"])},
        "H47": {"supported": default["orderFraction"] is not None
                and default["goalFraction"] >= SHARING_RATIO * default["orderFraction"]},
        "H48": {"supported": default["orderFraction"] is not None and default["orderFraction"] < ORDER_CEILING},
        "H49": {"supported": after_baseline > 0}}
    out["resultsSha256"] = sha256_file(RESULTS)
    out["callsSha256"] = sha256_file(CALLS) if CALLS.exists() else None
    return out


def write_report(summary: dict[str, Any]) -> None:
    s = summary
    d = s["whole"]["default"]
    lines = ["# A step-level Lean prover as the proposer (search v0.5)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             f"Tasks: {s['tasks']}; stated: {s['constructed']}; abandoned: {s['abandoned']}; errors: {s['errors']}.",
             "",
             "| Key | Expansions | Order duplicates | Goal duplicates |", "| --- | ---: | ---: | ---: |"]
    for key in KEYS:
        f = s["whole"][key]
        lines.append(f"| {key} | {f['expansions']} | {f['orderDuplicates']} "
                     f"({rsk.fmt(f['orderFraction'], '.1%')}) | {f['goalDuplicates']} "
                     f"({rsk.fmt(f['goalFraction'], '.1%')}) |")
    a = s["againstMenu"]
    lines += ["", f"Proved at {BASELINE_BUDGET} expansions: model {s['provedAtBaseline']['whole']}, "
              f"holdout-v0.1's menu {s['menuBaselineProved']} (model only {a['modelOnly']}, menu only "
              f"{a['menuOnly']}, one-sided p = {rsk.fmt(a['pValue'], '.3g')}).",
              f"Proved at {BUDGET}: whole {s['proved']['whole']}, AND-OR {s['proved']['andor']}; discordant "
              f"{s['discordant']}. Proofs found after expansion {BASELINE_BUDGET}: {s['provedAfterBaseline']}.",
              f"Entangled candidates: {s['andor']['entangled']}. Frontier exhausted: {s['frontierExhausted']}.",
              "", "## Hypotheses", ""]
    lines += [f"- {k}: supported: {v['supported']}." for k, v in s["hypotheses"].items()]
    lines += ["", "## Interpretation boundary", "",
              "One quantized open-weights prover at one sampling setting, on the theorems of one Mathlib slice.",
              "The model proposes tactics for the first goal only, which is what it was trained on; the",
              "whole-state search therefore sees no more context than the AND-OR search does."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--develop", action="store_true", help="one task outside the corpus at budget 4")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    if args.develop:
        if not prover.server_alive():
            raise SystemExit("no model server on 127.0.0.1:8080")
        prover.probe_max_n(MODEL_PATH)
        drawn = {(t["module"], t["declaration"]) for t in tasks()}
        candidates = json.loads((ROOT / "experiments" / "search-v0.3" / "tasks.json").read_text(encoding="utf-8"))
        task = next(t for t in candidates if (t["module"], t["declaration"]) not in drawn)
        for search in SEARCHES:
            row = run_unit(task, search, 4)
            result = row.get("result") or {}
            print(json.dumps({"declaration": row["declaration"], "search": search,
                              "constructed": row.get("constructed"), "proof": result.get("proof"),
                              "expansions": len(result.get("expansions", [])),
                              "seconds": result.get("seconds")}, ensure_ascii=False))
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
    for name in ("prover", "keys", "harness", "repl"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    task_list = tasks()

    if args.run:
        if not prover.server_alive():
            raise SystemExit("no model server on 127.0.0.1:8080")
        prover.probe_max_n(MODEL_PATH)
        rows = run_all(task_list, args.workers)
        order = {(t["module"], t["declaration"], s): i for i, (t, s) in
                 enumerate((t, s) for t in task_list for s in SEARCHES)}
        rows.sort(key=lambda r: order[unit_key(r)])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows, task_list)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.5-run": summary["hypotheses"], "proved": summary["proved"],
                          "againstMenu": summary["againstMenu"]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, task_list)
    for key in ("whole", "proved", "provedAtBaseline", "againstMenu", "discordant", "hypotheses"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    print(f"search-v0.5-check-ok: units={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
