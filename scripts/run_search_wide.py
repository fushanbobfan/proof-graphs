#!/usr/bin/env python3
"""Search v0.3: the menu searches of search-v0.1 on every candidate theorem.

  python scripts/run_search_wide.py --register
  python scripts/run_search_wide.py --run [--workers 4]
  python scripts/run_search_wide.py --check-committed

search-v0.1 sampled 47 of the 1,347 theorems of the Mathlib slice whose proof
is one `by` block of 3 to 20 steps (every 29th). This experiment runs the
deterministic menu arm of both searches, unchanged, on all of them at the same
budget of 24 expansions, each (theorem, search) unit in a fresh REPL
(`run_search_deep.run_unit`). The tasks of search-v0.1 are part of this
corpus, so their searches must reproduce the committed ones exactly.
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
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import sha256_file, write_lf  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "search-v0.3"
PREREG = EXPERIMENT / "preregistration.json"
TASKS = EXPERIMENT / "tasks.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py",
    "runner": Path(__file__).resolve(),
    "deepRunner": ROOT / "scripts" / "run_search_deep.py",
    "v1Runner": ROOT / "scripts" / "run_search.py",
}
BUDGET = 24
ARM = "menu"
SEARCHES = v2.SEARCHES
ORDER_CEILING = 0.05
SHARING_RATIO = 2.0
PERMUTATIONS = 10_000
CHECK_BUDGET = 4


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "search-v0.3",
        "question": "are the redundancy measures and the search comparison of search-v0.1 properties of the whole "
                    "population of candidate theorems rather than of its 47-task sample",
        "tasks": {"source": "linearizations-mathlib-v0.1", "sliceResultsSha256": sha256_file(slice_.RESULTS),
                  "sliceExtractionSha256": sha256_file(slice_.EXTRACTION),
                  "rule": f"every theorem of the slice whose proof is one `by` block of {v1.MIN_STEPS} to "
                          f"{v1.MAX_STEPS} steps, not generated, in (module, line) order: the candidate list of "
                          "search-v0.1, all of it",
                  "count": len(tasks)},
        "arm": "menu only: the fixed menu of scripts/search_harness.py, unchanged; the model arm is not run, since "
               "it is stochastic and costs about four times as much per search",
        "searches": "those of search-v0.1 after its amendment 2, unchanged (breadth-first whole-state search with "
                    "exact-state deduplication; breadth-first AND-OR search over canonical goals with the "
                    "entanglement rule; closing candidates verified inside the search, sorry refused)",
        "budget": {"expansionsPerSearch": BUDGET, "tacticWallClockSeconds": 60, "heartbeats": 40000},
        "execution": "every (task, search) unit in a fresh REPL, four units at a time, resumable",
        "measures": {
            "orderFraction": "whole-state expansions whose goal multiset was already expanded in another order, "
                             "over all whole-state expansions",
            "goalFraction": "whole-state expansions whose first goal, canonicalized, was already expanded as a "
                            "first goal, over all whole-state expansions",
            "proved": "tasks with a proof that re-verifies from the statement, per search",
            "entangled": "candidates the AND-OR search discarded as entangled"},
        "hypotheses": {
            "H22": f"the order-duplicate fraction of the whole-state search is below {ORDER_CEILING:.0%}",
            "H23": f"the goal-duplicate fraction is at least {SHARING_RATIO:g} times the order-duplicate fraction",
            "H24": "the AND-OR search proves at least as many tasks as the whole-state search",
            "H25": "of the tasks that the whole-state search proves and the AND-OR search does not, at least half "
                   "have at least one candidate discarded as entangled by the AND-OR search (undecidable if "
                   "there is no such task)",
        },
        "checks": {"C2": "for every task stated in search-v0.1, both menu searches equal the committed ones "
                         "(expansion records and proof), since the menu proposer is deterministic"},
        "analyses": {
            "orderVsOrderings": "Spearman correlation, over tasks with at least one whole-state expansion, between "
                                "log10 of the original proof's number of orderings and the task's number of "
                                f"order-duplicate expansions; two-sided permutation p-value ({PERMUTATIONS} "
                                "permutations, seed 0)",
            "goalVsOrderings": "the same with goal-duplicate expansions",
            "discordant": "tasks proved by exactly one search, with a two-sided sign test"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the runner was exercised on the first candidate task, whole-state "
                                                "search, at budget 4; no other unit was run",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run_all(tasks: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    """Every (task, search) unit not yet recorded, four at a time. An exception raised by a unit is recorded as an
    error row and retried on the next resume; nothing a unit does can stop the recording."""
    rows: list[dict[str, Any]] = []
    if RESULTS.exists():
        rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    done = {(r["module"], r["declaration"], r["search"]) for r in rows if not r.get("error")}
    lock = threading.Lock()

    def guarded(task: dict[str, Any], search: str) -> dict[str, Any]:
        started = time.monotonic()
        try:
            return v2.run_unit(task, ARM, search, BUDGET)
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "arm": ARM, "search": search,
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}

    def record(row: dict[str, Any]) -> None:
        with lock:
            rows.append(row)
            with RESULTS.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["declaration"], row["search"]], "expansions": len(result.get("expansions", [])),
                              "proof": bool(result.get("proof")), "abandoned": row.get("abandoned"),
                              "error": row.get("error"), "at": time.strftime("%H:%M:%S")}), flush=True)

    units = [(t, s) for t in tasks for s in SEARCHES if (t["module"], t["declaration"], s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t, s) for t, s in units]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    latest = {(r["module"], r["declaration"], r["search"]): r for r in rows}  # a retried unit keeps its last row
    return list(latest.values())


def ranks(values: list[float]) -> list[float]:
    """Average ranks, 1-based, ties sharing the mean of their positions."""
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and values[order[j + 1]] == values[order[i]]:
            j += 1
        for k in range(i, j + 1):
            out[order[k]] = (i + j) / 2 + 1
        i = j + 1
    return out


def pearson(x: list[float], y: list[float]) -> float | None:
    n = len(x)
    mx, my = sum(x) / n, sum(y) / n
    sxy = sum((a - mx) * (b - my) for a, b in zip(x, y))
    sxx = sum((a - mx) ** 2 for a in x)
    syy = sum((b - my) ** 2 for b in y)
    return sxy / math.sqrt(sxx * syy) if sxx > 0 and syy > 0 else None


def spearman_test(x: list[float], y: list[float]) -> dict[str, Any]:
    if len(x) < 3:
        return {"n": len(x), "rho": None, "pValue": None}
    rx, ry = ranks(x), ranks(y)
    rho = pearson(rx, ry)
    if rho is None:
        return {"n": len(x), "rho": None, "pValue": None}
    rng = random.Random(0)
    shuffled = list(ry)
    extreme = 0
    for _ in range(PERMUTATIONS):
        rng.shuffle(shuffled)
        r = pearson(rx, shuffled)
        if r is not None and abs(r) >= abs(rho) - 1e-12:
            extreme += 1
    return {"n": len(x), "rho": rho, "pValue": (extreme + 1) / (PERMUTATIONS + 1)}


def sign_test_two_sided(k: int, n: int) -> float | None:
    if n == 0:
        return None
    tail = sum(math.comb(n, i) for i in range(max(k, n - k), n + 1)) / 2 ** n
    return min(1.0, 2 * tail)


def replication(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """C2: the menu searches of the search-v0.1 tasks against the committed ones."""
    committed = {(r["module"], r["declaration"]): r for r in v2.v1_rows() if r.get("task")}
    compared, matched, mismatches = 0, 0, []
    for row in rows:
        old_row = committed.get((row["module"], row["declaration"]))
        if old_row is None or "result" not in row:
            continue
        old = old_row[f"menu.{row['search']}"]
        keys = v2.WHOLE_KEYS if row["search"] == "whole" else v2.ANDOR_KEYS
        new_exp = [{k: e[k] for k in keys} for e in row["result"]["expansions"]]
        old_exp = [{k: e[k] for k in keys} for e in old["expansions"]]
        compared += 1
        if new_exp == old_exp and row["result"]["proof"] == old["proof"]:
            matched += 1
        else:
            first = next((i for i, (a, b) in enumerate(zip(new_exp, old_exp)) if a != b),
                         min(len(new_exp), len(old_exp)))
            mismatches.append({"declaration": row["declaration"], "search": row["search"], "firstDifference": first})
    return {"compared": compared, "matched": matched, "mismatches": mismatches}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {(r["module"], r["declaration"], r["search"]): r for r in rows}
    units = {s: [by_unit.get((t["module"], t["declaration"], s)) for t in tasks] for s in SEARCHES}
    ran = {s: [u for u in units[s] if u is not None and "result" in u] for s in SEARCHES}
    whole = [e for u in ran["whole"] for e in u["result"]["expansions"]]
    order = sum(1 for e in whole if e["orderDuplicate"])
    goal = sum(1 for e in whole if e["goalDuplicate"])
    andor_valid = sum(e["valid"] for u in ran["andor"] for e in u["result"]["expansions"])
    entangled = sum(u["result"].get("entangled", 0) for u in ran["andor"])
    proved = {s: {(u["module"], u["declaration"]) for u in ran[s] if u["result"]["proof"]} for s in SEARCHES}
    whole_only = proved["whole"] - proved["andor"]
    andor_only = proved["andor"] - proved["whole"]
    andor_by_task = {(u["module"], u["declaration"]): u for u in ran["andor"]}
    whole_only_entangled = sum(1 for key in whole_only
                               if key in andor_by_task and andor_by_task[key]["result"].get("entangled", 0) > 0)
    out: dict[str, Any] = {
        "experiment": "search-v0.3", "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
        "tasks": len(tasks),
        "constructed": sum(1 for u in units["whole"] if u is not None and u.get("constructed")),
        "abandoned": {s: sum(1 for u in units[s] if u is not None and u.get("abandoned")) for s in SEARCHES},
        "errors": {s: sum(1 for u in units[s] if u is not None and u.get("error")) for s in SEARCHES},
        "whole": {"expansions": len(whole), "orderDuplicates": order,
                  "orderFraction": order / len(whole) if whole else None,
                  "goalDuplicates": goal, "goalFraction": goal / len(whole) if whole else None,
                  "validPerExpansion": sum(e["valid"] for e in whole) / len(whole) if whole else None,
                  "proved": len(proved["whole"]),
                  "frontierExhausted": sum(1 for u in ran["whole"] if not u["result"]["proof"]
                                           and len(u["result"]["expansions"]) < BUDGET)},
        "andor": {"expansions": sum(len(u["result"]["expansions"]) for u in ran["andor"]),
                  "proved": len(proved["andor"]), "entangled": entangled,
                  "entangledShare": entangled / (andor_valid + entangled) if andor_valid + entangled else None,
                  "picks": sum(u["result"].get("picks", 0) for u in ran["andor"])},
        "discordant": {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                       "wholeOnlyWithEntangled": whole_only_entangled,
                       "signTestTwoSided": sign_test_two_sided(len(andor_only), len(whole_only) + len(andor_only))},
    }
    per_task = []
    for task in tasks:
        unit = by_unit.get((task["module"], task["declaration"], "whole"))
        if unit is None or "result" not in unit or not unit["result"]["expansions"]:
            continue
        expansions = unit["result"]["expansions"]
        per_task.append((math.log10(int(task["linearizations"])),
                         sum(1 for e in expansions if e["orderDuplicate"]),
                         sum(1 for e in expansions if e["goalDuplicate"])))
    out["analyses"] = {
        "orderVsOrderings": spearman_test([p[0] for p in per_task], [p[1] for p in per_task]),
        "goalVsOrderings": spearman_test([p[0] for p in per_task], [p[2] for p in per_task])}
    w, a = out["whole"], out["andor"]
    out["hypotheses"] = {
        "H22": {"supported": w["orderFraction"] is not None and w["orderFraction"] < ORDER_CEILING},
        "H23": {"supported": w["orderFraction"] is not None and w["goalFraction"] >= SHARING_RATIO * w["orderFraction"]},
        "H24": {"supported": bool(ran["whole"]) and a["proved"] >= w["proved"]},
        "H25": {"supported": None if not whole_only else 2 * whole_only_entangled >= len(whole_only)},
    }
    out["C2"] = replication(rows)
    out["resultsSha256"] = sha256_file(RESULTS)
    return out


def fmt(x: float | None, pattern: str) -> str:
    return "n/a" if x is None else format(x, pattern)


def write_report(summary: dict[str, Any]) -> None:
    w, a, d, h, c = summary["whole"], summary["andor"], summary["discordant"], summary["hypotheses"], summary["C2"]
    an = summary["analyses"]
    lines = ["# Menu searches on every candidate theorem (search v0.3)", "",
             "The menu arm of search-v0.1's two searches, unchanged, on all candidate theorems of the Mathlib",
             "slice; definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Tasks: {summary['tasks']}; stated: {summary['constructed']}; abandoned on a REPL timeout: "
             f"whole {summary['abandoned']['whole']}, AND-OR {summary['abandoned']['andor']}.", "",
             "| Search | Expansions | Order duplicates | Goal duplicates | Proved | Entangled candidates |",
             "| --- | ---: | ---: | ---: | ---: | ---: |",
             f"| whole-state | {w['expansions']} | {w['orderDuplicates']} ({fmt(w['orderFraction'], '.1%')}) | "
             f"{w['goalDuplicates']} ({fmt(w['goalFraction'], '.1%')}) | {w['proved']} | |",
             f"| AND-OR | {a['expansions']} | | | {a['proved']} | {a['entangled']} ({fmt(a['entangledShare'], '.1%')}) |",
             "", f"Proved by the whole-state search only: {d['wholeOnly']} ({d['wholeOnlyWithEntangled']} with an "
             f"entangled candidate); by the AND-OR search only: {d['andorOnly']} (two-sided sign test "
             f"p = {fmt(d['signTestTwoSided'], '.3g')}).", "",
             "## Hypotheses", "",
             f"- H22 (order-duplicate fraction below {ORDER_CEILING:.0%}): supported: {h['H22']['supported']}.",
             f"- H23 (goal duplicates at least {SHARING_RATIO:g} times order duplicates): supported: "
             f"{h['H23']['supported']}.",
             f"- H24 (AND-OR proves at least as many): supported: {h['H24']['supported']}.",
             f"- H25 (at least half of the whole-only tasks have an entangled candidate): supported: "
             f"{h['H25']['supported']}.", "",
             f"C2 (the search-v0.1 tasks reproduce exactly): {c['matched']} of {c['compared']} searches.", "",
             "## Registered analyses", "",
             f"- Order duplicates against log10 orderings of the original proof: Spearman rho = "
             f"{fmt(an['orderVsOrderings']['rho'], '.3f')}, p = {fmt(an['orderVsOrderings']['pValue'], '.3g')}, "
             f"n = {an['orderVsOrderings']['n']}.",
             f"- Goal duplicates against log10 orderings: rho = {fmt(an['goalVsOrderings']['rho'], '.3f')}, "
             f"p = {fmt(an['goalVsOrderings']['pValue'], '.3g')}, n = {an['goalVsOrderings']['n']}.", "",
             "## Interpretation boundary", "",
             "Breadth-first search with the 26-tactic menu at 24 expansions, on every candidate theorem of one",
             "Mathlib slice. The measures describe where such a search spends its expansions, not the best",
             "achievable prover."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--develop", action="store_true", help="run the first task's whole-state search at budget 4")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    if args.develop:
        task = v1.candidate_tasks()[0]
        row = v2.run_unit(task, ARM, "whole", CHECK_BUDGET)
        print(json.dumps({"declaration": row["declaration"], "constructed": row.get("constructed"),
                          "expansions": len(row.get("result", {}).get("expansions", []))}))
        return 0

    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        tasks = v1.candidate_tasks()
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(tasks)
        payload["tasksSha256"] = sha256_file(TASKS)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["tasksSha256"] != sha256_file(TASKS):
        raise SystemExit("tasks changed since registration")
    if prereg["tasks"]["sliceResultsSha256"] != sha256_file(slice_.RESULTS):
        raise SystemExit("the slice results changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("harness", "repl", "deepRunner", "v1Runner"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))

    if args.run:
        rows = run_all(tasks, args.workers)
        order = {(t["module"], t["declaration"], s): i for i, (t, s) in
                 enumerate((t, s) for t in tasks for s in SEARCHES)}
        rows.sort(key=lambda r: order[(r["module"], r["declaration"], r["search"])])
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary = summarize(rows, tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"search-v0.3-run": summary["hypotheses"], "C2": [summary["C2"]["matched"],
                                                                            summary["C2"]["compared"]]}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    recomputed = summarize(committed, tasks)
    for key in ("whole", "andor", "discordant", "analyses", "hypotheses", "C2"):
        if recomputed[key] != summary[key]:
            raise SystemExit(f"the committed summary does not follow from the committed results ({key})")
    first = next((r for r in committed if r["search"] == "whole" and "result" in r), None)
    if first is not None:
        task = next(t for t in tasks if (t["module"], t["declaration"]) == (first["module"], first["declaration"]))
        fresh = v2.run_unit(task, ARM, "whole", CHECK_BUDGET)["result"]["expansions"]
        want = first["result"]["expansions"][:CHECK_BUDGET]
        if [{k: e[k] for k in v2.WHOLE_KEYS} for e in fresh] != [{k: e[k] for k in v2.WHOLE_KEYS} for e in want]:
            raise SystemExit(f"the first task's search differs on re-run: {fresh} vs {want}")
    print(f"search-v0.3-check-ok: units={len(committed)} rerun={'yes' if first else 'no'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
