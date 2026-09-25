#!/usr/bin/env python3
"""Holdout v0.1: the counts and the searches repeated on a second, disjoint Mathlib slice.

  python scripts/run_holdout.py --register
  python scripts/run_holdout.py --extract [--workers 4]
  python scripts/run_holdout.py --search [--workers 4]
  python scripts/run_holdout.py --check-committed

The first slice (linearizations-mathlib-v0.1) is every 50th module of Mathlib's population in name order,
starting at the first; its proofs supplied every Lean search task so far. This slice is every 50th module
starting at the 26th, so no module is in both. It is extracted with the same extractor and counted under the
corrected step derivation (`count_linearizations_v2.py`), and the hypotheses decided on the first slice and on
search-v0.3 are tested again, as registered there, on data none of them has seen.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import random
import sys
import threading
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations_v2 as counter  # noqa: E402
import run_linearizations as base  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
import run_search as v1  # noqa: E402
import run_search_keys as rsk  # noqa: E402
from run_linearizations import (STRATA, int_quantiles, quantiles, read_gz_lines, same_row, sha256_file,  # noqa: E402
                                stratum, write_gz, write_lf)

ROOT = base.ROOT
EXPERIMENT = ROOT / "experiments" / "holdout-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
EXTRACTION = EXPERIMENT / "extraction.jsonl.gz"
FAILURES = EXPERIMENT / "failures.json"
COUNTS = EXPERIMENT / "counts.jsonl"
TASKS = EXPERIMENT / "tasks.json"
SEARCHES = EXPERIMENT / "searches.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
RECOUNT = ROOT / "experiments" / "recount-v0.1" / "summary.json"
IMPLEMENTATIONS = {
    "extractor": base.IMPLEMENTATIONS["extractor"], "extractorMain": base.IMPLEMENTATIONS["extractorMain"],
    "counter": ROOT / "scripts" / "count_linearizations_v2.py",
    "earlierCounter": ROOT / "scripts" / "count_linearizations.py",
    "keys": ROOT / "scripts" / "search_keys.py", "harness": ROOT / "scripts" / "search_harness.py",
    "repl": ROOT / "scripts" / "lean_repl.py", "keysRunner": ROOT / "scripts" / "run_search_keys.py",
    "runner": Path(__file__).resolve(),
}
OFFSET = 25
SEARCH_TASKS = 200
SEED = 20260927
BUDGET = 24
MINIMUM_STRATUM = slice_.MINIMUM_STRATUM
TOLERANCE = slice_.TOLERANCE
ORDER_CEILING = 0.05
SHARING_RATIO = 2.0
CHECK_SAMPLE_SIZE = 3


def modules() -> list[tuple[str, Path]]:
    return slice_.population()[OFFSET::slice_.STRIDE]


def extract(selection: list[tuple[str, Path]], workers: int) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    """`run_mathlib_slice.extract`, one module per worker; records and failures in module-name order."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        parts = list(pool.map(lambda item: slice_.extract([item]), selection))
    records = [r for recs, _ in parts for r in recs]
    failures = [f for _, fails in parts for f in fails]
    return records, failures


def count(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [counter.analyse(r) for r in records]


def strata(rows: list[dict[str, Any]]) -> dict[str, Any]:
    out = {}
    for low, high in STRATA:
        members = [r for r in rows if low <= r["steps"] <= high]
        counted = [r for r in members if r["linearizations"] is not None]
        out[stratum(low)] = {
            "proofs": len(members), "counted": len(counted), "excluded": len(members) - len(counted),
            "forests": sum(1 for r in members if r["forest"]),
            "linearizations": int_quantiles([int(r["linearizations"]) for r in counted]),
            "log10": quantiles([r["log10"] for r in counted if r["log10"] is not None]),
            "structure": quantiles([r["structure"] for r in counted if r["structure"] is not None]),
            "fractionSingleOrder": (sum(1 for r in counted if r["linearizations"] == "1") / len(counted))
            if counted else None}
    return out


def candidates(records: list[dict[str, Any]], rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """search-v0.1's task rule on this slice, with the corrected step counts: theorems whose proof is one `by`
    block of 3 to 20 steps, not generated, in (module, line) order."""
    by_key = {(r["module"], r["declaration"]): r for r in rows}
    out = []
    for record in records:
        row = by_key[(record["module"], record["declaration"])]
        roots = [n for n in record["nodes"] if n["parent"] is None]
        if not (v1.MIN_STEPS <= row["steps"] <= v1.MAX_STEPS) or v1.generated(record["declaration"]):
            continue
        if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic"):
            continue
        out.append({"module": record["module"], "declaration": record["declaration"], "line": roots[0]["line"],
                    "steps": row["steps"], "structure": row["structure"], "linearizations": row["linearizations"]})
    return sorted(out, key=lambda t: (t["module"], t["line"]))


def draw(candidates_: list[dict[str, Any]]) -> list[dict[str, Any]]:
    order = list(range(len(candidates_)))
    random.Random(SEED).shuffle(order)
    return [candidates_[i] | {"draw": rank} for rank, i in enumerate(order[:SEARCH_TASKS])]


def registration_payload() -> dict[str, Any]:
    selected = [name for name, _ in modules()]
    first = [name for name, _ in slice_.modules()]
    if set(selected) & set(first):
        raise SystemExit("the holdout slice overlaps the first slice")
    recount = json.loads(RECOUNT.read_text(encoding="utf-8"))
    return {
        "experiment": "holdout-v0.1",
        "question": "do the counts of the Mathlib slice and the search measures of search-v0.3 hold on Mathlib "
                    "modules that no experiment has seen",
        "corpus": {"package": "mathlib", "revision": slice_.dependency_revision(),
                   "population": len(slice_.population()),
                   "populationRule": "as linearizations-mathlib-v0.1: every Mathlib module outside "
                                     + ", ".join(slice_.EXCLUDED_DIRECTORIES) + ", sorted by name",
                   "rule": f"every {slice_.STRIDE}th module starting at index {OFFSET} (0-based); the first slice "
                           "starts at index 0, so the two are disjoint",
                   "modules": len(selected), "moduleList": selected,
                   "scope": "every declaration with at least one tactic step in every selected module"},
        "derivation": "the corrected step derivation of scripts/count_linearizations_v2.py (recount-v0.1)",
        "exclusionPolicy": "as linearizations-mathlib-v0.1: a non-forest graph with more than 22 steps has no "
                           "count; a module that fails to elaborate is dropped and listed",
        "references": {"recountSummarySha256": sha256_file(RECOUNT),
                       "libraryStructureMedians": {n: e["structure"]["median"] if e["structure"] else None
                                                   for n, e in recount["library"]["strata"].items()},
                       "firstSliceStructureMedians": {n: e["structure"]["median"] if e["structure"] else None
                                                      for n, e in recount["slice"]["strata"].items()}},
        "search": {"tasks": f"search-v0.1's rule on this slice with the corrected step counts (one `by` block of "
                            f"{v1.MIN_STEPS} to {v1.MAX_STEPS} steps, not generated), in (module, line) order, "
                            f"shuffled with random.Random({SEED}); the first {SEARCH_TASKS}",
                   "searches": "search-v0.3's whole-state and AND-OR searches with the standard menu at "
                               f"{BUDGET} expansions, as implemented in search_keys.py (goal keys recorded; the "
                               "AND-OR search sets a goal's proof once)",
                   "execution": "every (task, search) unit in a fresh REPL, resumable; an exception becomes an "
                                "error row, run again on the next resume"},
        "hypotheses": {
            "H34": f"in every stratum of at least 6 steps with at least {MINIMUM_STRATUM} counted proofs, the median "
                   "number of linearizations is at least 10 (H13 of the first slice)",
            "H35": f"in every such stratum, the median structure index is within {TOLERANCE} of ProofNet-IR's "
                   "recounted median (H12 of the first slice)",
            "H36": f"in every such stratum, the median structure index is within {TOLERANCE} of the first slice's "
                   "recounted median",
            "H37": f"the whole-state search's order-duplicate fraction is below {ORDER_CEILING:.0%} (H22 of "
                   "search-v0.3)",
            "H38": f"its goal-duplicate fraction is at least {SHARING_RATIO:g} times its order-duplicate fraction "
                   "(H23 of search-v0.3)",
            "H39": "the AND-OR search proves at least as many tasks as the whole-state search (H24 of search-v0.3)"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on this slice: no module of it had been extracted or searched",
        "resultsSeenBeforeRegistration": "the first slice's counts and recount, and search-v0.3's progress log; "
                                         "search-v0.3's summary had not been computed",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def summarize_counts(rows: list[dict[str, Any]], failures: list[dict[str, str]]) -> dict[str, Any]:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    library = prereg["references"]["libraryStructureMedians"]
    first = prereg["references"]["firstSliceStructureMedians"]
    per = strata(rows)
    tested = [n for n, (low, _) in zip(per, STRATA) if low >= 6 and per[n]["counted"] >= MINIMUM_STRATUM]

    def within(reference: dict[str, float | None]) -> bool:
        return all(per[n]["structure"] and reference[n] is not None
                   and abs(per[n]["structure"]["median"] - reference[n]) <= TOLERANCE for n in tested)
    return {"proofs": len(rows), "counted": sum(1 for r in rows if r["linearizations"] is not None),
            "modulesExtracted": len({r["module"] for r in rows}), "modulesFailed": failures,
            "stepsQuartiles": quantiles([r["steps"] for r in rows]), "strata": per, "testedStrata": tested,
            "hypotheses": {"H34": {"supported": bool(tested) and all(
                               int(per[n]["linearizations"]["median"]) >= 10 for n in tested)},
                           "H35": {"supported": bool(tested) and within(library)},
                           "H36": {"supported": bool(tested) and within(first)}}}


def summarize_searches(search_rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    by_unit = {(r["module"], r["declaration"], r["search"]): r for r in search_rows}
    units_ = {s: [by_unit.get((t["module"], t["declaration"], s)) for t in tasks] for s in ("whole", "andor")}
    ran = {s: [u for u in units_[s] if u is not None and "result" in u] for s in units_}
    proved = {s: {u["declaration"] for u in ran[s] if u["result"]["proof"]} for s in ran}
    whole_only, andor_only = proved["whole"] - proved["andor"], proved["andor"] - proved["whole"]
    keyed = {key: rsk.fractions(ran["whole"], key) | {"bootstrap": rsk.bootstrap(ran["whole"], key)}
             for key in rsk.KEYS}
    default = keyed["default"]
    return {"tasks": len(tasks),
            "constructed": {s: sum(1 for u in units_[s] if u is not None and u.get("constructed")) for s in units_},
            "abandoned": {s: sum(1 for u in units_[s] if u is not None and u.get("abandoned")) for s in units_},
            "errors": {s: sum(1 for u in units_[s] if u is not None and u.get("error")) for s in units_},
            "missing": {s: sum(1 for u in units_[s] if u is None) for s in units_},
            "whole": keyed, "proved": {s: len(v) for s, v in proved.items()},
            "andor": {"expansions": sum(len(u["result"]["expansions"]) for u in ran["andor"]),
                      "entangled": sum(u["result"].get("entangled", 0) for u in ran["andor"])},
            "discordant": {"wholeOnly": len(whole_only), "andorOnly": len(andor_only),
                           "signTestTwoSided": None if not whole_only | andor_only else
                           min(1.0, 2 * min(rsk.sign_test_upper(len(andor_only), len(whole_only) + len(andor_only)),
                                            rsk.sign_test_upper(len(whole_only), len(whole_only) + len(andor_only))))},
            "hypotheses": {
                "H37": {"supported": default["orderFraction"] is not None and default["orderFraction"] < ORDER_CEILING},
                "H38": {"supported": default["orderFraction"] is not None
                        and default["goalFraction"] >= SHARING_RATIO * default["orderFraction"]},
                "H39": {"supported": bool(ran["whole"]) and len(proved["andor"]) >= len(proved["whole"])}}}


def run_searches(tasks: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if SEARCHES.exists():
        rows = [json.loads(l) for l in SEARCHES.read_text(encoding="utf-8").splitlines() if l.strip()]
    done = {(r["module"], r["declaration"], r["search"]) for r in rows if not r.get("error")}
    lock = threading.Lock()

    def guarded(task: dict[str, Any], search: str) -> dict[str, Any]:
        started = time.monotonic()
        try:
            row = rsk.run_unit(task, "keys", search, BUDGET)
            return row | {"arm": "holdout"}
        except Exception as error:  # noqa: BLE001
            return {"module": task["module"], "declaration": task["declaration"], "arm": "holdout", "search": search,
                    "constructed": None, "error": f"{type(error).__name__}: {error}"[:300],
                    "seconds": round(time.monotonic() - started, 1)}

    def record(row: dict[str, Any]) -> None:
        with lock:
            rows.append(row)
            with SEARCHES.open("a", encoding="utf-8", newline="\n") as handle:
                handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
            result = row.get("result") or {}
            print(json.dumps({"unit": [row["declaration"], row["search"]],
                              "expansions": len(result.get("expansions", [])), "proof": bool(result.get("proof")),
                              "error": row.get("error"), "at": time.strftime("%H:%M:%S")}), flush=True)

    todo = [(t, s) for t in tasks for s in ("whole", "andor") if (t["module"], t["declaration"], s) not in done]
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(guarded, t, s) for t, s in todo]
        for future in concurrent.futures.as_completed(futures):
            try:
                record(future.result())
            except Exception as error:  # noqa: BLE001
                print(json.dumps({"recordError": f"{type(error).__name__}: {error}"[:300]}), flush=True)
    latest = {(r["module"], r["declaration"], r["search"]): r for r in rows}
    order = {(t["module"], t["declaration"], s): i for i, (t, s) in
             enumerate((t, s) for t in tasks for s in ("whole", "andor"))}
    return sorted(latest.values(), key=lambda r: order[(r["module"], r["declaration"], r["search"])])


def write_summary(counts: dict[str, Any], searches: dict[str, Any] | None) -> dict[str, Any]:
    summary = {"experiment": "holdout-v0.1", "preregistrationSha256": sha256_file(PREREG),
               "counts": counts, "searches": searches,
               "hypotheses": counts["hypotheses"] | (searches["hypotheses"] if searches else {}),
               "extractionSha256": sha256_file(EXTRACTION), "countsSha256": sha256_file(COUNTS),
               "tasksSha256": sha256_file(TASKS),
               "searchesSha256": sha256_file(SEARCHES) if SEARCHES.exists() else None}
    write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
    lines = ["# Holdout slice (holdout v0.1)", "",
             "A second Mathlib slice, disjoint from the first; frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Modules extracted: {counts['modulesExtracted']}; dropped: {len(counts['modulesFailed'])}. Proofs: "
             f"{counts['proofs']}; counted: {counts['counted']}.", "",
             "| Stratum | Proofs | Median L | Median index | Single order |", "| --- | ---: | ---: | ---: | ---: |"]
    for name, e in counts["strata"].items():
        lin = e["linearizations"]
        lines.append(f"| {name} | {e['proofs']} | {base.format_count(lin['median']) if lin else 'n/a'} | "
                     f"{'n/a' if not e['structure'] else format(e['structure']['median'], '.3f')} | "
                     f"{'n/a' if e['fractionSingleOrder'] is None else format(e['fractionSingleOrder'], '.1%')} |")
    lines += ["", f"Strata tested: {', '.join(counts['testedStrata'])}.", ""]
    if searches:
        d = searches["whole"]["default"]
        lines += [f"Searches on {searches['tasks']} tasks: whole-state order duplicates {d['orderDuplicates']} of "
                  f"{d['expansions']} ({rsk.fmt(d['orderFraction'], '.1%')}), goal duplicates {d['goalDuplicates']} "
                  f"({rsk.fmt(d['goalFraction'], '.1%')}); proved: {searches['proved']}; discordant: "
                  f"{searches['discordant']}; entangled candidates: {searches['andor']['entangled']}.", ""]
    lines += ["## Hypotheses", ""] + [f"- {k}: supported: {v['supported']}." for k, v in summary["hypotheses"].items()]
    write_lf(REPORT, "\n".join(lines) + "\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--extract", action="store_true")
    mode.add_argument("--search", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    if args.register:
        if EXTRACTION.exists() or SEARCHES.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload()
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {payload['corpus']['modules']} modules: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["moduleList"] != [name for name, _ in modules()]:
        raise SystemExit("module list changed since registration")
    for name in ("extractor", "extractorMain", "counter", "keys", "harness", "repl", "keysRunner"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")

    if args.extract:
        records, failures = extract(modules(), args.workers)
        write_gz(EXTRACTION, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records))
        write_lf(FAILURES, json.dumps(failures, indent=1) + "\n")
        rows = count(records)
        write_lf(COUNTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        tasks = draw(candidates(records, rows))
        write_lf(TASKS, json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
        summary = write_summary(summarize_counts(rows, failures), None)
        print(json.dumps({"holdout-extract": summary["hypotheses"], "proofs": summary["counts"]["proofs"],
                          "tasks": len(tasks)}))
        return 0

    records = read_gz_lines(EXTRACTION)
    rows = [json.loads(l) for l in COUNTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    failures = json.loads(FAILURES.read_text(encoding="utf-8"))
    tasks = json.loads(TASKS.read_text(encoding="utf-8"))

    if args.search:
        search_rows = run_searches(tasks, args.workers)
        write_lf(SEARCHES, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n"
                                   for r in search_rows))
        summary = write_summary(summarize_counts(rows, failures), summarize_searches(search_rows, tasks))
        print(json.dumps({"holdout-search": summary["hypotheses"]}))
        return 0

    recounted = count(records)
    if len(recounted) != len(rows) or not all(same_row(a, b) for a, b in zip(recounted, rows)):
        raise SystemExit("the committed counts do not follow from the committed extraction")
    if draw(candidates(records, rows)) != tasks:
        raise SystemExit("the committed tasks do not follow from the committed counts")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    search_rows = [json.loads(l) for l in SEARCHES.read_text(encoding="utf-8").splitlines() if l.strip()] \
        if SEARCHES.exists() else None
    if summary["counts"] != json.loads(json.dumps(summarize_counts(rows, failures))) or \
            (search_rows is not None and summary["searches"] != json.loads(json.dumps(
                summarize_searches(search_rows, tasks)))):
        raise SystemExit("the committed summary does not follow from the committed rows")
    if summary["preregistrationSha256"] != sha256_file(PREREG) or summary["extractionSha256"] != sha256_file(EXTRACTION):
        raise SystemExit("summary hashes do not match the committed files")
    print(f"holdout-check-ok: proofs={len(rows)} searches={len(search_rows or [])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
