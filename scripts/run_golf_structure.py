#!/usr/bin/env python3
"""Golf structure v0.1: graph quantities of golfed proofs beyond length. Register, run, check.

  python scripts/run_golf_structure.py --register
  python scripts/run_golf_structure.py --run
  python scripts/run_golf_structure.py --check-committed

golf-v0.1 found that the golfed proof's lower structure index follows its
shorter length. This experiment asks, on the same pairs and the same committed
extraction, whether three other quantities of the goal-origin graph differ once
length is accounted for: depth (the most steps on one chain of dependencies),
width (the most steps at one depth), and branching (the mean number of
dependent steps of a step that has any). Each quantity is adjusted for length
by subtracting the median of that quantity among the Mathlib slice's proofs
with the same number of steps (pooled from 30 steps on).
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
import run_golf as golf  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import read_gz_lines, sha256_file, write_lf  # noqa: E402

ROOT = golf.ROOT
EXPERIMENT = ROOT / "experiments" / "golf-structure-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations.py", "runner": Path(__file__).resolve()}
QUANTITIES = ("depth", "width", "branching")
MIN_STEPS = 3
POOL_FROM = 30
ALPHA = 0.05


def quantities(record: dict[str, Any]) -> dict[str, Any]:
    steps = counter.derive_steps(record["nodes"])
    parents = counter.dependency_graph(steps)
    n = len(steps)
    children: list[list[int]] = [[] for _ in range(n)]
    for child, ps in enumerate(parents):
        for p in ps:
            children[p].append(child)
    level: dict[int, int] = {}

    def depth_of(i: int) -> int:  # 1 for a step with no parent; parents precede nothing in general, so memoize
        if i not in level:
            level[i] = 1 + max((depth_of(p) for p in parents[i]), default=0)
        return level[i]

    sys.setrecursionlimit(max(10000, 4 * n))
    depths = [depth_of(i) for i in range(n)]
    per_level: dict[int, int] = defaultdict(int)
    for d in depths:
        per_level[d] += 1
    internal = [len(c) for c in children if c]
    return {"steps": n, "depth": max(depths, default=0), "width": max(per_level.values(), default=0),
            "branching": statistics.mean(internal) if internal else None}


def references() -> dict[str, dict[int, float]]:
    by_n: dict[str, dict[int, list[float]]] = {q: defaultdict(list) for q in QUANTITIES}
    for record in read_gz_lines(slice_.EXTRACTION):
        q = quantities(record)
        if q["steps"] < MIN_STEPS:
            continue
        for name in QUANTITIES:
            if q[name] is not None:
                by_n[name][min(q["steps"], POOL_FROM)].append(q[name])
    return {name: {n: statistics.median(v) for n, v in table.items()} for name, table in by_n.items()}


def sign_test_two_sided(k: int, n: int) -> float | None:
    if n == 0:
        return None
    tail = sum(math.comb(n, i) for i in range(max(k, n - k), n + 1)) / 2 ** n
    return min(1.0, 2 * tail)


def registration_payload() -> dict[str, Any]:
    return {
        "experiment": "golf-structure-v0.1",
        "question": "do golfed proofs and their predecessors differ in depth, width, or branching of the goal-origin "
                    "graph once proof length is accounted for",
        "corpus": {"source": "golf-v0.1", "pairsSha256": sha256_file(golf.PAIRS),
                   "extractionSha256": sha256_file(golf.EXTRACTION), "resultsSha256": sha256_file(golf.RESULTS),
                   "rule": f"the pairs of golf-v0.1 that elaborate on both sides and have at least {MIN_STEPS} steps "
                           "on both sides"},
        "quantities": {"depth": "the most steps on one chain of dependencies",
                       "width": "the most steps at one depth, a step's depth being one more than its parents' "
                                "greatest depth",
                       "branching": "the mean number of dependent steps over the steps that have any"},
        "adjustment": {"reference": "linearizations-mathlib-v0.1", "referenceSha256": sha256_file(slice_.EXTRACTION),
                       "rule": f"subtract the median of the quantity among the slice's proofs of at least {MIN_STEPS} "
                               f"steps with the same number of steps, pooled from {POOL_FROM} steps on"},
        "test": "for each quantity, over the pairs whose adjusted values differ, a two-sided sign test of the golfed "
                "proof's adjusted value being lower; Holm's correction over the three quantities",
        "hypotheses": {"H28": f"for at least one of depth, width, and branching, the adjusted value differs between "
                              f"golfed proofs and their predecessors (Holm-corrected two-sided sign test, family-wise "
                              f"alpha {ALPHA})"},
        "disclosure": "the pairs' step counts, ordering counts, and structure indices were computed and reported by "
                      "golf-v0.1, with an exploratory length adjustment of the structure index; depth, width, and "
                      "branching had not been computed for any pair or slice proof before this registration",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def run() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    pair_rows = {r["pair"]: r for r in (json.loads(l) for l in golf.RESULTS.read_text(encoding="utf-8").splitlines()
                                         if l.strip())}
    extraction = {(r["pair"], r["side"]): r for r in read_gz_lines(golf.EXTRACTION)}
    ref = references()
    rows = []
    for pair_id, row in sorted(pair_rows.items()):
        if row["status"] != "ok":
            continue
        sides = {}
        for side in ("before", "after"):
            record = extraction[(pair_id, side)]["record"]
            sides[side] = quantities(record) if record is not None else {"steps": 0}
        if min(sides["before"]["steps"], sides["after"]["steps"]) < MIN_STEPS:
            continue
        out = {"pair": pair_id, "commit": row["commit"], "module": row["module"], "name": row["name"]}
        for side, q in sides.items():
            n = min(q["steps"], POOL_FROM)
            out[side] = q | {f"{name}Adjusted": None if q[name] is None or n not in ref[name] else q[name] - ref[name][n]
                             for name in QUANTITIES}
        rows.append(out)
    tests = {}
    for name in QUANTITIES:
        key = f"{name}Adjusted"
        differing = [r for r in rows if r["before"][key] is not None and r["after"][key] is not None
                     and r["before"][key] != r["after"][key]]
        lower = sum(1 for r in differing if r["after"][key] < r["before"][key])
        raw = [r for r in rows if r["before"][name] is not None and r["after"][name] is not None
               and r["before"][name] != r["after"][name]]
        tests[name] = {"pairs": len(differing), "golfedLower": lower,
                       "pValue": sign_test_two_sided(lower, len(differing)),
                       "unadjusted": {"pairs": len(raw), "golfedLower": sum(1 for r in raw
                                                                            if r["after"][name] < r["before"][name])}}
    ordered = sorted(QUANTITIES, key=lambda q: (tests[q]["pValue"] is None, tests[q]["pValue"] or 1.0))
    holm: dict[str, float | None] = {}
    running = 0.0
    for rank, name in enumerate(ordered):
        p = tests[name]["pValue"]
        if p is None:
            holm[name] = None
            continue
        running = max(running, min(1.0, (len(QUANTITIES) - rank) * p))
        holm[name] = running
    for name in QUANTITIES:
        tests[name]["holm"] = holm[name]
    summary = {"experiment": "golf-structure-v0.1", "preregistrationSha256": sha256_file(PREREG),
               "pairs": len(rows), "tests": tests,
               "hypotheses": {"H28": {"supported": any(h is not None and h < ALPHA for h in holm.values())}}}
    return rows, summary


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Depth, width, and branching of golfed proofs (golf structure v0.1)", "",
             "Quantities, adjustment, test, and hypothesis are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Pairs with at least {MIN_STEPS} steps on both sides: {summary['pairs']}.", "",
             "| Quantity | Pairs whose adjusted values differ | Golfed lower | Two-sided p | Holm | Unadjusted: differ, golfed lower |",
             "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for name, t in summary["tests"].items():
        p = "n/a" if t["pValue"] is None else f"{t['pValue']:.3g}"
        h = "n/a" if t["holm"] is None else f"{t['holm']:.3g}"
        lines.append(f"| {name} | {t['pairs']} | {t['golfedLower']} | {p} | {h} | "
                     f"{t['unadjusted']['pairs']}, {t['unadjusted']['golfedLower']} |")
    lines += ["", f"H28 (some adjusted quantity differs): supported: {summary['hypotheses']['H28']['supported']}."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    for name, path in (("pairsSha256", golf.PAIRS), ("extractionSha256", golf.EXTRACTION),
                       ("resultsSha256", golf.RESULTS)):
        if prereg["corpus"][name] != sha256_file(path):
            raise SystemExit(f"golf-v0.1 {name} changed since registration")
    if prereg["implementationSha256"]["counter"] != sha256_file(IMPLEMENTATIONS["counter"]):
        raise SystemExit("the counter changed since registration")
    rows, summary = run()
    if args.run:
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows))
        summary["resultsSha256"] = sha256_file(RESULTS)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: summary[k] for k in ("pairs", "hypotheses")}))
        return 0
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    stored = json.loads(SUMMARY.read_text(encoding="utf-8"))
    summary["resultsSha256"] = sha256_file(RESULTS)
    if committed != rows or stored != summary:
        raise SystemExit("the committed results do not follow from the golf extraction")
    print(f"golf-structure-check-ok: pairs={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
