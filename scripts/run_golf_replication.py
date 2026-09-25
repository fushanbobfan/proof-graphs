#!/usr/bin/env python3
"""Golf v0.2: the golf findings replicated on golf pairs no experiment has seen.

  python scripts/run_golf_replication.py --register
  python scripts/run_golf_replication.py --run [--workers 4]
  python scripts/run_golf_replication.py --check-committed

golf-v0.1 mined the golf commits between v4.29.0 and v4.32.0. Under the corrected step derivation, its pairs
showed that a golfed proof branches more than its predecessor once length is accounted for (H28r of
recount-v0.1), a difference that golf-structure-v0.1's registered test had not established and that was seen
before H28r was registered. This experiment mines the golf commits of the three releases before (v4.26.0 to
v4.29.0), keeps the pairs whose golfed text is still verbatim at v4.32.0, elaborates both sides there exactly as
golf-v0.1 does, counts under the corrected derivation, and tests the branching difference in the direction
seen, with golf-v0.1's registered tests alongside.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import statistics
import sys
import tempfile
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations_v2 as counter  # noqa: E402
import mine_golf  # noqa: E402
import run_golf as golf  # noqa: E402
import run_golf_structure as structure  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import quantiles, read_gz_lines, sha256_file, write_gz, write_lf  # noqa: E402

structure.counter = counter  # depth, width, branching, and the slice reference under the corrected derivation

ROOT = golf.ROOT
EXPERIMENT = ROOT / "experiments" / "golf-v0.2"
PREREG = EXPERIMENT / "preregistration.json"
PAIRS = EXPERIMENT / "pairs.jsonl.gz"
EXTRACTION = EXPERIMENT / "extraction.jsonl.gz"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
LOWER, MIDDLE = "v4.26.0", "v4.29.0"  # the commits mined; the golfed text must survive at golf.UPPER (v4.32.0)
IMPLEMENTATIONS = {
    "extractor": golf.IMPLEMENTATIONS["extractor"], "extractorMain": golf.IMPLEMENTATIONS["extractorMain"],
    "counter": ROOT / "scripts" / "count_linearizations_v2.py", "miner": ROOT / "scripts" / "mine_golf.py",
    "golfRunner": ROOT / "scripts" / "run_golf.py", "structureRunner": ROOT / "scripts" / "run_golf_structure.py",
    "runner": Path(__file__).resolve(),
}
ALPHA = 0.05
MIN_STEPS = structure.MIN_STEPS
POOL_FROM = structure.POOL_FROM
QUANTITIES = structure.QUANTITIES


def mine() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """mine_golf.mine, with the commits taken from LOWER..MIDDLE and survival judged at golf.UPPER; pairs of a
    declaration that golf-v0.1 also paired are dropped."""
    commits = mine_golf.golf_commits(golf.MATHLIB, LOWER, MIDDLE)
    found: list[dict[str, Any]] = []
    totals: dict[str, int] = {}
    for commit in commits:
        pairs, stats = mine_golf.pairs_of_commit(golf.MATHLIB, commit, golf.UPPER)
        found += pairs
        for key, value in stats.items():
            totals[key] = totals.get(key, 0) + value
    seen: dict[tuple[str, str, int], dict[str, Any]] = {}
    for pair in found:
        key = (pair["file"], pair["name"], pair["occurrence"])
        if key not in seen or pair["date"] > seen[key]["date"]:
            seen[key] = pair
    earlier = {(p["module"], p["name"]) for p in read_gz_lines(golf.PAIRS)}
    kept = [p for p in sorted(seen.values(), key=lambda p: (p["module"], p["upperLine"]))
            if (p["module"], p["name"]) not in earlier]
    totals |= {"commits": len(commits), "overlapWithGolfV01": len(seen) - len(kept), "pairs": len(kept),
               "commitsWithPairs": len({p["commit"] for p in kept})}
    return kept, totals


def registration_payload(pairs: list[dict[str, Any]], totals: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "golf-v0.2",
        "question": "do the golf findings, and above all the branching difference seen only after the correction "
                    "of the step derivation, hold on golf pairs that no experiment has seen",
        "corpus": {"repository": "Mathlib", "revision": golf.mathlib_revision(), "window": [LOWER, MIDDLE],
                   "survivalTag": golf.UPPER,
                   "rule": "every golf pair of scripts/mine_golf.py from the first-parent commits between the window's "
                           "tags whose subject contains 'golf', with the golfed text verbatim and unique in the file "
                           f"at {golf.UPPER}; a declaration golfed twice keeps its last golf; pairs of a declaration "
                           "that golf-v0.1 paired are dropped",
                   "mining": totals, "pairsSha256": sha256_file(PAIRS)},
        "elaboration": "as golf-v0.1: both sides elaborated from the file at v4.32.0 with Mathlib's two options, the "
                       "predecessor spliced in for the golfed text; a pair counts when both sides elaborate",
        "derivation": "the corrected step derivation of scripts/count_linearizations_v2.py",
        "adjustment": f"as golf-structure-v0.1: each quantity minus the median of that quantity among the first "
                      f"Mathlib slice's proofs with the same number of steps (pooled from {POOL_FROM}), recomputed "
                      "under the corrected derivation, as in H28r of recount-v0.1",
        "hypotheses": {
            "H40": f"among pairs with at least {MIN_STEPS} steps on both sides whose length-adjusted branching "
                   "differs, the golfed proof has the higher adjusted branching in more than half (one-sided sign "
                   f"test, alpha {ALPHA:g})",
            "H41": "among pairs whose step counts differ, the golfed proof has fewer steps in more than half "
                   f"(one-sided sign test, alpha {ALPHA:g}; H20 of golf-v0.1)",
            "H42": f"among pairs with at least {MIN_STEPS} steps on both sides whose structure indices differ, the "
                   f"golfed proof has the lower index in more than half (one-sided sign test, alpha {ALPHA:g}; H21)",
            "H43": f"among pairs with at least {MIN_STEPS} steps on both sides whose length-adjusted structure "
                   "indices differ, a two-sided sign test does not reject equal proportions at alpha "
                   f"{ALPHA:g} (golf-v0.1's exploratory length analysis, registered)",
            "H44": "for at least one of depth, width, and branching, the adjusted value differs (Holm-corrected "
                   f"two-sided sign tests, family-wise alpha {ALPHA:g}; H28r)"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the numbers of golf commits and surviving pairs were computed for "
                                               "the windows v4.22.0, v4.24.0, and v4.26.0 to v4.29.0 (373, 233, and "
                                               "122 commits; 1,166, 907, and 511 pairs) to choose a window of three "
                                               "releases, as golf-v0.1's; no pair was elaborated or counted",
        "resultsSeenBeforeRegistration": "golf-v0.1, golf-structure-v0.1, and recount-v0.1 on golf-v0.1's pairs",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def pair_results(pairs: list[dict[str, Any]], extraction: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """golf.pair_results, counted under the corrected derivation."""
    by_key = {(row["pair"], row["side"]): row for row in extraction}
    out = []
    for pair in pairs:
        row = {"pair": pair["id"], "commit": pair["commit"], "module": pair["module"], "name": pair["name"]}
        for side in ("before", "after"):
            extracted = by_key[(pair["id"], side)]
            if not extracted["ok"]:
                row[side] = {"status": "elaboration errors"}
            elif extracted["record"] is None:
                row[side] = {"status": "no tactic record", "steps": 0}
            else:
                c = counter.analyse(extracted["record"])
                q = structure.quantities(extracted["record"])
                row[side] = {"status": "ok", "steps": c["steps"], "linearizations": c["linearizations"],
                             "structure": c["structure"], "forest": c["forest"], "roots": c["roots"],
                             "depth": q["depth"], "width": q["width"], "branching": q["branching"]}
        both = row["before"]["status"] != "elaboration errors" and row["after"]["status"] != "elaboration errors"
        row["status"] = "ok" if both else ("before fails" if row["after"]["status"] != "elaboration errors"
                                           else "original fails")
        out.append(row)
    return out


def sign_upper(k: int, n: int) -> float | None:
    return None if n == 0 else sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def sign_two_sided(k: int, n: int) -> float | None:
    return None if n == 0 else min(1.0, 2 * sum(math.comb(n, i) for i in range(max(k, n - k), n + 1)) / 2 ** n)


def summarize(results: list[dict[str, Any]]) -> dict[str, Any]:
    ok = [r for r in results if r["status"] == "ok"]
    differ = [r for r in ok if r["before"]["steps"] != r["after"]["steps"]]
    fewer = sum(1 for r in differ if r["after"]["steps"] < r["before"]["steps"])
    eligible = [r for r in ok if r["before"]["steps"] >= MIN_STEPS and r["after"]["steps"] >= MIN_STEPS]
    ref = structure.references()
    sigma_ref: dict[int, list[float]] = defaultdict(list)
    for r in (json.loads(l) for l in (ROOT / "experiments" / "recount-v0.1" / "slice.jsonl")
              .read_text(encoding="utf-8").splitlines() if l.strip()):
        if r["structure"] is not None and r["steps"] >= MIN_STEPS:
            sigma_ref[min(r["steps"], POOL_FROM)].append(r["structure"])
    sigma_median = {n: statistics.median(v) for n, v in sigma_ref.items()}

    def adjusted(side: dict[str, Any], name: str) -> float | None:
        n = min(side["steps"], POOL_FROM)
        if name == "structure":
            return None if side["structure"] is None or n not in sigma_median else side["structure"] - sigma_median[n]
        return None if side[name] is None or n not in ref[name] else side[name] - ref[name][n]

    sdiff = [r for r in eligible if r["before"]["structure"] is not None and r["after"]["structure"] is not None
             and r["before"]["structure"] != r["after"]["structure"]]
    lower = sum(1 for r in sdiff if r["after"]["structure"] < r["before"]["structure"])
    adj_sigma = [(adjusted(r["after"], "structure"), adjusted(r["before"], "structure")) for r in eligible]
    adj_sigma = [(a, b) for a, b in adj_sigma if a is not None and b is not None and a != b]
    adj_sigma_lower = sum(1 for a, b in adj_sigma if a < b)
    tests = {}
    for name in QUANTITIES:
        pairs_ = [(adjusted(r["after"], name), adjusted(r["before"], name)) for r in eligible]
        pairs_ = [(a, b) for a, b in pairs_ if a is not None and b is not None and a != b]
        golfed_lower = sum(1 for a, b in pairs_ if a < b)
        raw = [r for r in eligible if r["before"][name] is not None and r["after"][name] is not None
               and r["before"][name] != r["after"][name]]
        tests[name] = {"pairs": len(pairs_), "golfedLower": golfed_lower,
                       "pValue": sign_two_sided(golfed_lower, len(pairs_)),
                       "unadjusted": {"pairs": len(raw),
                                      "golfedLower": sum(1 for r in raw if r["after"][name] < r["before"][name])}}
    ordered = sorted(QUANTITIES, key=lambda q: (tests[q]["pValue"] is None, tests[q]["pValue"] or 1.0))
    running = 0.0
    for rank, name in enumerate(ordered):
        p = tests[name]["pValue"]
        if p is None:
            tests[name]["holm"] = None
            continue
        running = max(running, min(1.0, (len(QUANTITIES) - rank) * p))
        tests[name]["holm"] = running
    b = tests["branching"]
    p40 = sign_upper(b["pairs"] - b["golfedLower"], b["pairs"])
    p41 = sign_upper(fewer, len(differ))
    p42 = sign_upper(lower, len(sdiff))
    p43 = sign_two_sided(adj_sigma_lower, len(adj_sigma))
    return {
        "experiment": "golf-v0.2", "preregistrationSha256": sha256_file(PREREG), "pairs": len(results),
        "ok": len(ok), "commits": len({r["commit"] for r in ok}),
        "excluded": {s: sum(1 for r in results if r["status"] == s) for s in ("before fails", "original fails")},
        "steps": {"before": quantiles([r["before"]["steps"] for r in ok]),
                  "after": quantiles([r["after"]["steps"] for r in ok])},
        "eligible": len(eligible),
        "H40": {"pairs": b["pairs"], "golfedHigher": b["pairs"] - b["golfedLower"], "pValue": p40,
                "supported": p40 is not None and p40 < ALPHA},
        "H41": {"pairsDiffering": len(differ), "golfedFewer": fewer, "pValue": p41,
                "supported": p41 is not None and p41 < ALPHA},
        "H42": {"pairsDiffering": len(sdiff), "golfedLower": lower, "pValue": p42,
                "supported": p42 is not None and p42 < ALPHA},
        "H43": {"pairs": len(adj_sigma), "golfedLower": adj_sigma_lower, "pValue": p43,
                "supported": p43 is not None and p43 >= ALPHA},
        "structureTests": tests,
        "hypotheses": {"H40": {"supported": p40 is not None and p40 < ALPHA},
                       "H41": {"supported": p41 is not None and p41 < ALPHA},
                       "H42": {"supported": p42 is not None and p42 < ALPHA},
                       "H43": {"supported": p43 is not None and p43 >= ALPHA},
                       "H44": {"supported": any(t["holm"] is not None and t["holm"] < ALPHA for t in tests.values())}},
        "extractionSha256": sha256_file(EXTRACTION), "resultsSha256": sha256_file(RESULTS),
        "pairsSha256": sha256_file(PAIRS)}


def write_report(summary: dict[str, Any]) -> None:
    s, t = summary, summary["structureTests"]
    lines = ["# Golf pairs from v4.26.0 to v4.29.0 (golf v0.2)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + s["preregistrationSha256"] + "`).", "",
             f"Pairs: {s['pairs']}; both sides elaborate: {s['ok']} from {s['commits']} commits; excluded: "
             f"{s['excluded']}. Pairs with at least {MIN_STEPS} steps on both sides: {s['eligible']}.", "",
             f"- H40 (golfed branches more after length adjustment): {s['H40']['golfedHigher']} of "
             f"{s['H40']['pairs']}, one-sided p = {s['H40']['pValue']}; supported: {s['H40']['supported']}.",
             f"- H41 (golfed has fewer steps): {s['H41']['golfedFewer']} of {s['H41']['pairsDiffering']}, "
             f"p = {s['H41']['pValue']}; supported: {s['H41']['supported']}.",
             f"- H42 (golfed has the lower structure index): {s['H42']['golfedLower']} of "
             f"{s['H42']['pairsDiffering']}, p = {s['H42']['pValue']}; supported: {s['H42']['supported']}.",
             f"- H43 (length-adjusted structure index not different): golfed lower in {s['H43']['golfedLower']} of "
             f"{s['H43']['pairs']}, two-sided p = {s['H43']['pValue']}; supported: {s['H43']['supported']}.",
             f"- H44 (some adjusted quantity differs, Holm): supported: {s['hypotheses']['H44']['supported']}.", "",
             "| Quantity | Adjusted: differing pairs, golfed lower, p (Holm) | Unadjusted: differing, golfed lower |",
             "| --- | --- | --- |"]
    for name in QUANTITIES:
        q = t[name]
        lines.append(f"| {name} | {q['pairs']}, {q['golfedLower']}, {q['pValue']} ({q['holm']}) | "
                     f"{q['unadjusted']['pairs']}, {q['unadjusted']['golfedLower']} |")
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    if args.register:
        if RESULTS.exists() or EXTRACTION.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        pairs, totals = mine()
        for index, pair in enumerate(pairs):
            pair["id"] = f"q{index:03d}"
        write_gz(PAIRS, "".join(json.dumps(p, ensure_ascii=False) + "\n" for p in pairs))
        payload = registration_payload(pairs, totals)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(pairs)} pairs from {totals['commitsWithPairs']} commits: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["pairsSha256"] != sha256_file(PAIRS):
        raise SystemExit("pairs changed since registration")
    for name in ("extractor", "extractorMain", "counter", "golfRunner", "structureRunner"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    pairs = read_gz_lines(PAIRS)
    by_module: dict[str, list[dict[str, Any]]] = {}
    for pair in pairs:
        by_module.setdefault(pair["module"], []).append(pair)

    if args.run:
        extraction: list[dict[str, Any]] = []
        with tempfile.TemporaryDirectory(prefix="golf2-") as scratch, \
                concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(golf.extract_module, m, ps, Path(scratch)): m for m, ps in by_module.items()}
            for done, future in enumerate(concurrent.futures.as_completed(futures), 1):
                rows = future.result()
                extraction += rows
                print(f"{done}/{len(futures)} {futures[future]}: {sum(1 for r in rows if r['ok'])}/{len(rows)} "
                      f"sides elaborated at {time.strftime('%H:%M:%S')}", flush=True)
        order = {(p["id"], side): i for i, (p, side) in enumerate((p, s) for p in pairs for s in ("after", "before"))}
        extraction.sort(key=lambda r: order[(r["pair"], r["side"])])
        write_gz(EXTRACTION, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n"
                                     for r in extraction))
        results = pair_results(pairs, extraction)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in results))
        summary = summarize(results)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"golf-v0.2-run": summary["hypotheses"], "ok": summary["ok"]}))
        return 0

    extraction = read_gz_lines(EXTRACTION)
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if json.loads(json.dumps(pair_results(pairs, extraction))) != committed:
        raise SystemExit("the committed results do not follow from the committed extraction")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if json.loads(json.dumps(summarize(committed))) != summary:
        raise SystemExit("the committed summary does not follow from the committed results")
    print(f"golf-v0.2-check-ok: pairs={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
