#!/usr/bin/env python3
"""Recount v0.1: every committed extraction counted again under the corrected step derivation.

  python scripts/run_recount.py --register
  python scripts/run_recount.py --run
  python scripts/run_recount.py --check-committed

extraction-audit-v0.1 found that the step derivation loses the closing step of
a tactic whose own internal node mentions the goal it closes
(`scripts/count_linearizations_v2.py` states the defect and the correction).
This experiment recounts the three committed extractions (ProofNet-IR v0.10.0,
the Mathlib slice, the golf pairs) with the corrected derivation, re-evaluates
the hypotheses of the experiments that counted them, re-runs the structural
audit and the blind-reconstruction comparison, and writes the corrected
dataset. No module is re-extracted; the extractions are those committed.
"""

from __future__ import annotations

import argparse
import collections
import gzip
import itertools
import json
import math
import statistics
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as old  # noqa: E402
import count_linearizations_v2 as counter  # noqa: E402
import audit_graphs  # noqa: E402
import export_graphs  # noqa: E402
import run_extraction_audit as audit  # noqa: E402
import run_golf as golf  # noqa: E402
import run_golf_structure as golf_structure  # noqa: E402
import run_linearizations as library  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import int_quantiles, quantiles, read_gz_lines, sha256_file, stratum, write_lf  # noqa: E402

for module in (audit_graphs, export_graphs, audit, golf_structure):  # every derived quantity below uses the correction
    module.counter = counter

ROOT = library.ROOT
EXPERIMENT = ROOT / "experiments" / "recount-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
LIBRARY = EXPERIMENT / "library.jsonl"
SLICE = EXPERIMENT / "slice.jsonl"
GOLF = EXPERIMENT / "golf.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
DATASET = ROOT / "datasets" / "proof-graphs-v0.2.jsonl.gz"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations_v2.py",
                   "earlierCounter": ROOT / "scripts" / "count_linearizations.py",
                   "runner": Path(__file__).resolve()}
EXTRACTIONS = {"library": library.EXTRACTION, "slice": slice_.EXTRACTION, "golf": golf.EXTRACTION}
STRATA = library.STRATA
MINIMUM_STRATUM = 30
TOLERANCE = 0.1
ALPHA = 0.05
MIN_STRUCTURE_STEPS = 3


def registration_payload() -> dict[str, Any]:
    return {
        "experiment": "recount-v0.1",
        "question": "what the counts, the hypotheses decided on them, and the dataset are under the corrected step "
                    "derivation",
        "correction": "a node consumes a goal present before it, absent after it, and never present before a later "
                      "node outside its own subtree (previously: any later node); scripts/count_linearizations_v2.py",
        "inputs": {name: sha256_file(path) for name, path in EXTRACTIONS.items()}
                  | {"golfPairs": sha256_file(golf.PAIRS), "golfResults": sha256_file(golf.RESULTS),
                     "auditSample": sha256_file(audit.SAMPLE), "auditReconstructions": sha256_file(audit.RECONSTRUCTIONS)},
        "hypotheses": {
            "H10r": "library: in every stratum of at least 6 steps, the median number of linearizations is at least 10",
            "H11r": "library: in every stratum of at least 6 steps, the median structure index is below 0.5",
            "H12r": f"slice: in every stratum of at least 6 steps with at least {MINIMUM_STRATUM} counted proofs, the "
                    f"median structure index is within {TOLERANCE} of the library's median recounted here",
            "H13r": f"slice: in every stratum of at least 6 steps with at least {MINIMUM_STRATUM} counted proofs, the "
                    "median number of linearizations is at least 10",
            "H20r": "golf: among pairs whose step counts differ, the golfed proof has fewer steps in more than half "
                    "(one-sided sign test, alpha 0.05)",
            "H21r": "golf: among pairs where both proofs have at least 3 steps and their structure indices differ, the "
                    "golfed proof has the lower index in more than half (one-sided sign test, alpha 0.05)",
            "H28r": "golf structure: as H28 of golf-structure-v0.1, with the quantities and the slice reference "
                    "recomputed under the correction",
        },
        "checks": {"C3": "the invariants of scripts/audit_graphs.py hold for every recounted graph",
                   "C4": "the 30 blind reconstructions of extraction-audit-v0.1 agree with the recounted graphs"},
        "outputs": ["per-proof rows for the library and the slice, per-pair rows for golf, as in the earlier "
                    "experiments", "the counts' changes against the earlier rule",
                    "datasets/proof-graphs-v0.2.jsonl.gz, the dataset under the correction"],
        "disclosure": "before this registration the correction was checked on the committed extractions: the "
                      "invariants hold for all 7,285 graphs (3,307 brute-forced), the six fixtures keep their "
                      "counts, all 30 blind reconstructions agree, and the numbers of graphs whose steps or counts "
                      "change were seen (steps: 838 library, 114 slice, 40 golf; counts: 774, 54, 34); no stratum, "
                      "quantile, median, or hypothesis under the correction had been computed",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


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


def changes(records: list[dict[str, Any]], rows: list[dict[str, Any]]) -> dict[str, int]:
    before = [old.analyse(r) for r in records]
    return {"stepsChanged": sum(1 for a, b in zip(before, rows) if a["steps"] != b["steps"]),
            "countChanged": sum(1 for a, b in zip(before, rows) if a["linearizations"] != b["linearizations"])}


def golf_rows() -> list[dict[str, Any]]:
    extraction = {(r["pair"], r["side"]): r for r in read_gz_lines(golf.EXTRACTION)}
    out = []
    for row in (json.loads(l) for l in golf.RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()):
        new = {k: row[k] for k in ("pair", "commit", "module", "name", "status")}
        for side in ("before", "after"):
            extracted = extraction[(row["pair"], side)]
            if not extracted["ok"]:
                new[side] = {"status": "elaboration errors"}
            elif extracted["record"] is None:
                new[side] = {"status": "no tactic record", "steps": 0}
            else:
                a = counter.analyse(extracted["record"])
                new[side] = {"status": "ok", "steps": a["steps"], "linearizations": a["linearizations"],
                             "structure": a["structure"], "forest": a["forest"], "roots": a["roots"]}
        out.append(new)
    return out


def golf_tests(rows: list[dict[str, Any]], slice_rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok = [r for r in rows if r["status"] == "ok"]
    differ = [r for r in ok if r["before"]["steps"] != r["after"]["steps"]]
    fewer = sum(1 for r in differ if r["after"]["steps"] < r["before"]["steps"])
    eligible = [r for r in ok if r["before"]["steps"] >= MIN_STRUCTURE_STEPS and r["after"]["steps"] >= MIN_STRUCTURE_STEPS
                and r["before"].get("structure") is not None and r["after"].get("structure") is not None]
    sdiff = [r for r in eligible if r["before"]["structure"] != r["after"]["structure"]]
    lower = sum(1 for r in sdiff if r["after"]["structure"] < r["before"]["structure"])
    by_n: dict[int, list[float]] = collections.defaultdict(list)
    for r in slice_rows:
        if r["structure"] is not None and r["steps"] >= MIN_STRUCTURE_STEPS:
            by_n[min(r["steps"], 30)].append(r["structure"])
    expected = {n: statistics.median(v) for n, v in by_n.items()}
    resid = [(r["after"]["structure"] - expected[min(r["after"]["steps"], 30)],
              r["before"]["structure"] - expected[min(r["before"]["steps"], 30)]) for r in eligible]
    changed = [(a, b) for a, b in resid if a != b]
    adj_lower = sum(1 for a, b in changed if a < b)
    shorter = [r for r in sdiff if r["after"]["steps"] < r["before"]["steps"]]
    longer = [r for r in sdiff if r["after"]["steps"] > r["before"]["steps"]]
    p20 = golf.sign_test_upper(fewer, len(differ))
    p21 = golf.sign_test_upper(lower, len(sdiff))
    return {"ok": len(ok),
            "steps": {"before": quantiles([r["before"]["steps"] for r in ok]),
                      "after": quantiles([r["after"]["steps"] for r in ok])},
            "H20r": {"pairsDiffering": len(differ), "golfedFewer": fewer, "pValue": p20,
                     "supported": p20 is not None and p20 < ALPHA},
            "H21r": {"eligible": len(eligible), "pairsDiffering": len(sdiff), "golfedLower": lower, "pValue": p21,
                     "supported": p21 is not None and p21 < ALPHA,
                     "structureBefore": quantiles([r["before"]["structure"] for r in eligible]),
                     "structureAfter": quantiles([r["after"]["structure"] for r in eligible])},
            "lengthAdjusted": {"note": "the exploratory analysis of golf-v0.1, repeated on the recount",
                               "shorter": [len(shorter), sum(1 for r in shorter if r["after"]["structure"] < r["before"]["structure"])],
                               "longer": [len(longer), sum(1 for r in longer if r["after"]["structure"] > r["before"]["structure"])],
                               "equalLength": sum(1 for r in sdiff if r["after"]["steps"] == r["before"]["steps"]),
                               "pairs": len(changed), "golfedLower": adj_lower,
                               "pValue": golf.sign_test_upper(adj_lower, len(changed))}}


def invariants() -> dict[str, int]:
    violating = brute = graphs = 0
    for path in audit_graphs.DEFAULT:
        for record in audit_graphs.records_of(path):
            found, forced = audit_graphs.violations(record)
            graphs += 1
            brute += forced
            violating += bool(found)
    return {"graphs": graphs, "bruteForced": brute, "violating": violating}


def reconstructions() -> dict[str, Any]:
    sample = json.loads(audit.SAMPLE.read_text(encoding="utf-8"))
    rebuilt = {(r["module"], r["declaration"]): r
               for r in json.loads(audit.RECONSTRUCTIONS.read_text(encoding="utf-8"))["proofs"]}
    results = [audit.compare_one(e, rebuilt[(e["module"], e["declaration"])]) for e in sample]
    return {"proofs": len(results), "agree": sum(1 for r in results if r["edgesAgree"]),
            "countAgree": sum(1 for r in results if r["derivedCount"] == r["rebuiltCount"])}


def compute() -> tuple[dict[str, list[dict[str, Any]]], dict[str, Any], bytes]:
    records = {"library": read_gz_lines(library.EXTRACTION), "slice": read_gz_lines(slice_.EXTRACTION)}
    rows = {name: [counter.analyse(r) for r in recs] for name, recs in records.items()}
    rows["golf"] = golf_rows()
    lib, sl = strata(rows["library"]), strata(rows["slice"])
    large = [stratum(low) for low, _ in STRATA if low >= 6]
    tested = [n for n in large if sl[n]["counted"] >= MINIMUM_STRATUM]
    structure_rows, structure_summary = golf_structure.run()
    summary = {
        "experiment": "recount-v0.1", "preregistrationSha256": sha256_file(PREREG),
        "library": {"proofs": len(rows["library"]), "counted": sum(1 for r in rows["library"] if r["linearizations"]),
                    "strata": lib} | changes(records["library"], rows["library"]),
        "slice": {"proofs": len(rows["slice"]), "counted": sum(1 for r in rows["slice"] if r["linearizations"]),
                  "strata": sl, "testedStrata": tested} | changes(records["slice"], rows["slice"]),
        "golf": golf_tests(rows["golf"], rows["slice"]),
        "golfStructure": structure_summary["tests"],
        "hypotheses": {
            "H10r": {"supported": all(lib[n]["linearizations"] and int(lib[n]["linearizations"]["median"]) >= 10
                                      for n in large)},
            "H11r": {"supported": all(lib[n]["structure"] and lib[n]["structure"]["median"] < 0.5 for n in large)},
            "H12r": {"supported": all(sl[n]["structure"] and lib[n]["structure"] and
                                      abs(sl[n]["structure"]["median"] - lib[n]["structure"]["median"]) <= TOLERANCE
                                      for n in tested)},
            "H13r": {"supported": all(int(sl[n]["linearizations"]["median"]) >= 10 for n in tested)},
            "H28r": structure_summary["hypotheses"]["H28"]},
        "checks": {"C3": invariants(), "C4": reconstructions()},
    }
    summary["hypotheses"]["H20r"] = {"supported": summary["golf"]["H20r"]["supported"]}
    summary["hypotheses"]["H21r"] = {"supported": summary["golf"]["H21r"]["supported"]}
    dataset = export_graphs.serialize(export_graphs.rows())
    return rows, summary, dataset


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Recount under the corrected step derivation (recount v0.1)", "",
             "Frozen in `preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             "| Corpus | Proofs | Graphs whose steps change | Whose count changes |", "| --- | ---: | ---: | ---: |"]
    for name in ("library", "slice"):
        s = summary[name]
        lines.append(f"| {name} | {s['proofs']} | {s['stepsChanged']} | {s['countChanged']} |")
    lines += ["", "| Stratum | Library: median L | Library: median index | Slice: median L | Slice: median index |",
              "| --- | ---: | ---: | ---: | ---: |"]
    for low, _ in STRATA:
        n = stratum(low)
        a, b = summary["library"]["strata"][n], summary["slice"]["strata"][n]
        fmt = lambda q, k: "n/a" if not q[k] else (library.format_count(q[k]["median"]) if k == "linearizations"
                                                  else f"{q[k]['median']:.3f}")
        lines.append(f"| {n} | {fmt(a, 'linearizations')} | {fmt(a, 'structure')} | {fmt(b, 'linearizations')} | "
                     f"{fmt(b, 'structure')} |")
    lines += ["", "## Hypotheses", ""] + [f"- {k}: supported: {v['supported']}." for k, v in summary["hypotheses"].items()]
    c = summary["checks"]
    lines += ["", f"C3: {c['C3']['violating']} of {c['C3']['graphs']} graphs violate an invariant "
              f"({c['C3']['bruteForced']} brute-forced). C4: {c['C4']['agree']} of {c['C4']['proofs']} reconstructions "
              "agree."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    if args.register:
        if SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    for name in ("counter", "earlierCounter"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    rows, summary, dataset = compute()
    texts = {path: "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in rows[name])
             for path, name in ((LIBRARY, "library"), (SLICE, "slice"), (GOLF, "golf"))}
    if args.run:
        for path, text in texts.items():
            write_lf(path, text)
        DATASET.write_bytes(dataset)
        summary["datasetSha256"] = sha256_file(DATASET)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"hypotheses": summary["hypotheses"], "checks": summary["checks"]}))
        return 0
    for path, text in texts.items():
        if path.read_text(encoding="utf-8") != text:
            raise SystemExit(f"{path.name} does not follow from the committed extractions")
    if DATASET.read_bytes() != dataset:
        raise SystemExit("the committed dataset does not follow from the committed extractions")
    summary["datasetSha256"] = sha256_file(DATASET)
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != summary:
        raise SystemExit("the committed summary does not follow from the committed extractions")
    print(f"recount-check-ok: graphs={summary['checks']['C3']['graphs']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
