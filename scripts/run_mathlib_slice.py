#!/usr/bin/env python3
"""Order redundancy of a fixed slice of Mathlib's tactic proofs: register, run, check.

  python scripts/run_mathlib_slice.py --register
  python scripts/run_mathlib_slice.py --run
  python scripts/run_mathlib_slice.py --recount
  python scripts/run_mathlib_slice.py --check-committed

The corpus is every 50th module, in name order, of Mathlib at the Lake
dependency's revision, outside its meta-programming directories. The
extractor, the counter, the strata, and the count summaries are those of the
ProofNet-IR experiment (`run_linearizations.py`, imported here); this script
only selects the modules, tolerates modules that fail to elaborate outside
Mathlib's build configuration (they are dropped and listed), and evaluates
the slice's hypotheses against the committed ProofNet-IR summary.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_linearizations as base  # noqa: E402
from run_linearizations import (STRATA, count, find_lake, format_count, int_quantiles, quantiles,  # noqa: E402
                                read_gz_lines, same_row, sha256_file, stratum, write_gz, write_lf)

ROOT = base.ROOT
PACKAGE = ROOT / ".lake" / "packages" / "mathlib"
EXPERIMENT = ROOT / "experiments" / "linearizations-mathlib-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
EXTRACTION = EXPERIMENT / "extraction.jsonl.gz"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
REFERENCE = base.SUMMARY  # the committed ProofNet-IR summary
IMPLEMENTATIONS = {**{k: v for k, v in base.IMPLEMENTATIONS.items() if k != "runner"},
                   "baseRunner": base.IMPLEMENTATIONS["runner"], "runner": Path(__file__).resolve()}
EXCLUDED_DIRECTORIES = ("Tactic", "Util", "Lean", "Testing", "Deprecated", "Mathport")
STRIDE = 50
MINIMUM_STRATUM = 30
TOLERANCE = 0.10
CHECK_SAMPLE_SIZE = 3


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def dependency_revision() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["name"].strip("«»") == "mathlib":
            return package["rev"]
    raise SystemExit("mathlib is not in the manifest")


def population() -> list[tuple[str, Path]]:
    result = []
    for path in (PACKAGE / "Mathlib").rglob("*.lean"):
        relative = path.relative_to(PACKAGE).with_suffix("")
        if len(relative.parts) > 1 and relative.parts[1] in EXCLUDED_DIRECTORIES:
            continue
        result.append((".".join(relative.parts), path))
    return sorted(result)


def modules() -> list[tuple[str, Path]]:
    return population()[::STRIDE]


def extract(selection: list[tuple[str, Path]]) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    """One extractor process per module; a module whose diagnostics report an
    error is dropped and returned in the second list."""
    records: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    for module, path in selection:
        completed = subprocess.run([find_lake(), "exe", "proof_graph_extract", module, str(path)], cwd=ROOT,
                                   capture_output=True, text=True, encoding="utf-8")
        diagnostics = [line for line in completed.stderr.splitlines() if ": modules=" in line]
        if completed.returncode != 0 or len(diagnostics) != 1 or "errors=0" not in diagnostics[0]:
            failures.append({"module": module, "diagnostics": (diagnostics or [completed.stderr[-500:]])[0][:1000]})
            continue
        records += [json.loads(line) for line in completed.stdout.splitlines() if line.startswith("{")]
    return records, failures


def registration_payload() -> dict[str, Any]:
    everything = population()
    selected = modules()
    reference = json.loads(REFERENCE.read_text(encoding="utf-8"))
    return {
        "experiment": "linearizations-mathlib-v0.1",
        "question": "is the order redundancy measured on ProofNet-IR's tactic proofs typical of Lean proofs "
                    "written by many hands, i.e. do Mathlib's proofs show the same distribution of "
                    "linearizations and structure index by step count",
        "object": "as in linearizations-v0.1: the step-dependency graph of a tactic proof, derived from "
                  "Lean's info trees by the same extractor and counter (after their amendments 1 to 4)",
        "corpus": {"package": "mathlib", "revision": dependency_revision(), "population": len(everything),
                   "populationRule": "every Mathlib module outside " + ", ".join(EXCLUDED_DIRECTORIES) +
                   ", sorted by name", "stride": STRIDE, "modules": len(selected),
                   "moduleList": [name for name, _ in selected],
                   "scope": "every declaration with at least one tactic step in every selected module"},
        "strata": [stratum(low) for low, _ in STRATA],
        "reference": {"experiment": "linearizations-v0.1", "summarySha256": sha256_file(REFERENCE),
                      "structureMedians": {name: entry["structure"]["median"] if entry["structure"] else None
                                           for name, entry in reference["strata"].items()}},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "exclusionPolicy": "a non-forest graph with more than 22 steps has no count and is reported as excluded; "
                           "a module that fails to elaborate outside Mathlib's build configuration is dropped "
                           "and listed with its first error",
        "hypotheses": {
            "H12": f"in every stratum of at least 6 steps with at least {MINIMUM_STRATUM} counted proofs, the "
                   f"median structure index is within {TOLERANCE} of ProofNet-IR's median for that stratum",
            "H13": f"in every stratum of at least 6 steps with at least {MINIMUM_STRATUM} counted proofs, the "
                   "median number of linearizations is at least 10",
        },
        "developmentChecksBeforeRegistration": "the extractor was run on Mathlib.Logic.Basic, "
                                                "Mathlib.Data.List.Basic, Mathlib.Topology.Basic, and "
                                                "Mathlib.Algebra.Group.Basic to confirm elaboration (11 to 64 "
                                                "seconds each, no errors); the counts of Mathlib.Logic.Basic "
                                                "were seen (71 declarations, median 2 steps, 54 single-order); "
                                                "none of the four is in the slice unless the stride selects it",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-21 America/Los_Angeles",
    }


def summarize(rows: list[dict[str, Any]], failures: list[dict[str, str]]) -> dict[str, Any]:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    reference = prereg["reference"]["structureMedians"]
    per_stratum: dict[str, Any] = {}
    for low, high in STRATA:
        name = stratum(low)
        members = [r for r in rows if low <= r["steps"] <= high]
        counted = [r for r in members if r["linearizations"] is not None]
        per_stratum[name] = {
            "proofs": len(members), "counted": len(counted), "excluded": len(members) - len(counted),
            "forests": sum(1 for r in members if r["forest"]),
            "multiRoot": sum(1 for r in members if r["roots"] > 1),
            "linearizations": int_quantiles([int(r["linearizations"]) for r in counted]),
            "log10": quantiles([r["log10"] for r in counted if r["log10"] is not None]),
            "structure": quantiles([r["structure"] for r in counted if r["structure"] is not None]),
            "referenceStructureMedian": reference[name],
            "fractionSingleOrder": (sum(1 for r in counted if r["linearizations"] == "1") / len(counted)) if counted else None,
        }
    tested = [name for name, (low, _) in zip(per_stratum, STRATA)
              if low >= 6 and per_stratum[name]["counted"] >= MINIMUM_STRATUM]
    h12 = all(per_stratum[n]["structure"] and reference[n] is not None
              and abs(per_stratum[n]["structure"]["median"] - reference[n]) <= TOLERANCE for n in tested)
    h13 = all(int(per_stratum[n]["linearizations"]["median"]) >= 10 for n in tested)
    return {"experiment": "linearizations-mathlib-v0.1", "preregistrationSha256": sha256_file(PREREG),
            "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
            "proofs": len(rows), "counted": sum(1 for r in rows if r["linearizations"] is not None),
            "modulesExtracted": len({r["module"] for r in rows}), "modulesFailed": failures,
            "stepsQuartiles": quantiles([r["steps"] for r in rows]),
            "strata": per_stratum, "testedStrata": tested,
            "hypotheses": {"H12": {"supported": h12}, "H13": {"supported": h13}},
            "extractionSha256": sha256_file(EXTRACTION), "resultsSha256": sha256_file(RESULTS)}


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Order redundancy of a Mathlib slice (linearizations-mathlib v0.1)", "",
             "Exact numbers of step orderings admitted by the goal-dependency graph of every",
             f"tactic proof in every {STRIDE}th Mathlib module; definitions, corpus, and hypotheses are",
             "frozen in `preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             f"Modules extracted: {summary['modulesExtracted']}; dropped for elaboration errors: "
             f"{len(summary['modulesFailed'])}. Proofs with tactic steps: {summary['proofs']}; counted exactly: "
             f"{summary['counted']}.", "",
             "| Steps | Proofs | Forests | Multi-root | Linearizations median (q1, q3, max) | log10 median | "
             "Structure median (q1, q3) | ProofNet-IR structure median | Single order |",
             "| --- | ---: | ---: | ---: | --- | ---: | --- | ---: | ---: |"]
    for name, entry in summary["strata"].items():
        lin = entry["linearizations"]; st = entry["structure"]; lg = entry["log10"]
        lin_text = "n/a" if not lin else (f"{format_count(lin['median'])} ({format_count(lin['q1'])}, "
                                          f"{format_count(lin['q3'])}, {format_count(lin['max'])})")
        st_text = "n/a" if not st else f"{st['median']:.3f} ({st['q1']:.3f}, {st['q3']:.3f})"
        lg_text = "n/a" if not lg else f"{lg['median']:.2f}"
        ref = entry["referenceStructureMedian"]
        ref_text = "n/a" if ref is None else f"{ref:.3f}"
        single = "n/a" if entry["fractionSingleOrder"] is None else f"{entry['fractionSingleOrder']:.1%}"
        lines.append(f"| {name} | {entry['proofs']} | {entry['forests']} | {entry['multiRoot']} | {lin_text} | "
                     f"{lg_text} | {st_text} | {ref_text} | {single} |")
    h = summary["hypotheses"]
    lines += ["", f"Strata tested (at least 6 steps and {MINIMUM_STRATUM} counted proofs): "
              + ", ".join(summary["testedStrata"]) + ".", "", "## Hypotheses", "",
              f"- H12 (median structure index within {TOLERANCE} of ProofNet-IR's in every tested stratum): "
              f"supported: {h['H12']['supported']}.",
              f"- H13 (median linearizations at least 10 in every tested stratum): supported: {h['H13']['supported']}.",
              "", "## Interpretation boundary", "",
              "The slice is a systematic sample of modules, not of proofs; a module's proofs share",
              "an author and a subject. The count says nothing about how a search would explore",
              "the orderings, and Lean's first-goal convention already fixes one of them."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def check_sample(records: list[dict[str, Any]]) -> list[str]:
    """The slice modules with the fewest extracted nodes, ties by name."""
    sizes: dict[str, int] = {}
    for record in records:
        sizes[record["module"]] = sizes.get(record["module"], 0) + len(record["nodes"])
    return [name for name, _ in sorted(sizes.items(), key=lambda item: (item[1], item[0]))[:CHECK_SAMPLE_SIZE]]


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--recount", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()

    if args.register:
        if RESULTS.exists() or EXTRACTION.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload()
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True) + "\n")
        print(f"registered {payload['corpus']['modules']} of {payload['corpus']['population']} modules at "
              f"{payload['corpus']['revision']}: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["revision"] != dependency_revision():
        raise SystemExit("mathlib revision changed since registration")
    if prereg["corpus"]["moduleList"] != [name for name, _ in modules()]:
        raise SystemExit("module list changed since registration")
    if prereg["reference"]["summarySha256"] != sha256_file(REFERENCE):
        raise SystemExit("the ProofNet-IR summary changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("extractor", "extractorMain", "counter"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")

    if args.run or args.recount:
        if args.run:
            records, failures = extract(modules())
            write_gz(EXTRACTION, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records))
            write_lf(EXPERIMENT / "failures.json", json.dumps(failures, indent=1) + "\n")
        else:
            records = read_gz_lines(EXTRACTION)
            failures = json.loads((EXPERIMENT / "failures.json").read_text(encoding="utf-8"))
        rows = count(records)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows, failures)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(f"mathlib-slice-run: modules={summary['modulesExtracted']} failed={len(failures)} "
              f"proofs={summary['proofs']} counted={summary['counted']} "
              f"H12={summary['hypotheses']['H12']['supported']} H13={summary['hypotheses']['H13']['supported']}")
        return 0

    records = read_gz_lines(EXTRACTION)
    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    recounted = count(records)
    if len(recounted) != len(committed):
        raise SystemExit(f"recounted {len(recounted)} rows, committed {len(committed)}")
    for fresh_row, committed_row in zip(recounted, committed):
        if not same_row(fresh_row, committed_row):
            raise SystemExit(f"recounted results differ from the committed results at "
                             f"{committed_row['declaration']}: {fresh_row} vs {committed_row}")
    sample_names = check_sample(records)
    sample = [(name, path) for name, path in modules() if name in sample_names]
    fresh_records, failures = extract(sample)
    if failures:
        raise SystemExit(f"re-extraction failed: {failures}")
    fresh = {(r["module"], r["declaration"]): r for r in fresh_records}
    committed_sample = {(r["module"], r["declaration"]): r for r in records if r["module"] in sample_names}
    if set(fresh) != set(committed_sample):
        raise SystemExit("re-extracted sample declarations differ from the committed extraction")

    def shape(record: dict[str, Any]) -> list[tuple[Any, ...]]:
        return [(n["index"], n["parent"], n["leaf"], n["kind"], len(n["before"]), len(n["after"]))
                for n in record["nodes"]]

    for key, record in fresh.items():
        if shape(record) != shape(committed_sample[key]):
            raise SystemExit(f"re-extracted nodes differ for {key[1]}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["extractionSha256"] != sha256_file(EXTRACTION) or summary["resultsSha256"] != sha256_file(RESULTS) \
            or summary["preregistrationSha256"] != sha256_file(PREREG) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    print(f"mathlib-slice-check-ok: proofs={len(committed)} sampleModules={len(sample)} sampleProofs={len(fresh)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
