#!/usr/bin/env python3
"""Order redundancy of real Lean tactic proofs: register, run, check.

  python scripts/run_linearizations.py --register
  python scripts/run_linearizations.py --run
  python scripts/run_linearizations.py --check-committed

The corpus is every tactic proof of ProofNet-IR `v0.10.0`, the Lake
dependency of this package. `--register` freezes the dependency revision, the
module list, the extractor and counter hashes, the strata, and the
hypotheses before any proof is extracted. `--run` extracts the step
dependency graph of every declaration with `proof_graph_extract`, counts the
linear orderings with `count_linearizations.py`, and writes
`extraction.jsonl`, `results.jsonl`, `summary.json`, and `report.md`.
`--check-committed` recounts from the committed extraction, re-extracts a
fixed sample of modules and compares, and verifies the artifact hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / ".lake" / "packages" / "proofnet-ir"
EXPERIMENT = ROOT / "experiments" / "linearizations-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
EXTRACTION = EXPERIMENT / "extraction.jsonl"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "extractor": ROOT / "ProofGraphs" / "Extract.lean",
    "extractorMain": ROOT / "ProofGraphsExtract.lean",
    "counter": ROOT / "scripts" / "count_linearizations.py",
    "runner": ROOT / "scripts" / "run_linearizations.py",
}
STRATA = [(1, 1), (2, 5), (6, 10), (11, 20), (21, 50), (51, 10**9)]
CHECK_SAMPLE_MODULES = ["ProofNetIR.Formula", "ProofNetIR.Certificate", "ProofNetIR.Figure7.Cost"]


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def write_lf(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


def find_lake() -> str:
    import shutil

    on_path = shutil.which("lake")
    if on_path:
        return on_path
    for name in ("lake", "lake.exe"):
        candidate = Path.home() / ".elan" / "bin" / name
        if candidate.is_file():
            return str(candidate)
    raise FileNotFoundError("lake not found")


def dependency_revision() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["name"].strip("«»") == "proofnet-ir":
            return package["rev"]
    raise SystemExit("proofnet-ir is not in the manifest")


def modules() -> list[tuple[str, Path]]:
    files = sorted((PACKAGE / "ProofNetIR").rglob("*.lean"))
    result = []
    for path in files:
        relative = path.relative_to(PACKAGE).with_suffix("")
        result.append((".".join(relative.parts), path))
    return result


def extract(selection: list[tuple[str, Path]]) -> list[dict[str, Any]]:
    """One extractor process per module, so that every module starts from a
    fresh environment and its diagnostics are attributable."""
    records: list[dict[str, Any]] = []
    for module, path in selection:
        completed = subprocess.run([find_lake(), "exe", "proof_graph_extract", module, str(path)], cwd=ROOT,
                                   capture_output=True, text=True, encoding="utf-8", check=True)
        diagnostics = [line for line in completed.stderr.splitlines() if ": modules=" in line]
        if len(diagnostics) != 1 or "errors=0" not in diagnostics[0]:
            raise SystemExit(f"elaboration problem in {module}: {diagnostics}")
        records += [json.loads(line) for line in completed.stdout.splitlines() if line.startswith("{")]
    return records


def count(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    payload = "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records)
    completed = subprocess.run([sys.executable, str(IMPLEMENTATIONS["counter"])], cwd=ROOT, input=payload,
                               capture_output=True, text=True, encoding="utf-8", check=True)
    return [json.loads(line) for line in completed.stdout.splitlines() if line.strip()]


def stratum(steps: int) -> str:
    for low, high in STRATA:
        if low <= steps <= high:
            return f"steps-{low}" if low == high else (f"steps-{low}-{high}" if high < 10**9 else f"steps-{low}+")
    raise AssertionError(steps)


def registration_payload() -> dict[str, Any]:
    module_list = [name for name, _ in modules()]
    return {
        "experiment": "linearizations-v0.1",
        "question": "how many orderings of its tactic steps does a real Lean proof admit, i.e. how much "
                    "rule-order redundancy does a linear tactic script carry relative to its goal-dependency graph",
        "object": "the step-dependency graph of a tactic proof: a step is a leaf tactic node that consumes "
                  "or produces goals; it depends on the steps that produced the goals it consumes; goals hidden "
                  "by focusing and reappearing later are not consumed",
        "quantity": "linearizations: orderings of the steps respecting the dependencies, exact by the "
                    "hook-length formula for forests and by subset dynamic programming otherwise (at most 22 "
                    "steps); structure: log(linearizations) / log(steps!)",
        "corpus": {"package": "proofnet-ir", "revision": dependency_revision(), "modules": len(module_list),
                   "moduleList": module_list,
                   "scope": "every declaration with at least one tactic step in every ProofNetIR module"},
        "strata": [stratum(low) for low, _ in STRATA],
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "exclusionPolicy": "a non-forest graph with more than 22 steps has no count and is reported as excluded; "
                           "a module with an elaboration error aborts the run",
        "hypotheses": {
            "H10": "in every stratum of at least 6 steps, the median number of linearizations is at least 10",
            "H11": "in every stratum of at least 6 steps, the median structure index is below 0.5",
        },
        "sideQuantity": "the distribution of the structure index per stratum, as a candidate measure of how "
                        "structured a proof is (0: a single chain, 1: every step independent)",
        "developmentChecksBeforeRegistration": "six hand-checked fixtures (chain 1, star 6, nested 80, single "
                                                "step 1, cases 2, nested cases 8) extracted and counted, and the "
                                                "extractor was exercised on ProofNetIR.Formula and ProofNetIR.Checker "
                                                "to confirm elaboration; no corpus count was recorded",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-22 America/Los_Angeles",
    }


def quantiles(values: list[float]) -> dict[str, float] | None:
    if not values:
        return None
    ordered = sorted(values)
    q = statistics.quantiles(ordered, n=4) if len(ordered) >= 2 else [ordered[0]] * 3
    return {"min": ordered[0], "q1": q[0], "median": statistics.median(ordered), "q3": q[2],
            "max": ordered[-1], "count": len(ordered)}


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    per_stratum: dict[str, Any] = {}
    for low, high in STRATA:
        name = stratum(low)
        members = [r for r in rows if low <= r["steps"] <= high]
        counted = [r for r in members if r["linearizations"] is not None]
        per_stratum[name] = {
            "proofs": len(members), "counted": len(counted), "excluded": len(members) - len(counted),
            "forests": sum(1 for r in members if r["forest"]),
            "linearizations": quantiles([float(r["linearizations"]) for r in counted]),
            "log10": quantiles([r["log10"] for r in counted if r["log10"] is not None]),
            "structure": quantiles([r["structure"] for r in counted if r["structure"] is not None]),
            "fractionSingleOrder": (sum(1 for r in counted if r["linearizations"] == "1") / len(counted)) if counted else None,
        }
    large = [name for name, (low, _) in zip(per_stratum, STRATA) if low >= 6]
    h10 = all(per_stratum[n]["linearizations"] and per_stratum[n]["linearizations"]["median"] >= 10 for n in large)
    h11 = all(per_stratum[n]["structure"] and per_stratum[n]["structure"]["median"] < 0.5 for n in large)
    return {"experiment": "linearizations-v0.1", "preregistrationSha256": sha256_file(PREREG),
            "proofs": len(rows), "counted": sum(1 for r in rows if r["linearizations"] is not None),
            "strata": per_stratum, "hypotheses": {"H10": {"supported": h10}, "H11": {"supported": h11}},
            "extractionSha256": sha256_file(EXTRACTION), "resultsSha256": sha256_file(RESULTS)}


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Order redundancy of ProofNet-IR's tactic proofs (linearizations v0.1)", "",
             "Exact numbers of step orderings admitted by the goal-dependency graph of every",
             "tactic proof in ProofNet-IR v0.10.0; definitions, corpus, and hypotheses are frozen",
             "in `preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             f"Proofs with tactic steps: {summary['proofs']}; counted exactly: {summary['counted']}.", "",
             "| Steps | Proofs | Forests | Linearizations median (q1, q3, max) | log10 median | Structure median (q1, q3) | Single order |",
             "| --- | ---: | ---: | --- | ---: | --- | ---: |"]
    for name, entry in summary["strata"].items():
        lin = entry["linearizations"]; st = entry["structure"]; lg = entry["log10"]
        lin_text = "n/a" if not lin else f"{lin['median']:.6g} ({lin['q1']:.6g}, {lin['q3']:.6g}, {lin['max']:.6g})"
        st_text = "n/a" if not st else f"{st['median']:.3f} ({st['q1']:.3f}, {st['q3']:.3f})"
        lg_text = "n/a" if not lg else f"{lg['median']:.2f}"
        single = "n/a" if entry["fractionSingleOrder"] is None else f"{entry['fractionSingleOrder']:.1%}"
        lines.append(f"| {name} | {entry['proofs']} | {entry['forests']} | {lin_text} | {lg_text} | {st_text} | {single} |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              f"- H10 (median linearizations at least 10 in every stratum of at least 6 steps): supported: {h['H10']['supported']}.",
              f"- H11 (median structure index below 0.5 in every such stratum): supported: {h['H11']['supported']}.", "",
              "## Interpretation boundary", "",
              "The count is a property of the proofs as written: how many step orders the",
              "goal-dependency graph admits. It says nothing about how a search would explore",
              "them, which is the next step, and nothing about proofs outside this corpus."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()

    if args.register:
        if RESULTS.exists() or EXTRACTION.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        payload = registration_payload()
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True) + "\n")
        print(f"registered {payload['corpus']['modules']} modules at {payload['corpus']['revision']}: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["revision"] != dependency_revision():
        raise SystemExit("dependency revision changed since registration")
    if prereg["corpus"]["moduleList"] != [name for name, _ in modules()]:
        raise SystemExit("module list changed since registration")
    for name in ("extractor", "extractorMain", "counter"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")

    if args.run:
        records = extract(modules())
        write_lf(EXTRACTION, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records))
        rows = count(records)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(f"linearizations-run: proofs={summary['proofs']} counted={summary['counted']} "
              f"H10={summary['hypotheses']['H10']['supported']} H11={summary['hypotheses']['H11']['supported']}")
        return 0

    records = [json.loads(line) for line in EXTRACTION.read_text(encoding="utf-8").splitlines() if line.strip()]
    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    recounted = count(records)
    if recounted != committed:
        raise SystemExit("recounted results differ from the committed results")
    sample = [(name, path) for name, path in modules() if name in CHECK_SAMPLE_MODULES]
    fresh = {r["declaration"]: r for r in extract(sample)}
    committed_sample = {r["declaration"]: r for r in records if r["module"] in CHECK_SAMPLE_MODULES}
    if set(fresh) != set(committed_sample):
        raise SystemExit("re-extracted sample declarations differ from the committed extraction")
    for name, record in fresh.items():
        want = [(s["kind"], len(s["consumed"]), len(s["produced"])) for s in committed_sample[name]["steps"]]
        have = [(s["kind"], len(s["consumed"]), len(s["produced"])) for s in record["steps"]]
        if want != have:
            raise SystemExit(f"re-extracted steps differ for {name}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["extractionSha256"] != sha256_file(EXTRACTION) or summary["resultsSha256"] != sha256_file(RESULTS) \
            or summary["preregistrationSha256"] != sha256_file(PREREG):
        raise SystemExit("summary hashes do not match the committed files")
    print(f"linearizations-check-ok: proofs={len(committed)} sampleModules={len(sample)} sampleProofs={len(fresh)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
