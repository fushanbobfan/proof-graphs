#!/usr/bin/env python3
"""Extraction audit v0.1: goal-dependency graphs reconstructed independently, blind.

  python scripts/run_extraction_audit.py --register
  python scripts/run_extraction_audit.py --compare
  python scripts/run_extraction_audit.py --check-committed

A seeded random sample of 30 proofs, 15 from each corpus of step 1 (the
tactic proofs of ProofNet-IR v0.10.0 and those of the Mathlib slice), 5 per
stratum of 2 to 5, 6 to 10, and 11 to 20 steps, among declarations whose
proof is one `by` block and whose name is not generated. For every sampled
proof a reconstructor who has not seen its derived graph reads the source,
displays Lean's goals where needed, and writes down the steps and dependency
edges of the definition in the docstring of `scripts/count_linearizations.py`
(`reconstructions.json`). `--compare` then matches the reconstructed steps
with the derived ones by source line and compares the dependency edges and
the ordering counts. Every disagreement is adjudicated (`adjudication.json`)
as an extractor error, a reconstruction error, or a gap in the definition.
"""

from __future__ import annotations

import argparse
import collections
import json
import random
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
import run_linearizations as library  # noqa: E402
import run_mathlib_slice as slice_  # noqa: E402
from run_linearizations import read_gz_lines, sha256_file, write_lf  # noqa: E402
from run_search import generated  # noqa: E402

ROOT = library.ROOT
EXPERIMENT = ROOT / "experiments" / "extraction-audit-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
SAMPLE = EXPERIMENT / "sample.json"
RECONSTRUCTIONS = EXPERIMENT / "reconstructions.json"
ADJUDICATION = EXPERIMENT / "adjudication.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations.py", "runner": Path(__file__).resolve()}
CORPORA = {
    "proofnet-ir": {"extraction": library.EXTRACTION, "results": library.RESULTS,
                    "source": ROOT / ".lake" / "packages" / "proofnet-ir"},
    "mathlib-slice": {"extraction": slice_.EXTRACTION, "results": slice_.RESULTS,
                      "source": ROOT / ".lake" / "packages" / "mathlib"},
}
STRATA = ((2, 5), (6, 10), (11, 20))
PER_STRATUM = 5
SEED = 20260925
CATEGORIES = ("extractor error", "reconstruction error", "definition gap")


def eligible(corpus: str) -> dict[tuple[int, int], list[dict[str, Any]]]:
    paths = CORPORA[corpus]
    rows = {(r["module"], r["declaration"]): r for r in
            (json.loads(l) for l in paths["results"].read_text(encoding="utf-8").splitlines() if l.strip())}
    out: dict[tuple[int, int], list[dict[str, Any]]] = {s: [] for s in STRATA}
    for record in read_gz_lines(paths["extraction"]):
        roots = [n for n in record["nodes"] if n["parent"] is None]
        if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic") or generated(record["declaration"]):
            continue
        steps = rows[(record["module"], record["declaration"])]["steps"]
        for low, high in STRATA:
            if low <= steps <= high:
                source = paths["source"] / (record["module"].replace(".", "/") + ".lean")
                out[(low, high)].append({"corpus": corpus, "module": record["module"],
                                         "declaration": record["declaration"],
                                         "source": source.relative_to(ROOT).as_posix(),
                                         "byLine": roots[0]["line"], "stratum": f"{low}-{high}"})
    for stratum in out.values():
        stratum.sort(key=lambda e: (e["module"], e["byLine"], e["declaration"]))
    return out


def draw_sample() -> list[dict[str, Any]]:
    rng = random.Random(SEED)
    sample = []
    for corpus in CORPORA:
        pools = eligible(corpus)
        for stratum in STRATA:
            sample += rng.sample(pools[stratum], PER_STRATUM)
    return sample


def registration_payload(sample: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "extraction-audit-v0.1",
        "question": "does the derived goal-dependency graph agree with the graph an independent reconstructor derives from "
                    "the proof and Lean's goal display, following the same definition",
        "sample": {"rule": f"seed {SEED}; for each corpus of linearizations-v0.1 and linearizations-mathlib-v0.1, "
                           f"{PER_STRATUM} proofs drawn uniformly without replacement from each stratum of "
                           f"{', '.join(f'{a} to {b}' for a, b in STRATA)} steps, among declarations with one root "
                           "`by` block and a name that is not generated, pools in (module, line) order",
                   "count": len(sample),
                   "libraryExtractionSha256": sha256_file(library.EXTRACTION),
                   "sliceExtractionSha256": sha256_file(slice_.EXTRACTION)},
        "protocol": ["the reconstructor receives only sample.json (declaration, module, source file, line of the "
                     "`by` block) and the definition in the docstring of scripts/count_linearizations.py",
                     "the reconstructor may read any source file and display Lean's goals at any position with the "
                     "Lean language server, and must not open the extraction, results, dataset, or audit files of "
                     "this repository or run the extractor or counter",
                     "for each proof the reconstructor records the steps (source line and tactic, in source order) "
                     "and the dependency edges (step i originated a goal that step j consumes) in "
                     "reconstructions.json, committed before --compare is first run",
                     "--compare matches steps by source line, and within a line by order; a proof agrees when both "
                     "graphs have the same steps per line and the same edges",
                     "every disagreement is adjudicated with its evidence (the goals Lean displays) into one of: "
                     + "; ".join(CATEGORIES)],
        "hypotheses": {"H26": "no disagreement is adjudicated as an extractor error"},
        "measures": {"agreement": "proofs whose steps and edges agree", "countAgreement": "proofs whose "
                     "number of orderings, computed from each graph by the same formula, agrees"},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on the sample; the runner's sampling was run once to write "
                                                "sample.json",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def derived_graph(entry: dict[str, Any]) -> tuple[list[dict[str, Any]], list[set[int]]]:
    extraction = CORPORA[entry["corpus"]]["extraction"]
    record = next(r for r in read_gz_lines(extraction)
                  if r["module"] == entry["module"] and r["declaration"] == entry["declaration"])
    steps = counter.derive_steps(record["nodes"])
    return steps, counter.dependency_graph(steps)


def count(parents: list[set[int]]) -> str | None:
    if all(len(ps) <= 1 for ps in parents):
        return str(counter.forest_linearizations(parents))
    if len(parents) <= counter.DP_MAX_STEPS:
        return str(counter.dag_linearizations(parents))
    return None


def keyed(lines: list[int]) -> list[tuple[int, int]]:
    """(line, order within the line) for steps listed in order."""
    seen: collections.Counter[int] = collections.Counter()
    out = []
    for line in lines:
        out.append((line, seen[line]))
        seen[line] += 1
    return out


def compare_one(entry: dict[str, Any], rebuilt: dict[str, Any]) -> dict[str, Any]:
    steps, parents = derived_graph(entry)
    order = sorted(range(len(steps)), key=lambda i: (steps[i]["line"], i))
    derived_keys = dict(zip(order, keyed([steps[i]["line"] for i in order])))
    derived_edges = {(derived_keys[p], derived_keys[c]) for c, ps in enumerate(parents) for p in ps}
    rebuilt_keys = keyed([s["line"] for s in rebuilt["steps"]])
    rebuilt_edges = {(rebuilt_keys[i], rebuilt_keys[j]) for i, j in rebuilt["edges"]}
    rebuilt_parents: list[set[int]] = [set() for _ in rebuilt["steps"]]
    for i, j in rebuilt["edges"]:
        rebuilt_parents[j].add(i)
    derived_lines = collections.Counter(s["line"] for s in steps)
    rebuilt_lines = collections.Counter(s["line"] for s in rebuilt["steps"])
    return {"corpus": entry["corpus"], "module": entry["module"], "declaration": entry["declaration"],
            "stratum": entry["stratum"],
            "derivedSteps": len(steps), "rebuiltSteps": len(rebuilt["steps"]),
            "stepsAgree": derived_lines == rebuilt_lines,
            "edgesAgree": derived_lines == rebuilt_lines and derived_edges == rebuilt_edges,
            "derivedCount": count(parents), "rebuiltCount": count(rebuilt_parents),
            "onlyDerivedLines": sorted((derived_lines - rebuilt_lines).elements()),
            "onlyRebuiltLines": sorted((rebuilt_lines - derived_lines).elements()),
            "onlyDerivedEdges": sorted([list(a), list(b)] for a, b in derived_edges - rebuilt_edges),
            "onlyRebuiltEdges": sorted([list(a), list(b)] for a, b in rebuilt_edges - derived_edges)}


def summarize(results: list[dict[str, Any]], adjudication: dict[str, Any]) -> dict[str, Any]:
    disagreements = [r for r in results if not r["edgesAgree"]]
    verdicts = {(a["module"], a["declaration"]): a["category"] for a in adjudication.get("verdicts", [])}
    missing = [r["declaration"] for r in disagreements if (r["module"], r["declaration"]) not in verdicts]
    by_category = collections.Counter(verdicts.get((r["module"], r["declaration"])) for r in disagreements)
    return {"experiment": "extraction-audit-v0.1", "preregistrationSha256": sha256_file(PREREG),
            "reconstructionsSha256": sha256_file(RECONSTRUCTIONS),
            "adjudicationSha256": sha256_file(ADJUDICATION) if ADJUDICATION.exists() else None,
            "proofs": len(results), "agree": len(results) - len(disagreements),
            "countAgree": sum(1 for r in results if r["derivedCount"] == r["rebuiltCount"]),
            "disagreements": len(disagreements),
            "byCategory": {c: by_category.get(c, 0) for c in CATEGORIES},
            "unadjudicated": missing,
            "hypotheses": {"H26": {"supported": None if missing else by_category.get("extractor error", 0) == 0}},
            "resultsSha256": sha256_file(RESULTS)}


def write_report(summary: dict[str, Any], results: list[dict[str, Any]], adjudication: dict[str, Any]) -> None:
    notes = {(a["module"], a["declaration"]): a for a in adjudication.get("verdicts", [])}
    lines = ["# Blind reconstruction of goal-dependency graphs (extraction audit v0.1)", "",
             "Sample, protocol, and hypothesis are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Proofs: {summary['proofs']}; graphs agree: {summary['agree']}; ordering counts agree: "
             f"{summary['countAgree']}.", "",
             "| Corpus | Stratum | Declaration | Steps (derived / rebuilt) | Agree |",
             "| --- | --- | --- | ---: | --- |"]
    for r in results:
        lines.append(f"| {r['corpus']} | {r['stratum']} | `{r['declaration']}` | {r['derivedSteps']} / "
                     f"{r['rebuiltSteps']} | {'yes' if r['edgesAgree'] else 'no'} |")
    lines += ["", "## Disagreements", ""]
    for r in results:
        if r["edgesAgree"]:
            continue
        verdict = notes.get((r["module"], r["declaration"]), {})
        lines.append(f"- `{r['declaration']}`: {verdict.get('category', 'not adjudicated')}. "
                     f"{verdict.get('note', '')}")
    if summary["disagreements"] == 0:
        lines.append("None.")
    lines += ["", f"H26 (no extractor error): supported: {summary['hypotheses']['H26']['supported']}."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--compare", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()

    if args.register:
        if RECONSTRUCTIONS.exists() or RESULTS.exists():
            raise SystemExit("reconstructions or results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        sample = draw_sample()
        write_lf(SAMPLE, json.dumps(sample, indent=1, ensure_ascii=False) + "\n")
        payload = registration_payload(sample)
        payload["sampleSha256"] = sha256_file(SAMPLE)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(sample)} proofs: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["sampleSha256"] != sha256_file(SAMPLE) or draw_sample() != json.loads(SAMPLE.read_text(encoding="utf-8")):
        raise SystemExit("the sample changed since registration")
    if prereg["implementationSha256"]["counter"] != sha256_file(IMPLEMENTATIONS["counter"]):
        raise SystemExit("the counter changed since registration")
    sample = json.loads(SAMPLE.read_text(encoding="utf-8"))
    rebuilt = {(r["module"], r["declaration"]): r
               for r in json.loads(RECONSTRUCTIONS.read_text(encoding="utf-8"))["proofs"]}
    results = [compare_one(entry, rebuilt[(entry["module"], entry["declaration"])]) for entry in sample]
    adjudication = json.loads(ADJUDICATION.read_text(encoding="utf-8")) if ADJUDICATION.exists() else {}

    if args.compare:
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in results))
        summary = summarize(results, adjudication)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary, results, adjudication)
        print(json.dumps({k: summary[k] for k in ("proofs", "agree", "countAgree", "byCategory", "unadjudicated")}))
        return 0

    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if committed != results:
        raise SystemExit("the committed comparison does not follow from the reconstructions and the extraction")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summarize(results, adjudication) != summary:
        raise SystemExit("the committed summary does not follow from the committed results and adjudication")
    print(f"extraction-audit-check-ok: proofs={len(results)} agree={summary['agree']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
