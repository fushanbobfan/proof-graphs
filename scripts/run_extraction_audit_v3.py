#!/usr/bin/env python3
"""Extraction audit v0.3: the corrected step derivation checked on long proofs and on graphs that are not forests.

  python scripts/run_extraction_audit_v3.py --register
  python scripts/run_extraction_audit_v3.py --assignments N --output-dir DIR
  python scripts/run_extraction_audit_v3.py --compare
  python scripts/run_extraction_audit_v3.py --compare-hand
  python scripts/run_extraction_audit_v3.py --check-committed

extraction-audit-v0.1 drew 30 proofs of 2 to 20 steps by length and v0.2 forty by construct, also within 20
steps; a review asked for the proofs both samples left out. This audit draws them from the three corpora (the
library, the first slice, and holdout-v0.1's second slice): every proof whose graph is not a forest, where a step
consumes goals of two origins and the counts use dynamic programming instead of the hook-length formula, and proofs
of 21 to 50 and of 51 to 150 steps. The protocol is v0.2's. Its instructions correct v0.2's description of Lean's
info tree, which v0.2's reconstructors found wrong, and the reconstructors see each proof's location only, not
the stratum that would reveal its derived size or shape.
"""

from __future__ import annotations

import argparse
import collections
import functools
import json
import random
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations_v2 as counter  # noqa: E402
import run_extraction_audit as v1  # noqa: E402
import run_extraction_audit_v2 as v2  # noqa: E402
from run_linearizations import read_gz_lines, sha256_file, write_lf  # noqa: E402
from run_search import generated  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "extraction-audit-v0.3"
PREREG = EXPERIMENT / "preregistration.json"
SAMPLE = EXPERIMENT / "sample.json"
INSTRUCTIONS = EXPERIMENT / "instructions.md"
KIT = EXPERIMENT / "human-kit"
RECONSTRUCTIONS = EXPERIMENT / "reconstructions.json"
ADJUDICATION = EXPERIMENT / "adjudication.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations_v2.py",
                   "base": ROOT / "scripts" / "count_linearizations.py",
                   "v1": ROOT / "scripts" / "run_extraction_audit.py",
                   "v2": ROOT / "scripts" / "run_extraction_audit_v2.py", "runner": Path(__file__).resolve()}
SEED = 20261002
CAP = 150
LONG = {"21-50": (21, 50, 8), "51-150": (51, 150, 6)}
CORPORA = v1.CORPORA | {"holdout-slice": {
    "extraction": ROOT / "experiments" / "holdout-v0.1" / "extraction.jsonl.gz",
    "source": ROOT / ".lake" / "packages" / "mathlib"}}
LEAN_SEMANTICS = [
    "Lean's info tree has a node for each tactic it elaborates, which is not always one node per tactic as written: "
    "`rw [a, b]` has one node per rewrite rule, and one for its closing `rfl` when that closes the goal; `intro x y` "
    "has one per binder; `conv_lhs` and `conv_rhs` insert a `conv` node; `cases h : e with` has two; a named "
    "`next` or `case` that renames hypotheses is a node. A tactic that runs on several goals (the second tactic of "
    "`t <;> s`, the body of `all_goals`) is one node, hence possibly one step, per goal it runs on. Where this list "
    "does not settle a case, Lean's own elaboration does: the goals it displays between tactics, or its source.",
    *v2.LEAN_SEMANTICS[1:]]


def audited() -> set[tuple[str, str]]:
    return {(e["module"], e["declaration"]) for path in (v1.SAMPLE, v2.SAMPLE)
            for e in json.loads(path.read_text(encoding="utf-8"))}


@functools.lru_cache(maxsize=None)
def records(corpus: str) -> dict[tuple[str, str], dict[str, Any]]:
    return {(r["module"], r["declaration"]): r for r in read_gz_lines(CORPORA[corpus]["extraction"])}


def eligible() -> list[dict[str, Any]]:
    """Proofs with one root `by` block, a name that is not generated, 2 to CAP steps, outside both earlier samples."""
    done = audited()
    out = []
    for corpus, paths in CORPORA.items():
        for (module, declaration), record in records(corpus).items():
            roots = [n for n in record["nodes"] if n["parent"] is None]
            if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic") or generated(declaration):
                continue
            if (module, declaration) in done:
                continue
            try:
                steps = counter.derive_steps(record["nodes"])
            except ValueError:
                continue
            if not 2 <= len(steps) <= CAP:
                continue
            source = paths["source"] / (module.replace(".", "/") + ".lean")
            out.append({"corpus": corpus, "module": module, "declaration": declaration,
                        "source": source.relative_to(ROOT).as_posix(), "byLine": roots[0]["line"],
                        "steps": len(steps),
                        "forest": all(len(ps) <= 1 for ps in counter.dependency_graph(steps))})
    out.sort(key=lambda e: (e["corpus"], e["module"], e["byLine"], e["declaration"]))
    return out


def draw_sample() -> list[dict[str, Any]]:
    rng = random.Random(SEED)
    pool = eligible()
    chosen = [e | {"stratum": "non-forest"} for e in pool if not e["forest"]]
    for name, (low, high, count) in LONG.items():
        candidates = [e for e in pool if e["forest"] and low <= e["steps"] <= high]
        chosen += [e | {"stratum": name} for e in rng.sample(candidates, count)]
    return [{k: e[k] for k in ("corpus", "module", "declaration", "source", "byLine", "stratum")} for e in chosen]


def assignments(sample: list[dict[str, Any]], reconstructors: int) -> list[list[dict[str, Any]]]:
    """Proofs dealt in sample order, so that every reconstructor gets a share of every stratum; locations only."""
    parts: list[list[dict[str, Any]]] = [[] for _ in range(reconstructors)]
    for i, entry in enumerate(sample):
        parts[i % reconstructors].append({k: entry[k] for k in ("module", "declaration", "source", "byLine")})
    return parts


def derived_graph(entry: dict[str, Any]) -> tuple[list[dict[str, Any]], list[set[int]]]:
    steps = counter.derive_steps(records(entry["corpus"])[(entry["module"], entry["declaration"])]["nodes"])
    return steps, counter.dependency_graph(steps)


def compare_one(entry: dict[str, Any], rebuilt: dict[str, Any]) -> dict[str, Any]:
    """extraction-audit-v0.1's comparison, against the corrected derivation, for all three corpora."""
    original = v1.derived_graph
    v1.derived_graph = derived_graph  # type: ignore[assignment]
    try:
        return v1.compare_one(entry, rebuilt)
    finally:
        v1.derived_graph = original  # type: ignore[assignment]


def compare(reconstructions: dict[str, Any], sample: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_key = {(p["module"], p["declaration"]): p for p in reconstructions["proofs"]}
    out = []
    for entry in sample:
        rebuilt = by_key.get((entry["module"], entry["declaration"]))
        if rebuilt is None:
            out.append({"corpus": entry["corpus"], "module": entry["module"], "declaration": entry["declaration"],
                        "stratum": entry["stratum"], "missing": True, "edgesAgree": False, "stepsAgree": False,
                        "derivedCount": None, "rebuiltCount": None})
            continue
        out.append(compare_one(entry, rebuilt))
    return out


def summarize(results: list[dict[str, Any]], adjudication: dict[str, Any]) -> dict[str, Any]:
    verdicts = {(a["module"], a["declaration"]): a["category"] for a in adjudication.get("verdicts", [])}
    disagreements = [r for r in results if not r["edgesAgree"]]
    strata = ["non-forest", *LONG]
    categories = collections.Counter(verdicts.get((r["module"], r["declaration"])) for r in disagreements)
    unadjudicated = sorted(r["declaration"] for r in disagreements if (r["module"], r["declaration"]) not in verdicts)
    return {"experiment": "extraction-audit-v0.3", "preregistrationSha256": sha256_file(PREREG),
            "proofs": len(results), "agree": len(results) - len(disagreements),
            "stepsAgree": sum(1 for r in results if r["stepsAgree"]),
            "countsAgree": sum(1 for r in results if r["derivedCount"] == r["rebuiltCount"]),
            "steps": sum(r.get("derivedSteps") or 0 for r in results),
            "byStratum": {s: {"proofs": sum(1 for r in results if r["stratum"] == s),
                              "agree": sum(1 for r in results if r["stratum"] == s and r["edgesAgree"])}
                          for s in strata},
            "byCorpus": {c: sum(1 for r in results if r["corpus"] == c) for c in CORPORA},
            "disagreements": len(disagreements),
            "categories": {c: categories.get(c, 0) for c in v1.CATEGORIES}, "unadjudicated": unadjudicated,
            "hypotheses": {"H82": {"supported": None if unadjudicated else categories.get("extractor error", 0) == 0}},
            "reconstructionsSha256": sha256_file(RECONSTRUCTIONS),
            "adjudicationSha256": sha256_file(ADJUDICATION) if ADJUDICATION.exists() else None,
            "resultsSha256": sha256_file(RESULTS)}


def instructions_text() -> str:
    """v0.2's instructions with the corrected description of the info tree and the line of a rule's step."""
    original = v2.LEAN_SEMANTICS
    v2.LEAN_SEMANTICS = LEAN_SEMANTICS
    try:
        text = v2.instructions_text()
    finally:
        v2.LEAN_SEMANTICS = original
    old = "A step's line is the line of the\ntactic's first token; two steps on one line are listed in the order they run."
    new = ("A step's line is the line where its\ninfo-tree node starts (for a rewrite rule, the rule's own line); "
           "two steps on one line are listed in the order\nthey run. Long proofs are expected: list every step.")
    if old not in text:
        raise SystemExit("v0.2's instructions changed; update the line rule here")
    return text.replace(old, new)


def write_kit(sample: list[dict[str, Any]]) -> None:
    """The person's worksheet: every proof whole, from its root `by` to its last node's line."""
    KIT.mkdir(parents=True, exist_ok=True)
    readme = ["# A reconstruction kit for people", "",
              "The same task as the model reconstructors of this audit, for a person: `../instructions.md` is the",
              "definition and the rules, and `worksheet.md` lists the proofs with their source. Fill in one JSON",
              "entry per proof as the instructions show and save them as a list in `reconstructions-by-hand.json`;",
              "`python scripts/run_extraction_audit_v3.py --compare-hand` then compares them with the derived graphs",
              "without showing those graphs first. Displaying Lean's goals at a line (in an editor with the Lean",
              "extension, opening the source file in this repository's Lean project) is allowed and expected."]
    write_lf(KIT / "README.md", "\n".join(readme) + "\n")
    sheet = ["# Worksheet", ""]
    for i, entry in enumerate(sample, 1):
        lines = v2.source_lines(entry["source"])
        record = records(entry["corpus"])[(entry["module"], entry["declaration"])]
        last = max(n["line"] for n in record["nodes"] if n["line"] is not None)
        sheet += [f"## {i}. `{entry['declaration']}`", "", f"Source: `{entry['source']}`, from line {entry['byLine']}.",
                  "", "```lean"]
        sheet += [f"{n:5d}  {lines[n - 1]}" for n in range(max(1, entry["byLine"] - 2), min(len(lines), last + 1) + 1)]
        sheet += ["```", "", "Steps (line, tactic):", "", "Edges [i, j]:", ""]
    write_lf(KIT / "worksheet.md", "\n".join(sheet) + "\n")


def registration_payload(sample: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "extraction-audit-v0.3",
        "question": "does the corrected step derivation agree with independent reconstructions on long proofs and on "
                    "graphs that are not forests, which the earlier samples left out",
        "sample": {"rule": f"seed {SEED}; every eligible proof whose graph under count_linearizations_v2 is not a forest; "
                           "then, for each long stratum in order, proofs drawn uniformly without replacement among the "
                           "eligible forests of that length; eligible: one root `by` block, a name that is not "
                           f"generated, 2 to {CAP} steps under count_linearizations_v2, from the library, the first "
                           "slice, or holdout-v0.1's slice, not in extraction-audit-v0.1's or v0.2's sample; pool in "
                           "(corpus, module, line, declaration) order",
                   "longStrata": {name: {"steps": [low, high], "count": count} for name, (low, high, count) in LONG.items()},
                   "count": len(sample),
                   "byStratum": dict(collections.Counter(e["stratum"] for e in sample)),
                   "extractionSha256": {c: sha256_file(p["extraction"]) for c, p in CORPORA.items()}},
        "protocol": ["reconstructors receive instructions.md and their proofs' locations (module, declaration, source "
                     "file, line of the root `by`), not the strata; the same instructions serve the human kit",
                     "the model reconstructors are separate language-model agent instances with Lean language-server "
                     "access, the sample dealt among them in sample order; they may read any source file and display "
                     "Lean's goals, and must not open the repository's extractions, results, datasets, audit files, or "
                     "scripts",
                     "reconstructions.json is committed before --compare first runs",
                     "--compare matches steps by source line and order within the line, as extraction-audit-v0.1 does, "
                     "and compares edges with the corrected derivation's",
                     "every disagreement is adjudicated with its evidence into: " + "; ".join(v1.CATEGORIES)],
        "hypotheses": {"H82": "no disagreement is adjudicated as an extractor error"},
        "humanKit": "human-kit/: the instructions, a worksheet with every proof whole, and a comparison mode "
                    "(--compare-hand) for reconstructions by a person; not part of this registration's decision",
        "instructionsSha256": sha256_file(INSTRUCTIONS),
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "none on the sample; the sampling was run once to write sample.json, "
                                               "and the derivation was run on the pool only to decide eligibility, "
                                               "step counts, and forests",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ("register", "compare", "compare-hand", "check-committed"):
        mode.add_argument("--" + name, action="store_true")
    mode.add_argument("--assignments", type=int, metavar="N")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.register:
        if RECONSTRUCTIONS.exists() or PREREG.exists():
            raise SystemExit("registration or reconstructions already exist")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        sample = draw_sample()
        write_lf(SAMPLE, json.dumps(sample, indent=1, ensure_ascii=False) + "\n")
        write_lf(INSTRUCTIONS, instructions_text())
        write_kit(sample)
        write_lf(PREREG, json.dumps(registration_payload(sample), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(sample)} proofs: {PREREG}")
        return 0
    sample = json.loads(SAMPLE.read_text(encoding="utf-8"))
    if args.assignments is not None:
        if args.output_dir is None or ROOT in args.output_dir.resolve().parents:
            raise SystemExit("--assignments needs an --output-dir outside the repository")
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for i, part in enumerate(assignments(sample, args.assignments), 1):
            write_lf(args.output_dir / f"proofs-{i}.json", json.dumps(part, indent=1, ensure_ascii=False) + "\n")
        print(f"{len(sample)} proofs dealt to {args.assignments} reconstructors in {args.output_dir}")
        return 0
    if args.compare_hand:
        hand = json.loads((KIT / "reconstructions-by-hand.json").read_text(encoding="utf-8"))
        names = {p["declaration"] for p in hand}
        for row in compare({"proofs": hand}, [e for e in sample if e["declaration"] in names]):
            print(json.dumps({k: row.get(k) for k in ("declaration", "stratum", "stepsAgree", "edgesAgree")},
                             ensure_ascii=False))
        return 0
    reconstructions = json.loads(RECONSTRUCTIONS.read_text(encoding="utf-8"))
    adjudication = json.loads(ADJUDICATION.read_text(encoding="utf-8")) if ADJUDICATION.exists() else {}
    if args.compare:
        results = compare(reconstructions, sample)
        write_lf(RESULTS, "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in results))
        summary = summarize(results, adjudication)
        write_lf(SUMMARY, json.dumps(summary, indent=1, ensure_ascii=False) + "\n")
        print(json.dumps({k: summary[k] for k in ("proofs", "agree", "stepsAgree", "disagreements", "categories",
                                                  "unadjudicated", "byStratum")}, indent=1))
        return 0
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if committed != json.loads(json.dumps(compare(reconstructions, sample))):
        raise SystemExit("the committed comparison does not follow from the reconstructions")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, adjudication))):
        raise SystemExit("the committed summary does not follow from the comparison")
    print(f"extraction-audit-v0.3-check-ok: proofs={summary['proofs']} agree={summary['agree']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
