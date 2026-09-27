#!/usr/bin/env python3
"""Extraction audit v0.2: the corrected step derivation checked on the constructs it is most likely to get wrong.

  python scripts/run_extraction_audit_v2.py --register
  python scripts/run_extraction_audit_v2.py --compare
  python scripts/run_extraction_audit_v2.py --check-committed

extraction-audit-v0.1 drew 30 proofs by length, found one extractor defect, and left open that a defect confined
to rarer constructs could remain. This audit draws by construct instead: five proofs for each of eight families
that the derivation handles by special rules or that hide goals, recognised in the proof's own text (the extraction
also records nodes that macros expand into, which would count constructs no one wrote):

- `try`, `first`, `repeat` (Lean keeps the info nodes of failed alternatives);
- `<;>`, `all_goals`, `any_goals` (one tactic, several goals);
- `calc` (steps whose goals no node produces);
- `conv` (a conversion inside one goal);
- `case`, `next` (focusing by tag);
- `rcases`, `obtain`, `rintro` (patterns that create several goals and hypotheses);
- `induction`, `cases`, `match` with named alternatives (case goals no node produces);
- a `by` nested inside the proof (a goal that originates in its enclosing node).

The proofs have one `by` block and 2 to 20 steps under the corrected derivation of `count_linearizations_v2.py`,
come from either corpus of step 1, and exclude extraction-audit-v0.1's sample. Reconstructors who have not seen
the derived graphs follow `instructions.md`, the same text a person uses with `human-kit/`; `--compare` matches
steps by source line as in v0.1 and compares edges with the corrected derivation's.
"""

from __future__ import annotations

import argparse
import functools
import json
import random
import re
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations_v2 as counter  # noqa: E402
import run_extraction_audit as v1  # noqa: E402
from run_linearizations import read_gz_lines, sha256_file, write_lf  # noqa: E402
from run_search import generated  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "extraction-audit-v0.2"
PREREG = EXPERIMENT / "preregistration.json"
SAMPLE = EXPERIMENT / "sample.json"
INSTRUCTIONS = EXPERIMENT / "instructions.md"
KIT = EXPERIMENT / "human-kit"
RECONSTRUCTIONS = EXPERIMENT / "reconstructions.json"
ADJUDICATION = EXPERIMENT / "adjudication.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"counter": ROOT / "scripts" / "count_linearizations_v2.py",
                   "base": ROOT / "scripts" / "count_linearizations.py", "runner": Path(__file__).resolve()}
SEED = 20260927
PER_FAMILY = 5
STEPS = (2, 20)
FAMILIES = {
    "try-first-repeat": r"\b(try|first|repeat'?)\b",
    "several-goals": r"<;>|\b(all_goals|any_goals)\b",
    "calc": r"\bcalc\b",
    "conv": r"\bconv(_lhs|_rhs)?\b",
    "case-next": r"(^|\n)[ \t·]*(case|next)\b",
    "patterns": r"\b(rcases|obtain|rintro)\b",
    "alternatives": r"\b(induction|cases|match)\b[^\n]*\bwith\b|(^|\n)[ \t]*\|",
    "nested-by": r"\bby\b",
}
COMMENT = re.compile(r"--[^\n]*|/-.*?-/", re.S)
BY = re.compile(r"\bby\b")


@functools.lru_cache(maxsize=None)
def source_lines(source: str) -> tuple[str, ...]:
    return tuple((ROOT / source).read_text(encoding="utf-8").split("\n"))


def proof_text(entry: dict[str, Any], record: dict[str, Any]) -> str:
    """The proof's source from its root `by` to its last node's line, comments removed, without the root `by`."""
    lines = source_lines(entry["source"])
    last = max(n["line"] for n in record["nodes"] if n["line"] is not None)
    text = COMMENT.sub("", "\n".join(lines[entry["byLine"] - 1:last]))
    head = BY.search(text)
    return text[head.end():] if head else text


def eligible() -> list[dict[str, Any]]:
    audited = {(e["module"], e["declaration"]) for e in json.loads(v1.SAMPLE.read_text(encoding="utf-8"))}
    out = []
    for corpus, paths in v1.CORPORA.items():
        for record in read_gz_lines(paths["extraction"]):
            roots = [n for n in record["nodes"] if n["parent"] is None]
            if len(roots) != 1 or not roots[0]["kind"].endswith("byTactic") or generated(record["declaration"]):
                continue
            if (record["module"], record["declaration"]) in audited:
                continue
            try:
                steps = counter.derive_steps(record["nodes"])
            except ValueError:
                continue
            if not STEPS[0] <= len(steps) <= STEPS[1]:
                continue
            source = paths["source"] / (record["module"].replace(".", "/") + ".lean")
            entry = {"corpus": corpus, "module": record["module"], "declaration": record["declaration"],
                     "source": source.relative_to(ROOT).as_posix(), "byLine": roots[0]["line"],
                     "steps": len(steps)}
            text = proof_text(entry, record)
            entry["families"] = [name for name, pattern in FAMILIES.items() if re.search(pattern, text)]
            if entry["families"]:
                out.append(entry)
    out.sort(key=lambda e: (e["corpus"], e["module"], e["byLine"], e["declaration"]))
    return out


def draw_sample() -> list[dict[str, Any]]:
    rng = random.Random(SEED)
    pool = eligible()
    chosen: set[tuple[str, str]] = set()
    sample = []
    for family in FAMILIES:
        candidates = [e for e in pool if family in e["families"] and (e["module"], e["declaration"]) not in chosen]
        for entry in rng.sample(candidates, PER_FAMILY):
            chosen.add((entry["module"], entry["declaration"]))
            sample.append({k: entry[k] for k in ("corpus", "module", "declaration", "source", "byLine")}
                          | {"family": family})
    return sample


def derived_graph(entry: dict[str, Any]) -> tuple[list[dict[str, Any]], list[set[int]]]:
    extraction = v1.CORPORA[entry["corpus"]]["extraction"]
    record = next(r for r in read_gz_lines(extraction)
                  if r["module"] == entry["module"] and r["declaration"] == entry["declaration"])
    steps = counter.derive_steps(record["nodes"])
    return steps, counter.dependency_graph(steps)


def compare_one(entry: dict[str, Any], rebuilt: dict[str, Any]) -> dict[str, Any]:
    """extraction-audit-v0.1's comparison, against the corrected derivation."""
    original = v1.derived_graph
    v1.derived_graph = derived_graph  # type: ignore[assignment]
    try:
        result = v1.compare_one(entry | {"stratum": entry["family"]}, rebuilt)
    finally:
        v1.derived_graph = original  # type: ignore[assignment]
    return result | {"family": entry["family"]}


def summarize(results: list[dict[str, Any]], adjudication: dict[str, Any]) -> dict[str, Any]:
    verdicts = {(a["module"], a["declaration"]): a["category"] for a in adjudication.get("verdicts", [])}
    disagreements = [r for r in results if not r["edgesAgree"]]
    by_family = {f: {"proofs": sum(1 for r in results if r["family"] == f),
                     "agree": sum(1 for r in results if r["family"] == f and r["edgesAgree"])} for f in FAMILIES}
    categories = {c: sum(1 for r in disagreements if verdicts.get((r["module"], r["declaration"])) == c)
                  for c in v1.CATEGORIES}
    unadjudicated = sum(1 for r in disagreements if (r["module"], r["declaration"]) not in verdicts)
    return {"experiment": "extraction-audit-v0.2", "preregistrationSha256": sha256_file(PREREG),
            "proofs": len(results), "agree": sum(1 for r in results if r["edgesAgree"]),
            "stepsAgree": sum(1 for r in results if r["stepsAgree"]),
            "countsAgree": sum(1 for r in results if r["derivedCount"] == r["rebuiltCount"]),
            "byFamily": by_family, "disagreements": len(disagreements), "categories": categories,
            "unadjudicated": unadjudicated,
            "hypotheses": {"H67": {"supported": None if unadjudicated else categories["extractor error"] == 0}},
            "reconstructionsSha256": sha256_file(RECONSTRUCTIONS), "resultsSha256": sha256_file(RESULTS)}


DEFINITION_CORRECTION = ("Correction (count_linearizations_v2.py): a node consumes a goal present before it, absent "
                         "after it, and never present before a later node of the proof outside the node's own "
                         "subtree. A later node inside the node's own subtree does not count, so a tactic whose own "
                         "internal node mentions the goal it closes (the internal node of `simpa ... using h` that "
                         "leaves the goal as it was) still consumes it.")
LEAN_SEMANTICS = [
    "Lean's info tree has one node per tactic invocation; a tactic that runs on several goals (the second tactic of "
    "`t <;> s`, the body of `all_goals`) is one node, hence possibly one step, per goal it runs on.",
    "Almost every tactic that changes a goal (its target or its local context) replaces that goal with a new goal, "
    "and a tactic that closes a goal produces no goal, so a step that transforms a goal consumes the old goal and "
    "originates the new one.",
    "Focusing (`·`, `next`, `case tag =>` without new names) and tactic sequences only select or hide goals; they "
    "are containers, not steps."]


def instructions_text() -> str:
    base = v1.counter.__doc__ or ""
    derivation = base[base.index("Steps are derived from the nodes:"):base.index("The output fields are:")].strip()
    return "\n".join([
        "# Reconstructing goal-origin graphs by hand", "",
        "For each proof in your list, write down the steps of its goal-origin graph and the dependency edges between",
        "them, following the definition below. Work from the proof's source and from the goals Lean displays; do not",
        "look at any extraction, result, dataset, or audit file of this repository, and do not run its extractor or",
        "its scripts.", "", "## The definition", "", derivation, "", DEFINITION_CORRECTION, "",
        "## How Lean behaves, which the definition relies on", ""] + [f"{i}. {s}" for i, s in
                                                                     enumerate(LEAN_SEMANTICS, 1)] + [
        "", "## What to write down", "",
        "For each proof: its steps in source order, each with the source line where its tactic starts and the tactic",
        "text, and its edges as pairs [i, j] of step indices (0-based, in your step order) meaning that step i",
        "originated a goal that step j consumes. Note anything you were unsure of. A step's line is the line of the",
        "tactic's first token; two steps on one line are listed in the order they run.", "",
        "```json",
        '{"module": "...", "declaration": "...", "steps": [{"line": 12, "tactic": "intro x"}, ...],',
        ' "edges": [[0, 1], ...], "notes": "..."}',
        "```"]) + "\n"


def write_kit(sample: list[dict[str, Any]]) -> None:
    KIT.mkdir(parents=True, exist_ok=True)
    readme = ["# A reconstruction kit for people", "",
              "The same task as the model reconstructors of this audit, for a person: `../instructions.md` is the",
              "definition and the rules, and `worksheet.md` lists the proofs with their source. Fill in one JSON",
              "entry per proof as the instructions show and save them as a list in `reconstructions-by-hand.json`;",
              "`python scripts/run_extraction_audit_v2.py --compare-hand` then compares them with the derived graphs",
              "without showing those graphs first. Displaying Lean's goals at a line (in an editor with the Lean",
              "extension, opening the source file in this repository's Lean project) is allowed and expected."]
    write_lf(KIT / "README.md", "\n".join(readme) + "\n")
    sheet = ["# Worksheet", ""]
    for i, entry in enumerate(sample, 1):
        lines = source_lines(entry["source"])
        start = entry["byLine"]
        end = min(len(lines), start + 40)
        sheet += [f"## {i}. `{entry['declaration']}` ({entry['family']})", "",
                  f"Source: `{entry['source']}`, from line {start}.", "", "```lean"]
        sheet += [f"{n:5d}  {lines[n - 1]}" for n in range(max(1, start - 2), end + 1)]
        sheet += ["```", "", "Steps (line, tactic):", "", "Edges [i, j]:", ""]
    write_lf(KIT / "worksheet.md", "\n".join(sheet) + "\n")


def registration_payload(sample: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "extraction-audit-v0.2",
        "question": "does the corrected step derivation agree with independent reconstructions on proofs that use the "
                    "constructs it handles by special rules or that hide goals",
        "sample": {"rule": f"seed {SEED}; for each of the families in order, {PER_FAMILY} proofs drawn uniformly "
                           "without replacement among those not yet drawn whose text (from the root `by` to the last "
                           "node's line, comments removed) matches the family's pattern; proofs with one root `by` "
                           f"block, a name that is not generated, {STEPS[0]} to {STEPS[1]} steps under "
                           "count_linearizations_v2, from either corpus of step 1, not in extraction-audit-v0.1's "
                           "sample; pool in (corpus, module, line, declaration) order",
                   "families": FAMILIES, "count": len(sample),
                   "libraryExtractionSha256": sha256_file(v1.CORPORA["proofnet-ir"]["extraction"]),
                   "sliceExtractionSha256": sha256_file(v1.CORPORA["mathlib-slice"]["extraction"])},
        "protocol": ["reconstructors receive instructions.md and their part of sample.json; the same instructions "
                     "serve the human kit",
                     "the model reconstructors are separate language-model agent instances with Lean language-server "
                     "access, each given ten proofs; they may read any source file and display Lean's goals, and must "
                     "not open the repository's extractions, results, datasets, audit files, or scripts",
                     "reconstructions.json is committed before --compare first runs",
                     "--compare matches steps by source line as extraction-audit-v0.1 does and compares edges with "
                     "the corrected derivation's",
                     "every disagreement is adjudicated with its evidence into: " + "; ".join(v1.CATEGORIES)],
        "hypotheses": {"H67": "no disagreement is adjudicated as an extractor error"},
        "humanKit": "human-kit/: the instructions, a worksheet with each proof's source, and a comparison mode "
                    "(--compare-hand) for reconstructions by a person; not part of this registration's decision",
        "instructionsSha256": sha256_file(INSTRUCTIONS),
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "otherBackend": "a cross-check with LeanTree (Kripner et al. 2025) was considered: it pins Lean v4.27.0 and "
                        "its own REPL fork, against this project's v4.32.0, so it would need a port or a second "
                        "corpus at the older version; not done here",
        "developmentChecksBeforeRegistration": "none on the sample; the sampling was run once to write sample.json, "
                                               "and the derivation was not run on it beyond counting steps for "
                                               "eligibility",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def compare(reconstructions: dict[str, Any], sample: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_key = {(p["module"], p["declaration"]): p for p in reconstructions["proofs"]}
    out = []
    for entry in sample:
        rebuilt = by_key.get((entry["module"], entry["declaration"]))
        if rebuilt is None:
            out.append({"module": entry["module"], "declaration": entry["declaration"], "family": entry["family"],
                        "missing": True, "edgesAgree": False, "stepsAgree": False, "derivedCount": None,
                        "rebuiltCount": None})
            continue
        out.append(compare_one(entry, rebuilt))
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--compare", action="store_true")
    mode.add_argument("--compare-hand", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    if args.register:
        if RECONSTRUCTIONS.exists():
            raise SystemExit("reconstructions already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        sample = draw_sample()
        write_lf(SAMPLE, json.dumps(sample, indent=1, ensure_ascii=False) + "\n")
        write_lf(INSTRUCTIONS, instructions_text())
        write_kit(sample)
        write_lf(PREREG, json.dumps(registration_payload(sample), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(sample)} proofs: {PREREG}")
        return 0
    sample = json.loads(SAMPLE.read_text(encoding="utf-8"))
    if args.compare_hand:
        hand = json.loads((KIT / "reconstructions-by-hand.json").read_text(encoding="utf-8"))
        for row in compare({"proofs": hand}, [e for e in sample if any(
                p["declaration"] == e["declaration"] for p in hand)]):
            print(json.dumps({k: row.get(k) for k in ("declaration", "family", "stepsAgree", "edgesAgree")},
                             ensure_ascii=False))
        return 0
    reconstructions = json.loads(RECONSTRUCTIONS.read_text(encoding="utf-8"))
    adjudication = json.loads(ADJUDICATION.read_text(encoding="utf-8")) if ADJUDICATION.exists() else {}
    if args.compare:
        results = compare(reconstructions, sample)
        write_lf(RESULTS, "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in results))
        summary = summarize(results, adjudication)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        print(json.dumps({k: summary[k] for k in ("proofs", "agree", "stepsAgree", "disagreements", "categories",
                                                  "unadjudicated", "byFamily")}, indent=1))
        return 0
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if committed != json.loads(json.dumps(compare(reconstructions, sample))):
        raise SystemExit("the committed comparison does not follow from the reconstructions")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, adjudication))):
        raise SystemExit("the committed summary does not follow from the comparison")
    print(f"extraction-audit-v0.2-check-ok: proofs={summary['proofs']} agree={summary['agree']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
