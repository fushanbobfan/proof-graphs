#!/usr/bin/env python3
"""Do golfed proofs have a different goal-dependency graph? Register, run, check.

  python scripts/run_golf.py --register
  python scripts/run_golf.py --run [--workers 6]
  python scripts/run_golf.py --recount
  python scripts/run_golf.py --check-committed

The corpus is every golf pair (`scripts/mine_golf.py`) of Mathlib between
the tags v4.29.0 and v4.32.0: a theorem whose proof a golf commit replaced,
with the statement unchanged and the replacing proof still verbatim at
v4.32.0. Both proofs are elaborated in the v4.32.0 environment: the module
as it is (the golfed proof), and the module with the golfed proof replaced by
its predecessor. The extractor and the counter are those of
linearizations-v0.1 after its amendments, unchanged.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mine_golf  # noqa: E402
import run_linearizations as base  # noqa: E402
from run_linearizations import (count, find_lake, format_count, int_quantiles, quantiles, read_gz_lines,  # noqa: E402
                                same_row, sha256_file, write_gz, write_lf)

ROOT = base.ROOT
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
EXPERIMENT = ROOT / "experiments" / "golf-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
PAIRS = EXPERIMENT / "pairs.jsonl.gz"
EXTRACTION = EXPERIMENT / "extraction.jsonl.gz"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
LOWER, UPPER = "v4.29.0", "v4.32.0"
IMPLEMENTATIONS = {
    "extractor": base.IMPLEMENTATIONS["extractor"],
    "extractorMain": base.IMPLEMENTATIONS["extractorMain"],
    "counter": base.IMPLEMENTATIONS["counter"],
    "miner": ROOT / "scripts" / "mine_golf.py",
    "runner": Path(__file__).resolve(),
}
ALPHA = 0.05
MIN_STRUCTURE_STEPS = 3
CHECK_SAMPLE = 2
# the elaboration options of Mathlib's `lake build` (its lakefile's `mathlibLeanOptions`, linters and
# pretty-printing aside), which the extractor, elaborating with Lean's defaults, would otherwise miss
MATHLIB_OPTIONS = ["set_option autoImplicit false", "set_option maxSynthPendingDepth 3"]
HEADER_LINE = __import__("re").compile(r"(module|prelude|(public\s+)?(meta\s+)?import\s)")


def amendments() -> list[Path]:
    return sorted(EXPERIMENT.glob("amendment-*.json"), key=lambda p: int(p.stem.split("-")[1]))


def expected_implementation_hashes(prereg: dict[str, Any]) -> dict[str, str]:
    expected = dict(prereg["implementationSha256"])
    for path in amendments():
        expected.update(json.loads(path.read_text(encoding="utf-8")).get("implementationSha256AfterAmendment", {}))
    return expected


def mathlib_revision() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    return next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")


def sign_test_upper(k: int, n: int) -> float | None:
    """P(X >= k) for X ~ Binomial(n, 1/2): the one-sided p-value of k successes in n."""
    if n == 0:
        return None
    return sum(math.comb(n, i) for i in range(k, n + 1)) / 2 ** n


def registration_payload(pairs: list[dict[str, Any]], totals: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "golf-v0.1",
        "question": "does the goal-dependency graph distinguish a proof from the proof Mathlib's reviewers "
                    "accepted as its golfed replacement, i.e. is the structure index a candidate signal of "
                    "proof quality (the third layer of the original proposal)",
        "corpus": {"repository": "Mathlib", "revision": mathlib_revision(), "window": [LOWER, UPPER],
                   "rule": "every golf pair of scripts/mine_golf.py: first-parent commits between the tags whose "
                           "subject contains 'golf', theorems and lemmas whose statement is unchanged and whose "
                           "proof changed, whose golfed text is verbatim and unique in the file at the upper tag; "
                           "a declaration golfed twice keeps its last golf",
                   "mining": totals, "pairsSha256": sha256_file(PAIRS)},
        "procedure": "each module is elaborated as it is at the upper tag (the golfed proofs) and, once per pair, "
                     "with the golfed text replaced by the predecessor text; a variant with any elaboration error "
                     "excludes its pair; the declaration's record is the extractor record whose name ends with the "
                     "declaration's name and whose first node lies in the declaration's lines; no record means no "
                     "tactic step (a term proof)",
        "quantities": "steps, linearizations, and the structure index log L / log n! of linearizations-v0.1, per "
                      "side; a term proof has 0 steps and no structure index",
        "hypotheses": {
            "H20": f"among pairs whose step counts differ, the golfed proof has fewer steps in more than half "
                   f"(one-sided sign test, alpha {ALPHA})",
            "H21": f"among pairs where both proofs have at least {MIN_STRUCTURE_STEPS} steps and their structure "
                   f"indices differ, the golfed proof has the lower index in more than half (one-sided sign test, "
                   f"alpha {ALPHA}); this is the proposal's candidate: fewer orderings relative to n! means a more "
                   "structured proof",
        },
        "secondary": "H21 repeated at the commit level (each commit's majority direction, ties dropped); the "
                     "fraction of pairs whose steps and linearizations are unchanged (golfs the graph does not "
                     "see); the lower-tail p-value of H21 is reported so that a significant effect in the other "
                     "direction is visible",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": "the miner was run on four windows (v4.28.0, v4.29.0, v4.30.0, "
                                                "v4.31.0 to v4.32.0: 511, 306, 75, 27 pairs) and three pairs' texts "
                                                "were read to check the mining; the splice-and-extract procedure was "
                                                "exercised on two pairs from golf commits before v4.29.0 (outside "
                                                "the corpus): one predecessor failed to elaborate, the other pair "
                                                "matched both records; no corpus pair was elaborated and no graph "
                                                "quantity of the corpus was computed",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def extract_file(module: str, path: Path) -> tuple[list[dict[str, Any]], str]:
    completed = subprocess.run([find_lake(), "exe", "proof_graph_extract", module, str(path)], cwd=ROOT,
                               capture_output=True, text=True, encoding="utf-8")
    diagnostics = [line for line in completed.stderr.splitlines() if ": modules=" in line]
    records = [json.loads(line) for line in completed.stdout.splitlines() if line.startswith("{")]
    text = diagnostics[0] if diagnostics else f"exit {completed.returncode}: {completed.stderr[-300:]}"
    # rendered errors carry file paths; keep machine paths out of the committed artifacts
    for local, placeholder in ((str(path), "<file>"), (str(ROOT), "<root>"), (str(Path.home()), "<home>")):
        text = text.replace(local, placeholder)
    return records, text


def match_record(records: list[dict[str, Any]], name: str, first_line: int, lines: int) -> dict[str, Any] | None:
    last_line = first_line + lines - 1
    found = [r for r in records
             if (r["declaration"] == name or r["declaration"].endswith("." + name))
             and r["nodes"] and first_line <= min(n["line"] for n in r["nodes"]) <= last_line]
    return found[0] if len(found) == 1 else None


def with_mathlib_options(text: str) -> tuple[str, int]:
    """The file with Mathlib's elaboration options inserted where its header
    ends (after the copyright comment, `module`, and the imports), and the
    number of lines inserted."""
    lines = text.split("\n")
    index, in_comment = 0, False
    while index < len(lines):
        line = lines[index].strip()
        if in_comment:
            in_comment = "-/" not in line
        elif line.startswith("/-") and not line.startswith("/-!") and not line.startswith("/--"):
            in_comment = "-/" not in line[2:]
        elif not (line == "" or line.startswith("--") or HEADER_LINE.match(line)):
            break
        index += 1
    return "\n".join(lines[:index] + MATHLIB_OPTIONS + lines[index:]), len(MATHLIB_OPTIONS)


def module_text(module: str) -> str:
    """The module's text at the upper tag, as git stores it (LF line endings,
    whatever the working tree's checkout converted them to)."""
    path = "/".join(module.split(".")) + ".lean"
    text = mine_golf.git_show(MATHLIB, UPPER, path)
    if text is None:
        raise SystemExit(f"{path} is not in {UPPER}")
    return text


def extract_module(module: str, pairs: list[dict[str, Any]], scratch: Path) -> list[dict[str, Any]]:
    """The extraction rows of one module: its golfed proofs, then each predecessor variant. Both
    sides are elaborated from scratch files: the upper tag's text with Mathlib's options inserted,
    and the same with the golfed text replaced by the predecessor text."""
    golfed, shift = with_mathlib_options(module_text(module))
    stem = module.replace(".", "_")
    path = scratch / f"{stem}.lean"
    path.write_bytes(golfed.encode("utf-8"))
    records, diagnostics = extract_file(module, path)
    path.unlink()
    original_ok = "errors=0" in diagnostics
    rows = []
    for pair in pairs:
        first_line = pair["upperLine"] + shift
        after = match_record(records, pair["name"], first_line, pair["afterLines"]) if original_ok else None
        rows.append({"pair": pair["id"], "side": "after", "ok": original_ok, "diagnostics": diagnostics,
                     "record": after})
        if golfed.count(pair["after"]) != 1:
            rows.append({"pair": pair["id"], "side": "before", "ok": False,
                         "diagnostics": "splice failed: the golfed text is not unique in the module", "record": None})
            continue
        variant = golfed.replace(pair["after"], pair["before"], 1)
        path = scratch / f"{stem}.{pair['id']}.lean"
        path.write_bytes(variant.encode("utf-8"))
        variant_records, variant_diagnostics = extract_file(module, path)
        path.unlink()
        variant_ok = "errors=0" in variant_diagnostics
        before = match_record(variant_records, pair["name"], first_line, pair["beforeLines"]) \
            if variant_ok else None
        rows.append({"pair": pair["id"], "side": "before", "ok": variant_ok, "diagnostics": variant_diagnostics,
                     "record": before})
    return rows


def pair_results(pairs: list[dict[str, Any]], extraction: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_key = {(row["pair"], row["side"]): row for row in extraction}
    # keyed by (pair, side): the two sides of a pair usually share module, name, and first line
    with_records = [row for row in extraction if row["record"] is not None]
    counted = {(row["pair"], row["side"]): c
               for row, c in zip(with_records, count([row["record"] for row in with_records]))}
    out = []
    for pair in pairs:
        row = {"pair": pair["id"], "commit": pair["commit"], "module": pair["module"], "name": pair["name"]}
        for side in ("before", "after"):
            extracted = by_key[(pair["id"], side)]
            record = extracted["record"]
            if not extracted["ok"]:
                row[side] = {"status": "elaboration errors"}
            elif record is None:
                row[side] = {"status": "no tactic record", "steps": 0}
            else:
                c = counted[(pair["id"], side)]
                row[side] = {"status": "ok", "steps": c["steps"], "linearizations": c["linearizations"],
                             "structure": c["structure"], "forest": c["forest"], "roots": c["roots"]}
        both = row["before"]["status"] != "elaboration errors" and row["after"]["status"] != "elaboration errors"
        row["status"] = "ok" if both else ("before fails" if row["after"]["status"] != "elaboration errors"
                                           else "original fails")
        out.append(row)
    return out


def summarize(results: list[dict[str, Any]]) -> dict[str, Any]:
    ok = [r for r in results if r["status"] == "ok"]
    step_pairs = [(r["before"]["steps"], r["after"]["steps"]) for r in ok]
    differ = [(b, a) for b, a in step_pairs if b != a]
    fewer = sum(1 for b, a in differ if a < b)
    eligible = [r for r in ok if r["before"]["steps"] >= MIN_STRUCTURE_STEPS and r["after"]["steps"] >= MIN_STRUCTURE_STEPS
                and r["before"].get("structure") is not None and r["after"].get("structure") is not None]
    structure_differ = [r for r in eligible if r["before"]["structure"] != r["after"]["structure"]]
    lower = sum(1 for r in structure_differ if r["after"]["structure"] < r["before"]["structure"])
    p20 = sign_test_upper(fewer, len(differ))
    p21 = sign_test_upper(lower, len(structure_differ))
    p21_other = sign_test_upper(len(structure_differ) - lower, len(structure_differ))
    by_commit: dict[str, list[int]] = {}
    for r in structure_differ:
        by_commit.setdefault(r["commit"], []).append(1 if r["after"]["structure"] < r["before"]["structure"] else -1)
    commit_votes = [sum(v) for v in by_commit.values() if sum(v) != 0]
    commit_lower = sum(1 for v in commit_votes if v > 0)
    unchanged = sum(1 for r in ok if r["before"]["steps"] == r["after"]["steps"]
                    and r["before"].get("linearizations") == r["after"].get("linearizations"))
    reductions = [b - a for b, a in step_pairs]
    return {
        "experiment": "golf-v0.1", "preregistrationSha256": sha256_file(PREREG),
        "amendmentsSha256": {p.name: sha256_file(p) for p in amendments()},
        "pairs": len(results), "ok": len(ok),
        "excluded": {s: sum(1 for r in results if r["status"] == s) for s in ("before fails", "original fails")},
        "commits": len({r["commit"] for r in ok}),
        "steps": {"before": quantiles([b for b, _ in step_pairs]), "after": quantiles([a for _, a in step_pairs]),
                  "reduction": quantiles(reductions),
                  "termProofs": {"before": sum(1 for b, _ in step_pairs if b == 0),
                                 "after": sum(1 for _, a in step_pairs if a == 0)}},
        "graphUnchanged": unchanged,
        "H20": {"pairsDiffering": len(differ), "golfedFewer": fewer, "golfedMore": len(differ) - fewer,
                "pValue": p20, "supported": p20 is not None and p20 < ALPHA},
        "H21": {"eligible": len(eligible), "pairsDiffering": len(structure_differ), "golfedLower": lower,
                "golfedHigher": len(structure_differ) - lower, "pValue": p21, "pValueOtherDirection": p21_other,
                "supported": p21 is not None and p21 < ALPHA,
                "structureBefore": quantiles([r["before"]["structure"] for r in eligible]),
                "structureAfter": quantiles([r["after"]["structure"] for r in eligible]),
                "commitLevel": {"commits": len(commit_votes), "golfedLower": commit_lower,
                                "pValue": sign_test_upper(commit_lower, len(commit_votes)),
                                "pValueOtherDirection": sign_test_upper(len(commit_votes) - commit_lower,
                                                                        len(commit_votes))}},
        "extractionSha256": sha256_file(EXTRACTION), "resultsSha256": sha256_file(RESULTS),
        "pairsSha256": sha256_file(PAIRS),
    }


def write_report(summary: dict[str, Any]) -> None:
    h20, h21 = summary["H20"], summary["H21"]
    s = summary["steps"]

    def q(entry: dict[str, Any] | None, digits: int = 0) -> str:
        if not entry:
            return "n/a"
        f = f"{{:.{digits}f}}"
        return f"{f.format(entry['median'])} ({f.format(entry['q1'])}, {f.format(entry['q3'])})"

    def p(value: float | None) -> str:
        return "n/a" if value is None else f"{value:.3g}"

    lines = ["# Golfed proofs and their predecessors (golf v0.1)", "",
             f"Golf pairs of Mathlib between {LOWER} and {UPPER}, both proofs elaborated at {UPPER}; definitions,",
             "corpus, and hypotheses are frozen in `preregistration.json` (SHA-256",
             "`" + summary["preregistrationSha256"] + "`).", "",
             f"Pairs: {summary['pairs']}; elaborated on both sides: {summary['ok']} from {summary['commits']} commits; "
             f"predecessor fails at {UPPER}: {summary['excluded']['before fails']}; golfed module fails: "
             f"{summary['excluded']['original fails']}.", "",
             "| Quantity | Predecessor | Golfed |", "| --- | --- | --- |",
             f"| Steps, median (q1, q3) | {q(s['before'])} | {q(s['after'])} |",
             f"| Term proofs (no tactic step) | {s['termProofs']['before']} | {s['termProofs']['after']} |",
             f"| Structure index, median (q1, q3), both sides at least {MIN_STRUCTURE_STEPS} steps | "
             f"{q(h21['structureBefore'], 3)} | {q(h21['structureAfter'], 3)} |", "",
             f"Pairs whose steps and linearizations are unchanged (golfs the graph does not see): "
             f"{summary['graphUnchanged']} of {summary['ok']}.", "",
             "## Hypotheses", "",
             f"- H20 (golfed proof has fewer steps, among {h20['pairsDiffering']} pairs that differ): fewer "
             f"{h20['golfedFewer']}, more {h20['golfedMore']}, p = {p(h20['pValue'])}; supported: {h20['supported']}.",
             f"- H21 (golfed proof has the lower structure index, among {h21['pairsDiffering']} pairs that differ): "
             f"lower {h21['golfedLower']}, higher {h21['golfedHigher']}, p = {p(h21['pValue'])} (other direction "
             f"p = {p(h21['pValueOtherDirection'])}); supported: {h21['supported']}.",
             f"- H21 by commit ({h21['commitLevel']['commits']} commits with a majority): lower "
             f"{h21['commitLevel']['golfedLower']}, p = {p(h21['commitLevel']['pValue'])} (other direction "
             f"p = {p(h21['commitLevel']['pValueOtherDirection'])}).", "",
             "## Interpretation boundary", "",
             "A golf is what Mathlib's reviewers accepted as a better proof of the same statement, which is",
             "one notion of quality among several (shorter, faster, more robust, more idiomatic). Pairs whose",
             f"predecessor no longer elaborates at {UPPER} are excluded, which removes golfs that deleted the",
             "lemmas their predecessors used."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--recount", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()

    if args.register:
        if RESULTS.exists() or EXTRACTION.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        pairs, totals = mine_golf.mine(MATHLIB, LOWER, UPPER)
        for index, pair in enumerate(pairs):
            pair["id"] = f"p{index:03d}"
        write_gz(PAIRS, "".join(json.dumps(p, ensure_ascii=False) + "\n" for p in pairs))
        payload = registration_payload(pairs, totals)
        write_lf(PREREG, json.dumps(payload, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(pairs)} pairs from {totals['commitsWithPairs']} commits: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["revision"] != mathlib_revision():
        raise SystemExit("mathlib revision changed since registration")
    if prereg["corpus"]["pairsSha256"] != sha256_file(PAIRS):
        raise SystemExit("pairs changed since registration")
    expected = expected_implementation_hashes(prereg)
    for name in ("extractor", "extractorMain", "counter"):
        if expected[name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration or the last amendment")
    pairs = read_gz_lines(PAIRS)
    by_module: dict[str, list[dict[str, Any]]] = {}
    for pair in pairs:
        by_module.setdefault(pair["module"], []).append(pair)

    if args.run:
        extraction: list[dict[str, Any]] = []
        with tempfile.TemporaryDirectory(prefix="golf-") as scratch, \
                concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(extract_module, m, ps, Path(scratch)): m for m, ps in by_module.items()}
            for done, future in enumerate(concurrent.futures.as_completed(futures), 1):
                rows = future.result()
                extraction += rows
                print(f"{done}/{len(futures)} {futures[future]}: "
                      f"{sum(1 for r in rows if r['ok'])}/{len(rows)} sides elaborated", flush=True)
        order = {(p["id"], side): i for i, (p, side) in enumerate((p, s) for p in pairs for s in ("after", "before"))}
        extraction.sort(key=lambda r: order[(r["pair"], r["side"])])
        write_gz(EXTRACTION, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n"
                                     for r in extraction))
    if args.run or args.recount:
        extraction = read_gz_lines(EXTRACTION)
        results = pair_results(pairs, extraction)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in results))
        summary = summarize(results)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({"golf-run": {"ok": summary["ok"], "H20": summary["H20"]["supported"],
                                       "H21": summary["H21"]["supported"]}}))
        return 0

    extraction = read_gz_lines(EXTRACTION)
    committed = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    recomputed = pair_results(pairs, extraction)
    for fresh_row, committed_row in zip(recomputed, committed):
        for side in ("before", "after"):
            a, b = fresh_row[side], committed_row[side]
            if a.get("status") != b.get("status") or a.get("steps") != b.get("steps") \
                    or a.get("linearizations") != b.get("linearizations") \
                    or (a.get("structure") is None) != (b.get("structure") is None) \
                    or (a.get("structure") is not None and not math.isclose(a["structure"], b["structure"],
                                                                             rel_tol=1e-9, abs_tol=1e-9)):
                raise SystemExit(f"recounted results differ at {committed_row['pair']} {side}")
    if len(recomputed) != len(committed):
        raise SystemExit("recounted a different number of pairs")
    sizes = {m: len(module_text(m)) for m in by_module}
    sample = sorted(sizes, key=lambda m: (sizes[m], m))[:CHECK_SAMPLE]
    with tempfile.TemporaryDirectory(prefix="golf-check-") as scratch:
        for module in sample:
            fresh = {(r["pair"], r["side"]): r for r in extract_module(module, by_module[module], Path(scratch))}
            for (pair_id, side), row in fresh.items():
                old = next(r for r in extraction if r["pair"] == pair_id and r["side"] == side)
                shape = lambda rec: None if rec is None else [  # noqa: E731
                    (n["index"], n["parent"], n["leaf"], n["kind"], len(n["before"]), len(n["after"]))
                    for n in rec["nodes"]]
                if row["ok"] != old["ok"] or shape(row["record"]) != shape(old["record"]):
                    raise SystemExit(f"re-extraction differs for {pair_id} {side}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["extractionSha256"] != sha256_file(EXTRACTION) or summary["resultsSha256"] != sha256_file(RESULTS) \
            or summary["preregistrationSha256"] != sha256_file(PREREG) or summary["pairsSha256"] != sha256_file(PAIRS) \
            or summary["amendmentsSha256"] != {p.name: sha256_file(p) for p in amendments()}:
        raise SystemExit("summary hashes do not match the committed files")
    print(f"golf-check-ok: pairs={len(committed)} sampleModules={len(sample)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
