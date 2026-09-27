#!/usr/bin/env python3
"""An audit of the goal keys on the recorded goals of the step-prover searches (not registered).

  python scripts/audit_goal_keys.py            # write experiments/goal-key-audit/audit.json
  python scripts/audit_goal_keys.py --check    # recompute and compare with the committed file

A review of 2026-09-26 showed two ways the text keys can merge different goals. The default key erases
metavariable numbers, so `R ?m.1 ?m.1` and `R ?m.1 ?m.2` coincide although one reuses an unknown and the other
does not. The coarse key renames hypotheses to `h0`, `h1`, ... by text substitution, which can capture a bound
variable already named `h0`: with `x : Nat`, `∀ h0, x = h0` and `∀ h0, h0 = h0` coincide. Neither was measured
on the experiments' goals.

The searches record keys as digests, but search-v0.6 and v0.7 logged the goal text behind every draw, and every
expansion used a draw of its first goal's default key in its task. So the default text of each whole-state
expansion's first goal is recovered, checked against the recorded coarse digest, and re-keyed with a *safe
coarse* key: the default text with every hypothesis renamed to a placeholder (`◊0`, `◊1`, ...) that no Lean goal
prints (`renaming.masked`), so that no bound name is captured and two goals coincide only if they are alike up to
a consistent renaming of those names. For every whole-state search the goal-duplicate share is recomputed under
the recorded keys, which must reproduce the recorded shares, and under the safe key.

The recovered text is one logged goal per default key and occurrence, not necessarily the goal each expansion
saw, so metavariable patterns can only be compared among the logged goals themselves: within a task, the default
keys whose logged goals differ once metavariables are numbered by first occurrence instead of erased. Few keys have
two logged goals, so that comparison has little power; what bounds the erasure's effect is how many goal
duplicates have a first goal with a metavariable at all, since only those can be merges the erasure made. What no
text key fixes, goals alike up to the names of bound variables, is not measured.
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_search_keys as rsk  # noqa: E402
from renaming import hypotheses, masked  # noqa: E402
from search_harness import canonical_goal  # noqa: E402
from search_keys import coarse_goal, digest  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "goal-key-audit" / "audit.json"
SEPARATOR = ":::"
RUNS = {"search-v0.6": ("whole",), "search-v0.7": ("whole", "wholeRenamed")}
MVAR = re.compile(r"\?m\.\d+|\?u\.\d+|_uniq\.\d+")


def read_gz(path: Path) -> list[dict[str, Any]]:
    return [json.loads(l) for l in gzip.decompress(path.read_bytes()).decode("utf-8").splitlines() if l.strip()]


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]


def safe_coarse(goal: str) -> str:
    return masked(goal, list(range(len(hypotheses(goal)))))


def mvar_pattern(goal: str) -> str:
    """The goal without its case tag, metavariables numbered by first occurrence within each kind."""
    lines = goal.split("\n")
    text = "\n".join(lines[1:] if lines and lines[0].startswith("case ") else lines)
    seen: dict[str, str] = {}

    def number(match: re.Match[str]) -> str:
        token = match.group(0)
        kind = token.split(".")[0]
        if token not in seen:
            seen[token] = f"{kind}.#{sum(1 for t in seen if t.split('.')[0] == kind)}"
        return seen[token]
    return MVAR.sub(number, text)


def goals_by_task() -> dict[int, list[str]]:
    """Every logged goal text, per task index (search-v0.6's draws, which seed search-v0.7's, and v0.7's new ones)."""
    out: dict[int, list[str]] = {}
    for run in ("search-v0.6", "search-v0.7"):
        for entry in read_gz(ROOT / "experiments" / run / "draws.jsonl.gz"):
            out.setdefault(entry["index"], []).append(entry["prompt"][:-len(SEPARATOR)])
    return out


def whole_state_shares(run: str, search: str, texts: dict[int, dict[str, str]]) -> dict[str, Any]:
    rows = [r for r in read_jsonl(ROOT / "experiments" / run / "results.jsonl")
            if r["search"] == search and "result" in r]
    recorded = {"default": 0, "coarse": 0}
    recomputed = {"default": 0, "coarse": 0, "safeCoarse": 0}
    expansions = unrecovered = mismatches = with_mvar = duplicates_with_mvar = 0
    for row in rows:
        steps = row["result"]["expansions"]
        for key in recorded:
            recorded[key] += sum(1 for f in rsk.flags(steps, key) if f is not None and f[1])
        by_digest = texts.get(row["index"], {})
        seen: dict[str, set[Any]] = {key: set() for key in recomputed}
        for step in steps:
            expansions += 1
            first = step["keys"]["default"][0] if step["keys"]["default"] else ""
            text = by_digest.get(first)
            if text is None:
                unrecovered += 1
                values: dict[str, Any] = {key: ("digest", first) for key in recomputed}
            else:
                mismatches += digest(coarse_goal(text)) != step["keys"]["coarse"][0]
                with_mvar += bool(MVAR.search(text))
                values = {"default": canonical_goal(text), "coarse": coarse_goal(text), "safeCoarse": safe_coarse(text)}
            duplicates_with_mvar += text is not None and values["default"] in seen["default"] \
                and bool(MVAR.search(text))
            for key, value in values.items():
                recomputed[key] += value in seen[key]
                seen[key].add(value)
    return {"units": len(rows), "expansions": expansions, "unrecovered": unrecovered,
            "coarseDigestMismatches": mismatches, "firstGoalsWithMetavariable": with_mvar,
            "goalDuplicatesWithMetavariable": duplicates_with_mvar,
            "goalDuplicates": {"recorded": recorded, "recomputed": recomputed},
            "shares": {"recordedDefault": round(recorded["default"] / expansions, 6),
                       "recordedCoarse": round(recorded["coarse"] / expansions, 6),
                       "safeCoarse": round(recomputed["safeCoarse"] / expansions, 6)}}


def logged_goal_collisions(goals: dict[int, list[str]]) -> dict[str, Any]:
    """Within each task: default keys whose logged goals differ in metavariable pattern, and coarse-key classes that
    the safe coarse key splits."""
    default_keys = with_mvar = comparable = pattern_split = coarse_classes = coarse_split = 0
    examples: dict[str, list[list[str]]] = {"pattern": [], "capture": []}
    for index in sorted(goals):
        by_default: dict[str, set[str]] = {}
        for text in goals[index]:
            by_default.setdefault(canonical_goal(text), set()).add(text)
        default_keys += len(by_default)
        for key in sorted(by_default):
            texts = by_default[key]
            with_mvar += any(MVAR.search(t) for t in texts)
            comparable += len(texts) > 1 and any(MVAR.search(t) for t in texts)
            patterns = sorted({mvar_pattern(t) for t in texts})
            if len(patterns) > 1:
                pattern_split += 1
                if len(examples["pattern"]) < 3:
                    examples["pattern"].append(patterns[:2])
        by_coarse: dict[str, set[str]] = {}
        for key in by_default:
            by_coarse.setdefault(coarse_goal(key), set()).add(key)
        for coarse in sorted(by_coarse):
            members = by_coarse[coarse]
            if len(members) < 2:
                continue
            coarse_classes += 1
            if len({safe_coarse(m) for m in members}) > 1:
                coarse_split += 1
                if len(examples["capture"]) < 3:
                    examples["capture"].append(sorted(members)[:2])
    return {"tasks": len(goals), "defaultKeys": default_keys, "defaultKeysWithMetavariable": with_mvar,
            "defaultKeysWithMetavariableAndSeveralLoggedGoals": comparable,
            "defaultKeysWithSeveralPatterns": pattern_split, "coarseClassesMergingSeveralDefaultKeys": coarse_classes,
            "coarseClassesSplitBySafeKey": coarse_split, "examples": examples}


def audit() -> dict[str, Any]:
    goals = goals_by_task()
    texts: dict[int, dict[str, str]] = {}
    for index in sorted(goals):
        for text in goals[index]:
            texts.setdefault(index, {}).setdefault(digest(canonical_goal(text)), text)
    return {"note": "not registered: an audit of the text keys on the logged goals of search-v0.6 and v0.7, made "
                    "after a review of 2026-09-26; no registered result changes",
            "wholeState": {f"{run}/{search}": whole_state_shares(run, search, texts)
                           for run, searches in RUNS.items() for search in searches},
            "loggedGoals": logged_goal_collisions(goals)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.check:
        if json.loads(OUT.read_text(encoding="utf-8")) != json.loads(json.dumps(result, ensure_ascii=False)):
            raise SystemExit("the committed goal-key audit does not follow from the committed logs")
        print("goal-key-audit-check-ok")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_bytes((json.dumps(result, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))
    print(json.dumps({k: {x: v[x] for x in ("expansions", "unrecovered", "coarseDigestMismatches",
                                             "firstGoalsWithMetavariable", "goalDuplicatesWithMetavariable",
                                             "goalDuplicates", "shares")}
                      for k, v in result["wholeState"].items()}, indent=1))
    print(json.dumps({k: v for k, v in result["loggedGoals"].items() if k != "examples"}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
