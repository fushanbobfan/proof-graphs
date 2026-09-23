#!/usr/bin/env python3
"""Structural invariants of the step graphs derived from committed extractions.

  python scripts/audit_graphs.py            # every committed extraction
  python scripts/audit_graphs.py FILE ...   # given extraction files

For every declaration, the step graph that `scripts/count_linearizations.py`
derives must satisfy:

- one root step per root `by` block: a declaration whose tactic nodes have
  one root node has at most one step without a parent;
- a step without a parent consumes a goal, and only goals of root nodes;
- no goal is consumed by two steps or originated by two steps;
- for graphs of 2 to 7 steps, the exact count equals a brute-force count of
  the permutations that respect the edges.

These are the checks that caught the defects recorded in amendments 1, 2,
and 4 of `linearizations-v0.1`. Violations are listed; the exit status is 1
when there is any.
"""

from __future__ import annotations

import collections
import itertools
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import count_linearizations as counter  # noqa: E402
from run_linearizations import read_gz_lines  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = [ROOT / "experiments" / "linearizations-v0.1" / "extraction.jsonl.gz",
           ROOT / "experiments" / "linearizations-mathlib-v0.1" / "extraction.jsonl.gz",
           ROOT / "experiments" / "golf-v0.1" / "extraction.jsonl.gz"]
BRUTE_FORCE_MAX = 7


def records_of(path: Path) -> list[dict[str, Any]]:
    """Declaration records of an extraction file; golf rows wrap theirs in `record`."""
    out = []
    for row in read_gz_lines(path):
        if "nodes" in row:
            out.append(row)
        elif row.get("record") is not None:
            out.append(row["record"] | {"declaration": f"{row['record']['declaration']} ({row['pair']} {row['side']})"})
    return out


def violations(record: dict[str, Any]) -> tuple[list[str], bool]:
    """The invariants the record's graph breaks, and whether it was brute-forced."""
    nodes = record["nodes"]
    steps = counter.derive_steps(nodes)
    parents = counter.dependency_graph(steps)
    root_nodes = [n for n in nodes if n["parent"] is None]
    root_goals = {g for n in root_nodes for g in n["before"]}
    root_steps = [i for i, ps in enumerate(parents) if not ps]
    found = []
    if len(root_nodes) == 1 and len(root_steps) > 1:
        found.append(f"one root node but {len(root_steps)} root steps")
    for i in root_steps:
        if not steps[i]["consumed"]:
            found.append(f"root step {i} ({steps[i]['kind'].split('.')[-1]}, line {steps[i]['line']}) consumes nothing")
        elif any(g not in root_goals for g in steps[i]["consumed"]):
            found.append(f"root step {i} consumes a goal that is not a root node's")
    consumed = collections.Counter(g for s in steps for g in s["consumed"])
    produced = collections.Counter(g for s in steps for g in s["produced"])
    if any(c > 1 for c in consumed.values()):
        found.append("a goal is consumed twice")
    if any(c > 1 for c in produced.values()):
        found.append("a goal is originated twice")
    brute = 2 <= len(steps) <= BRUTE_FORCE_MAX
    if brute:
        n = len(steps)
        permutations = sum(1 for order in itertools.permutations(range(n))
                           if all(order.index(p) < order.index(i) for i in range(n) for p in parents[i]))
        if str(permutations) != counter.analyse(record)["linearizations"]:
            found.append(f"count differs from brute force ({permutations})")
    return found, brute


def main() -> int:
    paths = [Path(p) for p in sys.argv[1:]] or DEFAULT
    total_bad = 0
    for path in paths:
        records = records_of(path)
        bad, brute = [], 0
        for record in records:
            found, forced = violations(record)
            brute += forced
            if found:
                bad.append((record["module"], record["declaration"], found))
        total_bad += len(bad)
        print(f"{path.relative_to(ROOT) if path.is_relative_to(ROOT) else path}: {len(records)} graphs, "
              f"{brute} brute-forced, {len(bad)} with violations")
        for module, declaration, found in bad[:20]:
            print(f"  {module} {declaration}: {'; '.join(found)}")
    return 1 if total_bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
