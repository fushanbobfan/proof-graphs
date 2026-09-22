#!/usr/bin/env python3
"""Order redundancy of tactic proofs: linear orderings of the step-dependency graph.

Reads the JSON lines of `proof_graph_extract` (one declaration per line with its
tactic steps) and prints one JSON line per declaration with:

- `steps`: number of atomic tactic steps;
- `forest`: whether every step consumes goals produced by at most one step;
- `linearizations`: the exact number of orderings of the steps that respect
  the dependencies (a proof with a single order counts 1), as a decimal string;
  for a forest by the hook-length formula `n! / prod(subtree sizes)`, for other
  graphs of at most 22 steps by subset dynamic programming, else `null`;
- `log10`: its base-10 logarithm;
- `structure`: `log(linearizations) / log(n!)`, 0 for a chain, 1 when every
  step is independent of every other; null for a single-step proof.
"""

from __future__ import annotations

import json
import math
import sys
from functools import lru_cache
from typing import Any

DP_MAX_STEPS = 22


def dependency_graph(steps: list[dict[str, Any]]) -> list[set[int]]:
    """parents[i] = indices of steps that produced a goal step i consumed."""
    producer: dict[str, int] = {}
    parents: list[set[int]] = []
    for index, step in enumerate(steps):
        parents.append({producer[goal] for goal in step["consumed"] if goal in producer})
        for goal in step["produced"]:
            producer[goal] = index
    return parents


def forest_linearizations(parents: list[set[int]]) -> int:
    n = len(parents)
    children: list[list[int]] = [[] for _ in range(n)]
    for index, ps in enumerate(parents):
        for p in ps:
            children[p].append(index)
    sizes = [0] * n
    for index in range(n - 1, -1, -1):  # children have larger indices (elaboration order)
        sizes[index] = 1 + sum(sizes[c] for c in children[index])
    product = 1
    for size in sizes:
        product *= size
    return math.factorial(n) // product


def dag_linearizations(parents: list[set[int]]) -> int:
    n = len(parents)
    masks = [sum(1 << p for p in ps) for ps in parents]

    @lru_cache(maxsize=None)
    def count(placed: int) -> int:
        if placed == (1 << n) - 1:
            return 1
        total = 0
        for index in range(n):
            bit = 1 << index
            if not placed & bit and masks[index] & placed == masks[index]:
                total += count(placed | bit)
        return total

    return count(0)


def analyse(record: dict[str, Any]) -> dict[str, Any]:
    steps = record["steps"]
    parents = dependency_graph(steps)
    n = len(steps)
    forest = all(len(ps) <= 1 for ps in parents)
    if forest:
        count: int | None = forest_linearizations(parents)
    elif n <= DP_MAX_STEPS:
        count = dag_linearizations(parents)
    else:
        count = None
    log10 = None if count is None else (math.log10(count) if count > 0 else None)
    structure = None
    if count is not None and n >= 2:
        structure = math.log(count) / math.log(math.factorial(n))
    return {"declaration": record["declaration"], "module": record["module"], "steps": n,
            "forest": forest, "roots": sum(1 for ps in parents if not ps),
            "linearizations": None if count is None else str(count), "log10": log10,
            "structure": structure}


def main() -> int:
    for line in sys.stdin:
        line = line.strip()
        if line.startswith("{"):
            print(json.dumps(analyse(json.loads(line)), separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
