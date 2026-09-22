#!/usr/bin/env python3
"""Order redundancy of tactic proofs: linear orderings of the step-dependency graph.

Reads the JSON lines of `proof_graph_extract` (one declaration per line with its
tactic info nodes: goals before and after, parent, leaf flag) and prints one
JSON line per declaration.

Steps are derived from the nodes:

- a goal is *consumed* by a node when it is present before, absent after, and
  never reappears in a later node of the proof (focusing constructs such as
  `·` and `case` hide goals without closing them);
- a leaf node that consumes or produces goals is a step;
- a goal consumed by a leaf that no leaf produced and that is not a goal of
  the statement itself (the case goals of `induction ... with`,
  `cases ... with`, `rcases`, and similar structured tactics) was created
  inside the deepest enclosing node that did not already hold it; that node
  is a step producing those goals and consuming what none of its descendant
  steps consumed; other non-leaf nodes are containers, not steps;
- a step depends on the step that produced a goal it consumes.

The output fields are:

- `steps`: number of steps;
- `forest`: whether every step depends on at most one step;
- `linearizations`: the exact number of orderings of the steps that respect
  the dependencies, as a decimal string; for a forest by the hook-length
  formula `n! / prod(subtree sizes)`, for other graphs of at most 22 steps by
  subset dynamic programming, else `null`;
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


def derive_steps(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Steps with `consumed` and `produced` goal lists, in node order."""
    n = len(nodes)
    later_before: list[set[str]] = [set() for _ in nodes]
    seen: set[str] = set()
    for index in range(n - 1, -1, -1):
        later_before[index] = set(seen)
        seen |= set(nodes[index]["before"])
    consumed: list[list[str]] = []
    produced: list[list[str]] = []
    for index, node in enumerate(nodes):
        after = set(node["after"])
        before = set(node["before"])
        consumed.append([g for g in node["before"] if g not in after and g not in later_before[index]])
        produced.append([g for g in node["after"] if g not in before])
    known = {g for index, node in enumerate(nodes) if node["leaf"] for g in produced[index]}
    known |= set(nodes[0]["before"]) if nodes else set()  # the statement's own goals

    def ancestors(index: int) -> list[int]:
        chain = []
        parent = nodes[index]["parent"]
        while parent is not None:
            chain.append(parent)
            parent = nodes[parent]["parent"]
        return chain

    # Orphan goals consumed by a leaf were created inside the deepest enclosing
    # node that did not already hold them: that node is their producing step.
    structured_produced: dict[int, list[str]] = {}
    for index, node in enumerate(nodes):
        if not node["leaf"]:
            continue
        for g in consumed[index]:
            if g in known:
                continue
            for ancestor in ancestors(index):
                if g not in set(nodes[ancestor]["before"]):
                    structured_produced.setdefault(ancestor, [])
                    if g not in structured_produced[ancestor]:
                        structured_produced[ancestor].append(g)
                    known.add(g)
                    break
    step_indices = [i for i, node in enumerate(nodes)
                    if (node["leaf"] and (consumed[i] or produced[i])) or i in structured_produced]
    step_set = set(step_indices)
    descendant_steps: dict[int, set[int]] = {}
    for i in step_indices:
        for a in ancestors(i):
            descendant_steps.setdefault(a, set()).add(i)
    steps = []
    for i in step_indices:
        node = nodes[i]
        if node["leaf"]:
            steps.append({"kind": node["kind"], "consumed": consumed[i], "produced": produced[i],
                          "line": node["line"]})
        else:
            below = {g for d in descendant_steps.get(i, set()) if d in step_set for g in consumed[d]}
            kind = node["kind"]
            for a in [i] + ancestors(i):
                if nodes[a]["kind"] not in ("null",) and "tacticSeq" not in nodes[a]["kind"]:
                    kind = nodes[a]["kind"]
                    break
            steps.append({"kind": kind, "consumed": [g for g in consumed[i] if g not in below],
                          "produced": structured_produced[i], "line": node["line"]})
    return steps


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


def validate(record: dict[str, Any]) -> None:
    """Node indices form the range 0..n-1 and every parent index lies in it."""
    nodes = record["nodes"]
    n = len(nodes)
    if [node["index"] for node in nodes] != list(range(n)) or             any(node["parent"] is not None and not 0 <= node["parent"] < n for node in nodes):
        raise ValueError(f"{record['module']} {record['declaration']}: node indices or parents out of range")


def analyse(record: dict[str, Any]) -> dict[str, Any]:
    validate(record)
    steps = derive_steps(record["nodes"])
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
