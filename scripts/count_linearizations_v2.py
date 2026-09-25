#!/usr/bin/env python3
"""The step derivation of `count_linearizations.py`, with one correction.

`count_linearizations.py` lets a node consume a goal present before it, absent
after it, and never present before a later node, so that focusing constructs,
which hide a goal without closing it, consume nothing. A later node inside the
node's own subtree also counted, so a tactic whose own internal node mentions
the goal it closes consumed nothing: the internal node of `simpa ... using h`
that leaves the goal as it was is one such node. Those closings were lost, and
with them their steps. The blind reconstructions of extraction-audit-v0.1
found the defect. Here only later nodes outside the node's own subtree count;
everything else is `count_linearizations.py`, unchanged. The earlier
experiments keep the earlier rule, as registered.

  lake exe proof_graph_extract <module> <file> | python scripts/count_linearizations_v2.py
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from count_linearizations import (DP_MAX_STEPS, dag_linearizations, dependency_graph,  # noqa: E402,F401
                                  forest_linearizations, validate)


def subtree_end(nodes: list[dict[str, Any]]) -> list[int]:
    """The last node of each node's subtree; subtrees are contiguous in node order, which is checked."""
    children: list[list[int]] = [[] for _ in nodes]
    for node in nodes:
        if node["parent"] is not None:
            children[node["parent"]].append(node["index"])
    end = list(range(len(nodes)))
    for index in range(len(nodes) - 1, -1, -1):
        end[index] = max([index] + [end[c] for c in children[index]])
    for index in range(len(nodes)):
        for member in range(index + 1, end[index] + 1):
            parent = nodes[member]["parent"]
            while parent is not None and parent > index:
                parent = nodes[parent]["parent"]
            if parent != index:
                raise ValueError("a subtree is not contiguous in node order")
    return end


def derive_steps(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Steps with `consumed` and `produced` goal lists, in node order."""
    n = len(nodes)
    end = subtree_end(nodes)
    later_outside: list[set[str]] = [set() for _ in range(n + 1)]  # goals before any node from here on
    for index in range(n - 1, -1, -1):
        later_outside[index] = later_outside[index + 1] | set(nodes[index]["before"])
    consumed: list[list[str]] = []
    produced: list[list[str]] = []
    for index, node in enumerate(nodes):
        after = set(node["after"])
        before = set(node["before"])
        outside = later_outside[end[index] + 1]
        consumed.append([g for g in node["before"] if g not in after and g not in outside])
        produced.append([g for g in node["after"] if g not in before])

    def ancestors(index: int) -> list[int]:
        chain = []
        parent = nodes[index]["parent"]
        while parent is not None:
            chain.append(parent)
            parent = nodes[parent]["parent"]
        return chain

    # origin of every goal: the deepest producing node, else the deepest node
    # enclosing the goal's first mention that did not already hold it
    producers: dict[str, list[int]] = {}
    for index in range(n):
        for g in produced[index]:
            producers.setdefault(g, []).append(index)
    origin: dict[str, int] = {}
    for g, candidates in producers.items():
        ancestor_sets = {i: set(ancestors(i)) for i in candidates}
        deepest = [i for i in candidates if not any(i in ancestor_sets[j] for j in candidates if j != i)]
        origin[g] = deepest[0]
    for index, node in enumerate(nodes):
        for g in node["before"]:
            if g in origin or g in producers:
                continue
            for ancestor in ancestors(index):
                held = set(nodes[ancestor]["before"])
                if held and g not in held:
                    origin[g] = ancestor
                    break
            producers.setdefault(g, [])  # first mention seen; do not revisit
    originated: dict[int, list[str]] = {}
    for g, index in origin.items():
        originated.setdefault(index, []).append(g)

    consumed_below: dict[int, set[str]] = {}
    for index in range(n):
        for a in ancestors(index):
            consumed_below.setdefault(a, set()).update(consumed[index])
    own = [[g for g in consumed[index] if g not in consumed_below.get(index, set())] for index in range(n)]
    consumer = {g: index for index in range(n) for g in own[index]}
    for index in sorted(originated):
        if own[index]:
            continue
        targets = [consumer[g] for g in nodes[index]["before"]
                   if g in consumer and index in ancestors(consumer[g])]
        if targets:
            originated.setdefault(targets[0], []).extend(originated.pop(index))
    steps = []
    for index, node in enumerate(nodes):
        if not own[index] and index not in originated:
            continue
        kind = node["kind"]
        for a in [index] + ancestors(index):
            if nodes[a]["kind"] != "null" and "tacticSeq" not in nodes[a]["kind"]:
                kind = nodes[a]["kind"]
                break
        steps.append({"kind": kind, "consumed": own[index], "produced": originated.get(index, []),
                      "line": node["line"]})
    live_goals = {g for node in nodes if node["parent"] is None for g in node["before"]}
    live = [False] * len(steps)
    changed = True
    while changed:
        changed = False
        for index, step in enumerate(steps):
            if not live[index] and any(g in live_goals for g in step["consumed"]):
                live[index] = True
                live_goals.update(step["produced"])
                changed = True
    return [step for index, step in enumerate(steps) if live[index]]


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
