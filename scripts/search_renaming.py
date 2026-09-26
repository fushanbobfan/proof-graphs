#!/usr/bin/env python3
"""The two searches of search_keys.py, with goals and states identified up to the names of their hypotheses.

`whole_state_search` is `search_keys.whole_state_search` with one change: a child state is dropped when its goals
agree, goal by goal and in order, with those of a state already generated up to renaming (`coarse_goal`), not only
when they print identically. This is the deduplication by renaming that LEAN-GitHub's best-first prover applies to
states. No proof passes through a dropped state, so the proofs need no renaming.

`and_or_search` is `search_keys.and_or_search` with one change: a new goal is merged into an earlier one that it
matches up to renaming when `renaming.renaming_step` turns it into that goal. The step is run in the REPL on the new
goal where it was created, and the merge stands only if the renamed goal prints as the earlier one up to the names
of the earlier goal's inaccessible hypotheses (`renaming.agrees`); otherwise the new goal is a node of its own. The
earlier goal keeps its names, so the proposer sees the goal as it arose, and its proof is used for the new goal
behind the renaming step, which becomes part of the proof script. A goal printed like one already merged reuses its
step without a new check. Everything else, including the draws (keyed by the printed goal the proposer sees), the
entanglement rule, a proof set once, and the verification of every completed proof from the statement, is as in
search_keys; only the parents of a goal are kept in insertion order, so that which proof a goal records when several
complete at once does not depend on Python's string hashing, as it does in search_keys.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Any, Callable

from lean_repl import LeanRepl
from renaming import agrees, renaming_step
from search_harness import State, canonical_goal
from search_keys import coarse_goal, goal_keys


def whole_state_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                       proposer: Callable[[State], list[str]], budget: int,
                       verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    """`search_keys.whole_state_search`, deduplicating states up to renaming."""
    states: list[State] = [State(0, root_proof_state, root_goals, None, None, 0)]
    frontier: list[int] = [0]
    seen_printed: set[tuple[str, ...]] = {states[0].ordered_key}
    seen: set[tuple[str, ...]] = {tuple(coarse_goal(g) for g in root_goals)}
    expanded_multisets: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    expanded_first_goals: set[str] = set()
    expansions: list[dict[str, Any]] = []
    proof: list[str] | None = None
    timeouts = 0
    rejected = 0
    started = time.monotonic()
    while frontier and len(expansions) < budget and proof is None:
        state = states[frontier.pop(0)]
        order_duplicate = state.multiset_key in expanded_multisets and \
            state.ordered_key not in expanded_multisets[state.multiset_key]
        goal_duplicate = state.first_goal_key in expanded_first_goals
        expanded_multisets.setdefault(state.multiset_key, set()).add(state.ordered_key)
        expanded_first_goals.add(state.first_goal_key)
        keys = goal_keys(repl, state.proof_state, state.goals)
        candidates = proposer(state)
        valid = 0
        exact_duplicates = 0
        renamed_duplicates = 0
        for tactic in candidates:
            result = repl.tactic(state.proof_state, tactic)
            if result is None:
                continue
            goals, proof_state = result
            child = State(len(states), proof_state, goals, state.id, tactic, state.depth + 1)
            if not goals:
                script = []
                cursor: State | None = child
                while cursor is not None and cursor.tactic is not None:
                    script.append(cursor.tactic)
                    cursor = states[cursor.parent] if cursor.parent is not None else None
                script.reverse()
                if verifier is not None and not verifier(script):
                    rejected += 1
                    continue
                valid += 1
                states.append(child)
                state.children.append(child.id)
                proof = script
                break
            valid += 1
            renamed_key = tuple(coarse_goal(g) for g in goals)
            if renamed_key in seen:
                if child.ordered_key in seen_printed:
                    exact_duplicates += 1
                else:
                    renamed_duplicates += 1
                seen_printed.add(child.ordered_key)
                continue
            seen.add(renamed_key)
            seen_printed.add(child.ordered_key)
            states.append(child)
            state.children.append(child.id)
            frontier.append(child.id)
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "exactDuplicates": exact_duplicates,
                           "renamedDuplicates": renamed_duplicates, "orderDuplicate": order_duplicate,
                           "goalDuplicate": goal_duplicate, "keys": keys})
    return {"expansions": expansions, "states": len(states), "proof": proof, "timeouts": timeouts,
            "rejected": rejected, "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts,
            "orderDuplicates": sum(1 for e in expansions if e["orderDuplicate"]),
            "goalDuplicates": sum(1 for e in expansions if e["goalDuplicate"]),
            "uniqueFirstGoals": len(expanded_first_goals),
            "renamedDuplicates": sum(e["renamedDuplicates"] for e in expansions),
            "exactDuplicates": sum(e["exactDuplicates"] for e in expansions)}


Child = tuple[str, list[str]]  # a node's key and the renaming lines that turn the goal into the node's goal


@dataclass
class Node:
    key: str
    goal: str  # the goal as it arose, which the proposer sees and every merged goal is renamed into
    home: tuple[int, int, list[str]]  # a REPL proof state, the 1-based position of this goal in it, its goals
    proved_by: tuple[str, list[Child]] | None = None
    alternatives: list[tuple[str, list[Child]]] = field(default_factory=list)
    expansions: int = 0


def script_of(nodes: dict[str, Node], key: str) -> list[str]:
    """The proof script of a proved node: its tactic, then each child's renaming lines and script."""
    tactic, children = nodes[key].proved_by  # type: ignore[misc]
    lines = [tactic]
    parts = [renaming + script_of(nodes, child) for child, renaming in children]
    if len(parts) == 1:
        lines += parts[0]
    else:
        for part in parts:
            lines.append("· " + part[0])
            lines += ["  " + line for line in part[1:]]
    return lines


def and_or_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                  proposer: Callable[[State], list[str]], budget: int,
                  verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    """`search_keys.and_or_search`, merging goals alike up to renaming behind a verified renaming step."""
    root_key = canonical_goal(root_goals[0])
    nodes: dict[str, Node] = {root_key: Node(root_key, root_goals[0], (root_proof_state, 1, list(root_goals)))}
    classes: dict[str, list[str]] = {coarse_goal(root_goals[0]): [root_key]}
    aliases: dict[str, tuple[Child, bool]] = {}
    parents: dict[str, dict[str, None]] = {}  # insertion-ordered, so that settling does not depend on hashing
    frontier: list[str] = [root_key]
    expansions: list[dict[str, Any]] = []
    merges = {"arrivals": 0, "new": 0, "printed": 0, "renamed": 0, "renamedExact": 0, "reused": 0,
              "checks": 0, "refused": 0}
    picks = 0
    timeouts = 0
    entangled = 0
    rejected = 0
    started = time.monotonic()
    proof: list[str] | None = None

    def settle(key: str) -> None:
        node = nodes[key]
        if node.proved_by is not None:
            return
        for tactic, children in node.alternatives:
            if all(nodes[c].proved_by is not None for c, _ in children):
                node.proved_by = (tactic, children)
                for parent in parents.get(key, {}):
                    settle(parent)
                return

    def root_completed() -> bool:
        nonlocal rejected, proof
        root = nodes[root_key]
        while root.proved_by is not None:
            script = script_of(nodes, root_key)
            if verifier is None or verifier(script):
                proof = script
                return True
            rejected += 1
            root.alternatives = [a for a in root.alternatives if a != root.proved_by]
            root.proved_by = None
            settle(root_key)
        return False

    def identify(goal: str, index: int, proof_state: int, goals: list[str]) -> Child:
        """The node a goal created at `index` of `proof_state` belongs to, creating it if none matches."""
        merges["arrivals"] += 1
        key = canonical_goal(goal)
        if key in nodes:
            merges["printed"] += 1
            return key, []
        if key in aliases:
            child, exact = aliases[key]
            merges["renamed"] += 1
            merges["renamedExact"] += exact
            merges["reused"] += 1
            return child
        coarse = coarse_goal(goal)
        for candidate in classes.get(coarse, []):
            target = nodes[candidate].goal
            lines = renaming_step(goal, target)
            if lines is None:
                continue
            merges["checks"] += 1
            renamed = goal
            if lines:
                focus = ([f"pick_goal {index + 1}"] if index else []) + lines
                result = repl.tactic(proof_state, "; ".join(focus))
                if result is None or not result[0]:
                    merges["refused"] += 1
                    continue
                renamed = result[0][0]
            if not agrees(renamed, target):
                merges["refused"] += 1
                continue
            exact = canonical_goal(renamed) == canonical_goal(target)
            aliases[key] = ((candidate, lines), exact)
            merges["renamed"] += 1
            merges["renamedExact"] += exact
            return candidate, lines
        nodes[key] = Node(key, goal, (proof_state, index + 1, list(goals)))
        classes.setdefault(coarse, []).append(key)
        frontier.append(key)
        merges["new"] += 1
        return key, []

    while frontier and len(expansions) < budget and proof is None:
        key = frontier.pop(0)
        node = nodes[key]
        if node.proved_by is not None:
            continue
        proof_state, position, home_goals = node.home
        if position != 1:
            picked = repl.tactic(proof_state, f"pick_goal {position}")
            picks += 1
            if picked is None:
                continue
            proof_state = picked[1]
            home_goals = picked[0]
            node.home = (proof_state, 1, home_goals)
        keys = goal_keys(repl, proof_state, home_goals)
        carried = [canonical_goal(g) for g in home_goals[1:]]
        candidates = proposer(State(len(expansions), proof_state, [home_goals[0]], None, None, 0))
        node.expansions += 1
        valid = 0
        for tactic in candidates:
            result = repl.tactic(proof_state, tactic)
            if result is None:
                continue
            goals, new_state = result
            tail = [canonical_goal(g) for g in goals[len(goals) - len(carried):]] if carried else []
            if len(goals) < len(carried) or tail != carried:
                entangled += 1
                continue
            valid += 1
            children_goals = goals[:len(goals) - len(carried)]
            children = [identify(g, index, new_state, goals) for index, g in enumerate(children_goals)]
            for child, _ in children:
                parents.setdefault(child, {})[key] = None
            node.alternatives.append((tactic, children))
            if node.proved_by is None and all(nodes[c].proved_by is not None for c, _ in children):
                node.proved_by = (tactic, children)
                for parent in parents.get(key, {}):
                    settle(parent)
                if root_completed():
                    break
        expansions.append({"goal": key[:80], "candidates": len(candidates), "valid": valid,
                           "keys": {name: (None if value is None else value[:1]) for name, value in keys.items()}})
    return {"expansions": expansions, "goals": len(nodes), "proof": proof, "picks": picks, "timeouts": timeouts,
            "entangled": entangled, "rejected": rejected, "merges": merges,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}
