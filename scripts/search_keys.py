#!/usr/bin/env python3
"""The searches of search_harness.py, recording each expanded goal under three identities.

Goal identity decides what counts as a duplicate. The searches of search-v0.1 to v0.3 compare goals by their
pretty-printed text with the case tag removed and metavariable numbers erased (`canonical_goal`, the *default*
key). That text hides implicit arguments, so two different goals can print alike, and it keeps hypothesis names,
so two goals that differ only by renaming print differently. The searches here behave exactly as those of
`search_harness` (they deduplicate and merge by the default key), and record for every expanded goal:

- *fine*: the goal printed with `pp.all`, canonicalized the same way: every implicit argument, universe, and
  coercion explicit;
- *default*: `canonical_goal`;
- *coarse*: the default text with the hypotheses renamed by position (`h0`, `h1`, ... in context order), so
  that goals equal up to the names of their hypotheses coincide.

Each key is stored as the first 16 hexadecimal digits of the SHA-256 of its text. The fine text comes from
`set_option pp.all true in trace_state` run on the expanded state, which leaves the state unchanged.

`and_or_search` differs from the harness in one respect: a goal's recorded proof is set once and never
overwritten. The harness let a later candidate of the same expansion overwrite it; when that candidate returned
the goal itself unchanged in print, the goal became its own proof and building the script did not terminate
(search-v0.3, FirstOrder.Language.BoundedFormula.realize_ex).
"""

from __future__ import annotations

import hashlib
import re
import time
from typing import Any, Callable

from lean_repl import LeanRepl
from search_harness import MENU, GoalNode, State, _script, canonical_goal

# The menu without its one-shot provers: the simp family, aesop, norm_num (simp with arithmetic extensions), and
# exact? (library search). What remains closes goals only within a decision procedure (omega, decide, linarith,
# positivity, ring) or by a step of logic, so proofs take several steps.
HAMMERS = ["simp", "simp_all", "aesop", "norm_num", "exact?", "simp at *", "simp [*]"]
MENU_HAMMER_FREE = [t for t in MENU if t not in HAMMERS]
TRACE = "set_option pp.all true in trace_state"
IDENTIFIER_TAIL = r"[\w'✝!?]"


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def coarse_goal(goal: str) -> str:
    """`canonical_goal` with every hypothesis renamed by its position in the context."""
    text = canonical_goal(goal)
    lines = text.split("\n")
    turnstile = next((i for i, line in enumerate(lines) if line.startswith("⊢")), None)
    if turnstile is None:
        return text
    names: list[str] = []
    for line in lines[:turnstile]:
        if line.startswith(" "):
            continue  # a wrapped hypothesis continues on an indented line
        head, separator, _ = line.partition(" : ")
        if separator:
            names.extend(head.split())
    mapping = {name: f"h{i}" for i, name in enumerate(dict.fromkeys(names))}
    if not mapping:
        return text
    pattern = re.compile(r"(?<![\w'✝.!?])(" + "|".join(re.escape(n) for n in sorted(mapping, key=len, reverse=True))
                         + r")(?!" + IDENTIFIER_TAIL + ")")
    return pattern.sub(lambda m: mapping[m.group(1)], text)


def fine_goals(repl: LeanRepl, proof_state: int, count: int) -> list[str] | None:
    """The state's goals printed with pp.all, or None when the trace fails or does not split into `count` goals."""
    response = repl._exchange({"tactic": TRACE, "proofState": proof_state}, repl.timeout)
    traces = response.get("traces") or []  # the REPL reports trace output here, not among the messages
    if any(m.get("severity") == "error" for m in response.get("messages", [])) or len(traces) != 1:
        return None
    goals = [g for g in traces[0].strip("\n").split("\n\n") if g.strip()]
    return goals if len(goals) == count else None


def goal_keys(repl: LeanRepl, proof_state: int, goals: list[str]) -> dict[str, list[str] | None]:
    fine = fine_goals(repl, proof_state, len(goals))
    return {"fine": None if fine is None else [digest(canonical_goal(g)) for g in fine],
            "default": [digest(canonical_goal(g)) for g in goals],
            "coarse": [digest(coarse_goal(g)) for g in goals]}


def whole_state_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                       proposer: Callable[[State], list[str]], budget: int,
                       verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    """`search_harness.whole_state_search`, with the keys of the expanded state's goals in each expansion."""
    states: list[State] = [State(0, root_proof_state, root_goals, None, None, 0)]
    frontier: list[int] = [0]
    seen_exact: set[tuple[str, ...]] = {states[0].ordered_key}
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
            if child.ordered_key in seen_exact:
                exact_duplicates += 1
                continue
            seen_exact.add(child.ordered_key)
            states.append(child)
            state.children.append(child.id)
            frontier.append(child.id)
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "exactDuplicates": exact_duplicates,
                           "orderDuplicate": order_duplicate, "goalDuplicate": goal_duplicate, "keys": keys})
    return {"expansions": expansions, "states": len(states), "proof": proof, "timeouts": timeouts,
            "rejected": rejected, "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts,
            "orderDuplicates": sum(1 for e in expansions if e["orderDuplicate"]),
            "goalDuplicates": sum(1 for e in expansions if e["goalDuplicate"]),
            "uniqueFirstGoals": len(expanded_first_goals)}


def and_or_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                  proposer: Callable[[State], list[str]], budget: int,
                  verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    """`search_harness.and_or_search` with a goal's proof set once, and the keys of each expanded goal."""
    root_key = canonical_goal(root_goals[0])
    nodes: dict[str, GoalNode] = {root_key: GoalNode(root_key, (root_proof_state, 1, list(root_goals)))}
    parents: dict[str, set[str]] = {}
    frontier: list[str] = [root_key]
    expansions: list[dict[str, Any]] = []
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
            if all(nodes[c].proved_by is not None for c in children):
                node.proved_by = (tactic, children)
                for parent in parents.get(key, set()):
                    settle(parent)
                return

    def root_completed() -> bool:
        nonlocal rejected, proof
        root = nodes[root_key]
        while root.proved_by is not None:
            script = _script(nodes, root_key)
            if verifier is None or verifier(script):
                proof = script
                return True
            rejected += 1
            root.alternatives = [a for a in root.alternatives if a != root.proved_by]
            root.proved_by = None
            settle(root_key)
        return False

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
            child_keys = [canonical_goal(g) for g in children_goals]
            for index, child_key in enumerate(child_keys):
                if child_key not in nodes:
                    nodes[child_key] = GoalNode(child_key, (new_state, index + 1, list(goals)))
                    frontier.append(child_key)
                parents.setdefault(child_key, set()).add(key)
            node.alternatives.append((tactic, child_keys))
            if node.proved_by is None and all(nodes[c].proved_by is not None for c in child_keys):
                node.proved_by = (tactic, child_keys)
                for parent in parents.get(key, set()):
                    settle(parent)
                if root_completed():
                    break
        expansions.append({"goal": key[:80], "candidates": len(candidates), "valid": valid,
                           "keys": {name: (None if value is None else value[:1]) for name, value in keys.items()}})
    return {"expansions": expansions, "goals": len(nodes), "proof": proof, "picks": picks, "timeouts": timeouts,
            "entangled": entangled, "rejected": rejected, "seconds": round(time.monotonic() - started, 1),
            "restarts": repl.restarts}


def menu_proposer(state: State) -> list[str]:
    return list(MENU)


def hammer_free_proposer(state: State) -> list[str]:
    return list(MENU_HAMMER_FREE)
