#!/usr/bin/env python3
"""search-v0.8's three searches with goal identity from the typed key (`goal_identity_typed`) throughout.

`search_faithful` identifies goals and states by the expression key of `goal_identity`, whose known defects the
typed key corrects (it numbers term and level metavariables jointly over a state, keeps literals literal, keeps
out-of-context free variables apart, marks implementation-detail hypotheses, and fails closed). This module is
`search_faithful`'s searches with every identity decision made by the typed key:

- the whole-state search drops a child state whose typed ordered key (one joint renaming over the state's goals)
  equals that of a state generated before; its order and goal duplicates are measured with typed keys too;
- the goal search merges a goal into an earlier one with the same typed goal key, behind a renaming step when
  hypothesis names differ, as before; a candidate is entangled when the carried goals' typed keys change;
- the group search partitions goals by `goal_identity_typed.groups` (term and level metavariables, contexts and
  targets) and merges a group of several goals when its typed group key, and its printed goals, agree with an
  earlier group's: the printed goals must agree because a group's proof is reused verbatim.

A state whose export fails is never merged, and its child goals are kept apart (fail closed); where an export
fails, the entanglement check falls back to printed goals. The proposer still keys its draws by printed goal text,
since the printed goal is what the prover is shown. At each identity decision the searches also record whether the
typed key and the expression key had each met the state or goal before (both exporters are defined in the task's
environment), so that a run is also an audit of the expression key on the typed searches' own trajectories.
"""

from __future__ import annotations

import json
import time
from typing import Any, Callable

import goal_identity as gi
import goal_identity_typed as gt
import search_faithful as sf
import search_goal_selection as sgs
from lean_repl import LeanRepl, ReplTimeout
from renaming import hypotheses
from search_faithful import (Child, GoalGraph, HARNESS_TAG, Node, harness_step, names_agree, pick_sequence,
                             step_from_names)
from search_harness import ModuleSession, State, canonical_goal

TYPED_TACTIC = sgs.EXPORT_TACTIC


class TypedSession(ModuleSession):
    """A module environment that defines, right after its imports, the typed exporter and the expression exporter,
    and `pick_goal` where the imports lack it."""

    def __init__(self, repl: LeanRepl, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        self.env = sgs.define_exporter(repl, self.env)
        response = repl._exchange({"cmd": sf.DEFINITION, "env": self.env}, repl.import_timeout)
        ok = "env" in response and not any(m.get("severity") == "error" for m in response.get("messages", []))
        if ok:
            self.env = response["env"]
        setattr(repl, "fast_export", ok)
        self.env = sgs.define_pick_goal(repl, self.env)


class TypedCountingRepl(sgs.ClosingRepl):
    """search_faithful.CountingRepl's accounting, with both exporters counted as exports."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.costs = {kind: {"calls": 0, "seconds": 0.0} for kind in ("tactic", "export", "harness", "command")}
        super().__init__(*args, **kwargs)

    def _exchange(self, request: dict[str, Any], timeout: float) -> dict[str, Any]:
        text = request.get("tactic")
        if text is None:
            kind = "command"
        elif HARNESS_TAG in text:
            kind = "harness"
        elif "run_tac" in text or sf.EXPORT_TACTIC in text or TYPED_TACTIC in text:
            kind = "export"
        else:
            kind = "tactic"
        started = time.monotonic()
        try:
            return super()._exchange(request, timeout)
        finally:
            self.costs[kind]["calls"] += 1
            self.costs[kind]["seconds"] += time.monotonic() - started

    def cost_summary(self) -> dict[str, Any]:
        return {k: {"calls": v["calls"], "seconds": round(v["seconds"], 1)} for k, v in self.costs.items()}


class Exports:
    """The typed export and the expression export of each state a search reaches, one REPL call each."""

    def __init__(self, repl: LeanRepl) -> None:
        self.repl = repl
        self.typed_cache: dict[int, list[dict[str, Any]] | None] = {}
        self.expr_cache: dict[int, list[dict[str, Any]] | None] = {}
        self.failures = 0
        self.attempts = 0
        self.expr_failures = 0

    def get(self, proof_state: int, count: int) -> list[dict[str, Any]] | None:
        if proof_state not in self.typed_cache:
            self.attempts += 1
            exported = sgs.export(self.repl, proof_state)
            if exported is None or len(exported) != count:
                self.failures += 1
                exported = None
            self.typed_cache[proof_state] = exported
        return self.typed_cache[proof_state]

    def expression(self, proof_state: int, count: int) -> list[dict[str, Any]] | None:
        if proof_state not in self.expr_cache:
            exported = sf.export(self.repl, proof_state)
            if exported is None or len(exported) != count:
                self.expr_failures += 1
                exported = None
            self.expr_cache[proof_state] = exported
        return self.expr_cache[proof_state]


def tally() -> dict[str, int]:
    """Decisions of the typed key against the expression key's at the same points: agreements, the two directions
    of disagreement, and points where an export failed."""
    return {"agree": 0, "typedOnly": 0, "expressionOnly": 0, "unexported": 0}


def compare(audit: dict[str, int], typed: bool | None, expression: bool | None) -> None:
    if typed is None or expression is None:
        audit["unexported"] += 1
    elif typed == expression:
        audit["agree"] += 1
    elif typed:
        audit["typedOnly"] += 1
    else:
        audit["expressionOnly"] += 1


# ---------------------------------------------------------------- whole states


def whole_state_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                       proposer: Callable[[State], list[str]], budget: int,
                       verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    exports = Exports(repl)
    states: list[State] = [State(0, root_proof_state, root_goals, None, None, 0)]
    drawn_from: dict[int, dict[str, Any] | None] = {0: None}
    frontier: list[int] = [0]
    root = exports.get(root_proof_state, len(root_goals))
    root_expr = exports.expression(root_proof_state, len(root_goals))
    seen = {gt.ordered_state_key(root)} if root is not None else set()
    seen_expr = {gi.state_key(root_expr)} if root_expr is not None else set()
    multisets: dict[str, set[str]] = {}
    firsts: set[str] = set()
    expansions: list[dict[str, Any]] = []
    proof: list[str] | None = None
    proof_draws: list[dict[str, Any] | None] = []
    rejected = 0
    drops = tally()
    started = time.monotonic()
    while frontier and len(expansions) < budget and proof is None:
        state = states[frontier.pop(0)]
        exported = exports.get(state.proof_state, len(state.goals))
        order_duplicate = goal_duplicate = None
        if exported is not None:
            ordered = gt.ordered_state_key(exported)
            multiset = gt.unordered_state_key(exported)
            if multiset is not None:
                order_duplicate = multiset in multisets and ordered not in multisets[multiset]
                multisets.setdefault(multiset, set()).add(ordered)
            first = gt.goal_key(exported[0])
            goal_duplicate = first in firsts
            firsts.add(first)
        candidates = proposer(state)
        info = sf.draw_info(proposer)
        valid = duplicates = 0
        for tactic in candidates:
            result = repl.tactic(state.proof_state, tactic)
            if result is None:
                continue
            goals, proof_state = result
            child = State(len(states), proof_state, goals, state.id, tactic, state.depth + 1)
            if not goals:
                script, draws, cursor = [tactic], [info], state
                while cursor.tactic is not None and cursor.parent is not None:
                    script.append(cursor.tactic)
                    draws.append(drawn_from.get(cursor.id))
                    cursor = states[cursor.parent]
                script.reverse()
                if verifier is not None and not verifier(script):
                    rejected += 1
                    continue
                valid += 1
                proof, proof_draws = script, list(reversed(draws))
                break
            valid += 1
            typed = exports.get(proof_state, len(goals))
            key = gt.ordered_state_key(typed) if typed is not None else None
            expr = exports.expression(proof_state, len(goals))
            expr_key = gi.state_key(expr) if expr is not None else None
            dropped = key is not None and key in seen
            compare(drops, None if key is None else dropped, None if expr_key is None else expr_key in seen_expr)
            if expr_key is not None:
                seen_expr.add(expr_key)
            if dropped:
                duplicates += 1
                continue
            if key is not None:
                seen.add(key)
            states.append(child)
            drawn_from[child.id] = info
            frontier.append(child.id)
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "duplicates": duplicates,
                           "orderDuplicate": order_duplicate, "goalDuplicate": goal_duplicate, "draw": info})
    return {"expansions": expansions, "states": len(states), "proof": proof, "proofDraws": proof_draws,
            "rejected": rejected, "exportFailures": exports.failures, "exportAttempts": exports.attempts,
            "expressionExportFailures": exports.expr_failures,
            "dropsAgainstExpressionKey": drops, "seconds": round(time.monotonic() - started, 1),
            "restarts": repl.restarts}


# ---------------------------------------------------------------- goals and groups


class TypedGoalGraph(GoalGraph):
    """search_faithful.GoalGraph with typed keys; a goal or group whose export failed gets a key of its own. Built
    by `_graph`, since GoalGraph's constructor sets up the expression exports and the root node itself."""

    def single_key(self, goal: str, exported: dict[str, Any] | None) -> tuple[Any, ...]:  # type: ignore[override]
        if exported is None:
            self.unexported += 1
            return ("goal", None, canonical_goal(goal), self.unexported)
        return ("goal", gt.goal_key(exported), canonical_goal(goal))

    def identify_goal(self, goal: str, index: int, proof_state: int, state_goals: list[str],
                      exported: dict[str, Any] | None) -> Child:
        """GoalGraph.identify_goal with typed keys, recording whether this goal's typed key and its expression key
        had arrived before."""
        typed_key = gt.goal_key(exported) if exported is not None else None
        expr = self.exports.expression(proof_state, len(state_goals))
        expr_key = gi.goal_key(expr[index]) if expr is not None else None
        compare(self.merge_audit, None if typed_key is None else typed_key in self.typed_keys,
                None if expr_key is None else expr_key in self.expr_keys)
        if typed_key is not None:
            self.typed_keys.add(typed_key)
        if expr_key is not None:
            self.expr_keys.add(expr_key)
        return super().identify_goal(goal, index, proof_state, state_goals, exported)

    def identify_group(self, goals: list[str], positions: list[int], proof_state: int,
                       exported: list[dict[str, Any]] | None) -> Child:
        self.merges["arrivals"] += 1
        members = [exported[i] for i in positions] if exported else None
        if members is None:
            self.unexported += 1
            key: tuple[Any, ...] = ("group", None, tuple(canonical_goal(goals[i]) for i in positions), self.unexported)
        else:
            key = ("group", gt.group_key(members), tuple(canonical_goal(goals[i]) for i in positions))
        if key in self.by_key:
            self.merges["identical"] += 1
            return self.by_key[key], []
        return self.new_node(key, [goals[i] for i in positions], (proof_state, list(positions), list(goals))), []


def _graph(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
           verifier: Callable[[list[str]], bool] | None) -> TypedGoalGraph:
    """A TypedGoalGraph whose exports are the typed and expression exports (GoalGraph builds the root node in its
    constructor, so the exports are set up before it runs)."""
    graph = TypedGoalGraph.__new__(TypedGoalGraph)
    graph.unexported = 0
    graph.merge_audit = tally()
    graph.typed_keys = set()
    graph.expr_keys = set()
    graph.repl = repl
    graph.exports = Exports(repl)
    graph.verifier = verifier
    graph.nodes = {}
    graph.by_key = {}
    graph.classes = {}
    graph.aliases = {}
    graph.parents = {}
    graph.frontier = []
    graph.merges = {"arrivals": 0, "new": 0, "identical": 0, "renamed": 0, "reused": 0, "checks": 0, "refused": 0}
    graph.rejected = 0
    graph.proof = None
    exported = graph.exports.get(root_proof_state, len(root_goals))
    expr = graph.exports.expression(root_proof_state, len(root_goals))
    if exported is not None:
        graph.typed_keys.add(gt.goal_key(exported[0]))
    if expr is not None:
        graph.expr_keys.add(gi.goal_key(expr[0]))
    graph.root = graph.new_node(graph.single_key(root_goals[0], exported[0] if exported else None),
                                [root_goals[0]], (root_proof_state, [0], list(root_goals)))
    graph.merges["new"] -= 1
    return graph


def carried_unchanged(graph: TypedGoalGraph, parent: tuple[int, list[str]], size: int, child_state: int,
                      goals: list[str], audit: dict[str, int]) -> bool:
    """Whether a candidate left the goals carried behind the node's `size` goals unchanged: by their typed keys,
    jointly renamed, when both states exported, else by printed text."""
    parent_state, parent_goals = parent
    carried = parent_goals[size:]
    if len(goals) < len(carried):
        return False
    tail = goals[len(goals) - len(carried):] if carried else []
    printed = [canonical_goal(g) for g in tail] == [canonical_goal(g) for g in carried]
    if not carried:
        return True
    before = graph.exports.get(parent_state, len(parent_goals))
    after = graph.exports.get(child_state, len(goals))
    if before is None or after is None:
        audit["printed"] += 1
        return printed
    typed = gt.ordered_state_key(before[size:]) == gt.ordered_state_key(after[len(goals) - len(carried):])
    audit["typed"] += 1
    audit["disagree"] += typed != printed
    return typed


def and_or_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                  proposer: Callable[[State], list[str]], budget: int,
                  verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    graph = _graph(repl, root_proof_state, root_goals, verifier)
    graph.nodes[graph.root].home = (root_proof_state, [0], list(root_goals))
    expansions: list[dict[str, Any]] = []
    entangled = 0
    checks = {"typed": 0, "printed": 0, "disagree": 0}
    started = time.monotonic()
    while graph.frontier and len(expansions) < budget and graph.proof is None:
        node_id = graph.frontier.pop(0)
        node = graph.nodes[node_id]
        if node.proved_by is not None:
            continue
        front = graph.bring_to_front(node)
        if front is None:
            continue
        proof_state, home_goals = front
        candidates = proposer(State(len(expansions), proof_state, [home_goals[0]], None, None, 0))
        info = sf.draw_info(proposer)
        node.expansions += 1
        valid = 0
        for tactic in candidates:
            result = repl.tactic(proof_state, tactic)
            if result is None:
                continue
            goals, new_state = result
            if not carried_unchanged(graph, (proof_state, home_goals), 1, new_state, goals, checks):
                entangled += 1
                continue
            valid += 1
            count = len(goals) - (len(home_goals) - 1)
            exported = graph.exports.get(new_state, len(goals)) if count else None
            children = [graph.identify_goal(goals[i], i, new_state, goals, exported[i] if exported else None)
                        for i in range(count)]
            if graph.add_alternative(node_id, tactic, [], children):
                break
        expansions.append({"node": node_id, "candidates": len(candidates), "valid": valid, "draw": info})
    return {"expansions": expansions, "nodes": len(graph.nodes), "proof": graph.proof, "entangled": entangled,
            "rejected": graph.rejected, "merges": graph.merges, "exportFailures": graph.exports.failures,
            "exportAttempts": graph.exports.attempts,
            "expressionExportFailures": graph.exports.expr_failures, "unexported": graph.unexported,
            "mergesAgainstExpressionKey": graph.merge_audit, "carriedChecks": checks,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}


def coupled_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                   proposer: Callable[[State], list[str]], budget: int,
                   verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    graph = _graph(repl, root_proof_state, root_goals, verifier)
    graph.nodes[graph.root].home = (root_proof_state, [0], list(root_goals))
    expansions: list[dict[str, Any]] = []
    outside = 0
    groups_made = {"single": 0, "several": 0}
    checks = {"typed": 0, "printed": 0, "disagree": 0}
    started = time.monotonic()
    while graph.frontier and len(expansions) < budget and graph.proof is None:
        node_id = graph.frontier.pop(0)
        node = graph.nodes[node_id]
        if node.proved_by is not None:
            continue
        front = graph.bring_to_front(node)
        if front is None:
            continue
        proof_state, home_goals = front
        size = len(node.goals)
        candidates = proposer(State(len(expansions), proof_state, [home_goals[0]], None, None, 0))
        info = sf.draw_info(proposer)
        node.expansions += 1
        valid = 0
        for tactic in candidates:
            result = repl.tactic(proof_state, tactic)
            if result is None:
                continue
            goals, new_state = result
            if not carried_unchanged(graph, (proof_state, home_goals), size, new_state, goals, checks):
                outside += 1
                continue
            count = len(goals) - (len(home_goals) - size)
            partition: list[list[int]] = []
            exported = graph.exports.get(new_state, len(goals)) if count else None
            if count:
                if exported is None:
                    partition = [list(range(count))]
                else:
                    partition = gt.groups(exported)
                    if any(min(g) < count <= max(g) for g in partition):
                        outside += 1  # a group reaching past the node's goals: coupled outside the node
                        continue
                    partition = [g for g in partition if max(g) < count]
            valid += 1
            wanted = [i for group in partition for i in group]
            picks = pick_sequence(len(goals), wanted) if wanted != list(range(count)) else []
            children = []
            for group in partition:
                groups_made["single" if len(group) == 1 else "several"] += 1
                if len(group) == 1:
                    children.append(graph.identify_goal(goals[group[0]], group[0], new_state, goals,
                                                        exported[group[0]] if exported else None))
                else:
                    children.append(graph.identify_group(goals, group, new_state, exported))
            if graph.add_alternative(node_id, tactic, picks, children):
                break
        expansions.append({"node": node_id, "goals": size, "candidates": len(candidates), "valid": valid,
                           "draw": info})
    proof_groups = 0
    if graph.proof is not None:
        stack = [graph.root]
        while stack:
            current = graph.nodes[stack.pop()]
            proof_groups += len(current.goals) > 1
            stack += [c for c, _ in current.proved_by[2]] if current.proved_by else []
    return {"expansions": expansions, "nodes": len(graph.nodes), "proof": graph.proof, "outside": outside,
            "rejected": graph.rejected, "merges": graph.merges, "groups": groups_made,
            "groupsInProof": proof_groups, "exportFailures": graph.exports.failures,
            "exportAttempts": graph.exports.attempts,
            "expressionExportFailures": graph.exports.expr_failures, "unexported": graph.unexported,
            "mergesAgainstExpressionKey": graph.merge_audit, "carriedChecks": checks,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}
