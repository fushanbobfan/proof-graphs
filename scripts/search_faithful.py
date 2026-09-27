#!/usr/bin/env python3
"""Three searches that identify goals by their Lean expressions (`goal_identity`), and one of them keeps goals
that share a metavariable together.

- `whole_state_search`: breadth-first over whole tactic states, as `search_keys.whole_state_search`, with child
  states dropped when their faithful state key (the goals' joint serialization, hypotheses by position, bound
  variables by index, metavariables by identity) equals that of a state already generated.
- `and_or_search`: breadth-first over single goals, as `search_renaming.and_or_search`: a goal is merged into an
  earlier goal with the same faithful goal key, behind a renaming step when their hypothesis names differ (the
  step is run in the REPL and must give the renamed goal the earlier goal's names wherever the earlier goal can
  mention them; bound names may differ); a candidate that changes a goal carried behind the chosen one is
  discarded as entangled. This is the independent-goal baseline, with faithful identity.
- `coupled_search`: breadth-first over groups of goals coupled by metavariables. A node is a group of goals no
  metavariable connects to any goal outside it; it is expanded by bringing its goals to the front (`pick_goal`) and
  applying each candidate to its first goal. The goals the candidate leaves in the group, new ones and old ones it
  may have changed by an assignment, are split into coupled groups again, each a child node. So a tactic that
  assigns a metavariable two goals share is kept, not discarded: the goals it changes stay in the node. A group of
  one goal is merged as in `and_or_search`; a larger group only with a group that prints identically. In the proof
  script the children of a step are brought to the front in order, a one-goal child under a bullet and a larger
  group without one, since no tactic focuses several goals.

The export is `goal_identity`'s code defined once in the task's environment as the tactic `pg_export_goals`
(`ExportingSession`), which costs a few milliseconds a call against half a second for the same code as a `run_tac`
block; the one added declaration is a tactic no candidate names. Where the definition fails the `run_tac` block
is used. Each search exports every state it reaches once (one REPL call), counts its REPL calls and their time by kind,
and records for every expansion the draw it used, so that a whole-state proof can be traced to fresh candidates
for a goal expanded again. Every completed proof is verified from the statement, as in all earlier searches.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Any, Callable

import json

import goal_identity as gi
from lean_repl import LeanRepl, ReplTimeout
from renaming import MARK, hypotheses
from search_harness import ModuleSession, State, canonical_goal

EXPORT_TACTIC = "pg_export_goals"
DEFINITION = ("open Lean Elab Tactic in\nelab \"" + EXPORT_TACTIC + "\" : tactic => do"
              + gi.KEY_TACTIC.replace("run_tac do", "", 1))


class ExportingSession(ModuleSession):
    """A ModuleSession whose environment, right after the module's imports, defines the export tactic."""

    def __init__(self, repl: LeanRepl, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        response = repl._exchange({"cmd": DEFINITION, "env": self.env}, repl.import_timeout)
        ok = "env" in response and not any(m.get("severity") == "error" for m in response.get("messages", []))
        if ok:
            self.env = response["env"]
        setattr(repl, "fast_export", ok)


def export(repl: LeanRepl, proof_state: int) -> list[dict[str, Any]] | None:
    """`goal_identity.export` through the defined tactic when the session has it."""
    if not getattr(repl, "fast_export", False):
        return gi.export(repl, proof_state)
    try:
        response = repl._exchange({"tactic": f"set_option maxHeartbeats {gi.HEARTBEATS} in\n{EXPORT_TACTIC}",
                                   "proofState": proof_state}, repl.timeout)
    except ReplTimeout:
        return None
    if any(m.get("severity") == "error" for m in response.get("messages", [])):
        return None
    infos = [m["data"] for m in response.get("messages", []) if m.get("severity") == "info"]
    if len(infos) != 1:
        return None
    try:
        goals = json.loads(infos[0])
    except json.JSONDecodeError:
        return None
    return goals if isinstance(goals, list) else None


class CountingRepl(LeanRepl):
    """A REPL session that counts its requests and their time: candidate tactics, exports, harness steps
    (`pick_goal`, renaming), and commands (setup and verification)."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.costs = {kind: {"calls": 0, "seconds": 0.0} for kind in ("tactic", "export", "harness", "command")}
        super().__init__(*args, **kwargs)

    def _exchange(self, request: dict[str, Any], timeout: float) -> dict[str, Any]:
        text = request.get("tactic")
        if text is None:
            kind = "command"
        elif HARNESS_TAG in text:
            kind = "harness"
        elif "run_tac" in text or EXPORT_TACTIC in text:
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


HARNESS_TAG = "-- harness"


def harness_step(repl: LeanRepl, proof_state: int, steps: list[str]) -> tuple[list[str], int] | None:
    """A step of the search itself (goal reordering, renaming), marked so that it is not counted as a candidate."""
    return repl.tactic(proof_state, "; ".join(steps) + f" {HARNESS_TAG}\n")


class Exports:
    """The faithful export of each state a search reaches, one REPL call per state."""

    def __init__(self, repl: LeanRepl) -> None:
        self.repl = repl
        self.cache: dict[int, list[dict[str, Any]] | None] = {}
        self.failures = 0

    def get(self, proof_state: int, count: int) -> list[dict[str, Any]] | None:
        if proof_state not in self.cache:
            exported = export(self.repl, proof_state)
            if exported is None or len(exported) != count:
                self.failures += 1
                exported = None
            self.cache[proof_state] = exported
        return self.cache[proof_state]


def accessible(names: list[str], i: int) -> bool:
    return MARK not in names[i]


def step_from_names(ours: list[str], theirs: list[str]) -> list[str] | None:
    """`renaming.renaming_step` for two goals aligned by the faithful key rather than the coarse one: tactic lines
    that give our hypotheses the names the target gives the hypotheses it can mention."""
    if len(ours) != len(theirs) or len(set(ours)) != len(ours) or len(set(theirs)) != len(theirs):
        return None
    moved: list[tuple[str, str]] = []
    wanted: dict[int, str] = {}
    for position, (mine, name) in enumerate(zip(ours, theirs)):
        if MARK in name or mine == name:
            continue
        if MARK in mine:
            wanted[position] = name
        else:
            moved.append((mine, name))
    lines = []
    if moved:
        lines.append("rename' " + ", ".join(f"{old} => {new}" for old, new in moved))
    if wanted:
        renamed = dict(moved)
        after = [renamed.get(name, name) for name in ours]
        unnamed = [i for i, name in enumerate(after) if MARK in name or name in after[i + 1:]]
        if not set(wanted) <= set(unnamed):
            return None
        first = min(wanted)
        lines.append("rename_i " + " ".join(wanted.get(i, "_") for i in unnamed if i >= first))
    return lines


def names_agree(renamed: list[str], target: list[str]) -> bool:
    """The renamed goal has the target's name wherever the target can mention one."""
    return len(renamed) == len(target) and all(renamed[i] == target[i] for i in range(len(target))
                                               if accessible(target, i))


def draw_info(proposer: Callable[[State], list[str]]) -> dict[str, Any] | None:
    return getattr(proposer, "last", None)


# ---------------------------------------------------------------- whole states


def whole_state_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                       proposer: Callable[[State], list[str]], budget: int,
                       verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    exports = Exports(repl)

    def identity(proof_state: int, goals: list[str]) -> tuple[str, ...]:
        exported = exports.get(proof_state, len(goals))
        if exported is None:
            return ("printed",) + tuple(canonical_goal(g) for g in goals)
        return ("faithful", gi.state_key(exported))

    states: list[State] = [State(0, root_proof_state, root_goals, None, None, 0)]
    drawn_from: dict[int, dict[str, Any] | None] = {0: None}
    frontier: list[int] = [0]
    seen = {identity(root_proof_state, root_goals)}
    multisets: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    firsts: set[str] = set()
    expansions: list[dict[str, Any]] = []
    proof: list[str] | None = None
    proof_draws: list[dict[str, Any] | None] = []
    rejected = 0
    started = time.monotonic()
    while frontier and len(expansions) < budget and proof is None:
        state = states[frontier.pop(0)]
        exported = exports.get(state.proof_state, len(state.goals))
        order_duplicate = goal_duplicate = None
        if exported is not None:
            ordered = tuple(gi.goal_key(g) for g in exported)
            multiset = tuple(sorted(ordered))
            order_duplicate = multiset in multisets and ordered not in multisets[multiset]
            goal_duplicate = ordered[0] in firsts
            multisets.setdefault(multiset, set()).add(ordered)
            firsts.add(ordered[0])
        candidates = proposer(state)
        info = draw_info(proposer)
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
            key = identity(proof_state, goals)
            if key in seen:
                duplicates += 1
                continue
            seen.add(key)
            states.append(child)
            drawn_from[child.id] = info
            frontier.append(child.id)
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "duplicates": duplicates,
                           "orderDuplicate": order_duplicate, "goalDuplicate": goal_duplicate, "draw": info})
    return {"expansions": expansions, "states": len(states), "proof": proof, "proofDraws": proof_draws,
            "rejected": rejected, "exportFailures": exports.failures,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}


# ---------------------------------------------------------------- goals and groups


Child = tuple[int, list[str]]  # a node and the renaming lines that turn the arriving goal into the node's goal


@dataclass
class Node:
    key: tuple[Any, ...]
    goals: list[str]  # as they arose; the first is the one the proposer sees
    home: tuple[int, list[int], list[str]]  # a proof state, the 0-based positions of the goals in it, its goals
    proved_by: tuple[str, list[int], list[Child]] | None = None  # tactic, reorder picks, children
    alternatives: list[tuple[str, list[int], list[Child]]] = field(default_factory=list)
    expansions: int = 0


def pick_sequence(length: int, wanted: list[int]) -> list[int]:
    """`pick_goal` arguments (1-based) that bring the goals at 0-based positions `wanted` of a goal list of
    `length` goals to its front, in that order, leaving the others in their order behind them."""
    order = list(range(length))
    picks = []
    for goal in reversed(wanted):
        position = order.index(goal)
        if position != 0:
            picks.append(position + 1)
            order.insert(0, order.pop(position))
    assert order[:len(wanted)] == list(wanted)
    return picks


def script_of(nodes: dict[int, Node], node_id: int) -> list[str]:
    """A proved node's script: its tactic, the picks that order its children, then each child, a one-goal child
    under a bullet and a larger group in line."""
    tactic, picks, children = nodes[node_id].proved_by  # type: ignore[misc]
    lines = [tactic]
    if picks:
        lines.append("; ".join(f"pick_goal {p}" for p in picks))
    if len(children) == 1:
        child, renaming = children[0]
        return lines + renaming + script_of(nodes, child)
    for child, renaming in children:
        body = renaming + script_of(nodes, child)
        if len(nodes[child].goals) == 1:
            lines.append("· " + body[0])
            lines += ["  " + line for line in body[1:]]
        else:
            lines += body
    return lines


class GoalGraph:
    """The shared machinery of the goal search and the group search: nodes, merging, proof, and verification."""

    def __init__(self, repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                 verifier: Callable[[list[str]], bool] | None) -> None:
        self.repl = repl
        self.exports = Exports(repl)
        self.verifier = verifier
        self.nodes: dict[int, Node] = {}
        self.by_key: dict[tuple[Any, ...], int] = {}
        self.classes: dict[str, list[int]] = {}
        self.aliases: dict[tuple[Any, ...], Child] = {}
        self.parents: dict[int, dict[int, None]] = {}
        self.frontier: list[int] = []
        self.merges = {"arrivals": 0, "new": 0, "identical": 0, "renamed": 0, "reused": 0, "checks": 0, "refused": 0}
        self.rejected = 0
        self.proof: list[str] | None = None
        exported = self.exports.get(root_proof_state, len(root_goals))
        self.root = self.new_node(self.single_key(root_goals[0], exported[0] if exported else None),
                                  [root_goals[0]], (root_proof_state, [0], list(root_goals)))
        self.merges["new"] -= 1  # the root did not arrive from a tactic

    @staticmethod
    def single_key(goal: str, exported: dict[str, Any] | None) -> tuple[Any, ...]:
        return ("goal", gi.goal_key(exported) if exported else None, canonical_goal(goal))

    def new_node(self, key: tuple[Any, ...], goals: list[str], home: tuple[int, list[int], list[str]]) -> int:
        node_id = len(self.nodes)
        self.nodes[node_id] = Node(key, goals, home)
        self.by_key[key] = node_id
        if key[0] == "goal" and key[1] is not None:
            self.classes.setdefault(key[1], []).append(node_id)
        self.frontier.append(node_id)
        self.merges["new"] += 1
        return node_id

    def identify_goal(self, goal: str, index: int, proof_state: int, state_goals: list[str],
                      exported: dict[str, Any] | None) -> Child:
        """The node a single goal created at `index` of `proof_state` belongs to, created if none matches."""
        self.merges["arrivals"] += 1
        key = self.single_key(goal, exported)
        if key in self.by_key:
            self.merges["identical"] += 1
            return self.by_key[key], []
        if key in self.aliases:
            self.merges["renamed"] += 1
            self.merges["reused"] += 1
            return self.aliases[key]
        faithful = key[1]
        for candidate in (self.classes.get(faithful, []) if faithful is not None else []):
            target = self.nodes[candidate].goals[0]
            lines = step_from_names(hypotheses(goal), hypotheses(target))
            if lines is None:
                continue
            self.merges["checks"] += 1
            renamed = goal
            if lines:
                result = harness_step(self.repl, proof_state, ([f"pick_goal {index + 1}"] if index else []) + lines)
                if result is None or not result[0]:
                    self.merges["refused"] += 1
                    continue
                renamed = result[0][0]
            if not names_agree(hypotheses(renamed), hypotheses(target)):
                self.merges["refused"] += 1
                continue
            self.aliases[key] = (candidate, lines)
            self.merges["renamed"] += 1
            return candidate, lines
        return self.new_node(key, [goal], (proof_state, [index], list(state_goals))), []

    def identify_group(self, goals: list[str], positions: list[int], proof_state: int,
                       exported: list[dict[str, Any]] | None) -> Child:
        self.merges["arrivals"] += 1
        members = [exported[i] for i in positions] if exported else None
        key = ("group", gi.group_key(members) if members else None, tuple(canonical_goal(goals[i]) for i in positions))
        if key in self.by_key:
            self.merges["identical"] += 1
            return self.by_key[key], []
        return self.new_node(key, [goals[i] for i in positions], (proof_state, list(positions), list(goals))), []

    def settle(self, node_id: int) -> None:
        node = self.nodes[node_id]
        if node.proved_by is not None:
            return
        for alternative in node.alternatives:
            if all(self.nodes[c].proved_by is not None for c, _ in alternative[2]):
                node.proved_by = alternative
                for parent in self.parents.get(node_id, {}):
                    self.settle(parent)
                return

    def add_alternative(self, node_id: int, tactic: str, picks: list[int], children: list[Child]) -> bool:
        """Record an alternative; True once the root is proved and its script verifies."""
        node = self.nodes[node_id]
        for child, _ in children:
            self.parents.setdefault(child, {})[node_id] = None
        node.alternatives.append((tactic, picks, children))
        if node.proved_by is None and all(self.nodes[c].proved_by is not None for c, _ in children):
            node.proved_by = (tactic, picks, children)
            for parent in self.parents.get(node_id, {}):
                self.settle(parent)
            return self.root_completed()
        return False

    def root_completed(self) -> bool:
        root = self.nodes[self.root]
        while root.proved_by is not None:
            script = script_of(self.nodes, self.root)
            if self.verifier is None or self.verifier(script):
                self.proof = script
                return True
            self.rejected += 1
            root.alternatives = [a for a in root.alternatives if a != root.proved_by]
            root.proved_by = None
            self.settle(self.root)
        return False

    def bring_to_front(self, node: Node) -> tuple[int, list[str]] | None:
        """The node's home state with its goals first, in order."""
        proof_state, positions, goals = node.home
        if not goals:
            goals = self.goals_of(proof_state)
            if goals is None:
                return None
        picks = pick_sequence(len(goals), positions)
        if picks:
            result = harness_step(self.repl, proof_state, [f"pick_goal {p}" for p in picks])
            if result is None:
                return None
            goals, proof_state = result
        node.home = (proof_state, list(range(len(positions))), goals)
        return proof_state, goals

    def goals_of(self, proof_state: int) -> list[str] | None:
        result = self.repl.tactic(proof_state, f"skip {HARNESS_TAG}\n")
        return None if result is None else result[0]


def and_or_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                  proposer: Callable[[State], list[str]], budget: int,
                  verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    graph = GoalGraph(repl, root_proof_state, root_goals, verifier)
    graph.nodes[graph.root].home = (root_proof_state, [0], list(root_goals))
    expansions: list[dict[str, Any]] = []
    entangled = 0
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
        carried = [canonical_goal(g) for g in home_goals[1:]]
        candidates = proposer(State(len(expansions), proof_state, [home_goals[0]], None, None, 0))
        info = draw_info(proposer)
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
            count = len(goals) - len(carried)
            exported = graph.exports.get(new_state, len(goals)) if count else None
            children = [graph.identify_goal(goals[i], i, new_state, goals, exported[i] if exported else None)
                        for i in range(count)]
            if graph.add_alternative(node_id, tactic, [], children):
                break
        expansions.append({"node": node_id, "candidates": len(candidates), "valid": valid, "draw": info})
    return {"expansions": expansions, "nodes": len(graph.nodes), "proof": graph.proof, "entangled": entangled,
            "rejected": graph.rejected, "merges": graph.merges, "exportFailures": graph.exports.failures,
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}


def coupled_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                   proposer: Callable[[State], list[str]], budget: int,
                   verifier: Callable[[list[str]], bool] | None = None) -> dict[str, Any]:
    graph = GoalGraph(repl, root_proof_state, root_goals, verifier)
    graph.nodes[graph.root].home = (root_proof_state, [0], list(root_goals))
    expansions: list[dict[str, Any]] = []
    outside = 0
    groups_made = {"single": 0, "several": 0}
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
        carried = [canonical_goal(g) for g in home_goals[size:]]
        candidates = proposer(State(len(expansions), proof_state, [home_goals[0]], None, None, 0))
        info = draw_info(proposer)
        node.expansions += 1
        valid = 0
        for tactic in candidates:
            result = repl.tactic(proof_state, tactic)
            if result is None:
                continue
            goals, new_state = result
            tail = [canonical_goal(g) for g in goals[len(goals) - len(carried):]] if carried else []
            if len(goals) < len(carried) or tail != carried:
                outside += 1
                continue
            count = len(goals) - len(carried)
            partition: list[list[int]] = []
            exported = graph.exports.get(new_state, len(goals)) if count else None
            if count:
                if exported is None:
                    partition = [list(range(count))]
                else:
                    partition = gi.groups(exported)
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
            "seconds": round(time.monotonic() - started, 1), "restarts": repl.restarts}
