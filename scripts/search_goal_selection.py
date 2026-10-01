#!/usr/bin/env python3
"""Breadth-first whole-state search with a choice of the goal to act on."""

from __future__ import annotations

import os
import subprocess
import time
from collections import deque
from typing import Any, Callable

import goal_identity_typed as gi
from lean_repl import LeanRepl, ReplTimeout
from search_faithful import harness_step
from search_harness import ModuleSession, State

EXPORT_TACTIC = "pg_export_typed_goals"
DEFINITION = ("open Lean Elab Tactic in\nelab \"" + EXPORT_TACTIC + "\" : tactic => do"
              + gi.KEY_TACTIC.replace("run_tac do", "", 1))


class ClosingRepl(LeanRepl):
    """Close the launcher and its REPL child together, including after a failed import."""

    def start(self) -> None:
        try:
            super().start()
        except BaseException:
            self.close()
            raise

    def close(self) -> None:
        if self.process is not None:
            if os.name == "nt" and self.process.poll() is None:
                subprocess.run(["taskkill", "/PID", str(self.process.pid), "/T", "/F"],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
            elif self.process.poll() is None:
                self.process.kill()
            self.process.wait()
            self.process = None

    def restart(self) -> None:
        self.close()
        self.restarts += 1
        self.start()


def define_exporter(repl: LeanRepl, env: int | None) -> int | None:
    response = repl._exchange({"cmd": DEFINITION, "env": env}, repl.import_timeout)
    ok = "env" in response and not any(m.get("severity") == "error" for m in response.get("messages", []))
    repl.typed_fast_export = ok
    return response["env"] if ok else env


class ExportingSession(ModuleSession):
    """A module environment with the typed exporter defined once after its imports."""

    def __init__(self, repl: LeanRepl, *args: Any, **kwargs: Any) -> None:
        super().__init__(repl, *args, **kwargs)
        self.env = define_exporter(repl, self.env)


def export(repl: LeanRepl, proof_state: int) -> list[dict[str, Any]] | None:
    restarts = repl.restarts
    result = gi.export(repl, proof_state,
                       tactic=EXPORT_TACTIC if getattr(repl, "typed_fast_export", False) else None)
    if repl.restarts != restarts:
        raise ReplTimeout("typed export restarted the task environment")
    return result


class Exports:
    def __init__(self, repl: LeanRepl, exporter: Callable) -> None:
        self.repl = repl
        self.exporter = exporter
        self.cache: dict[int, list[dict[str, Any]] | None] = {}
        self.failures = 0
        self.attempts = 0

    def get(self, proof_state: int, count: int) -> list[dict[str, Any]] | None:
        if proof_state not in self.cache:
            self.attempts += 1
            goals = self.exporter(self.repl, proof_state)
            if goals is None or len(goals) != count:
                goals = None
                self.failures += 1
            self.cache[proof_state] = goals
        return self.cache[proof_state]


class Measures:
    def __init__(self) -> None:
        self.text: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
        self.typed: dict[str, set[str]] = {}
        self.firsts: set[str] = set()
        self.generated_text: set[tuple[str, ...]] = set()

    def expanded(self, state: State, goals: list[dict[str, Any]] | None) -> dict[str, Any]:
        order = state.multiset_key in self.text and state.ordered_key not in self.text[state.multiset_key]
        first = state.first_goal_key in self.firsts
        self.text.setdefault(state.multiset_key, set()).add(state.ordered_key)
        self.firsts.add(state.first_goal_key)
        key = gi.unordered_state_key(goals) if goals is not None else None
        typed_order = coupled = None
        if goals is not None:
            coupled = any(len(g) > 1 for g in gi.groups(goals))
            if key is not None:
                ordered = gi.ordered_state_key(goals)
                if ordered is not None:
                    typed_order = key in self.typed and ordered not in self.typed[key]
                    self.typed.setdefault(key, set()).add(ordered)
        return {"orderDuplicate": order, "goalDuplicate": first,
                "orderDuplicateTyped": typed_order, "coupled": coupled, "typedMultiset": key}

    def generated(self, child: State) -> bool:
        duplicate = child.multiset_key in self.generated_text
        self.generated_text.add(child.multiset_key)
        return duplicate


def script_of(states: list[State], child: State) -> list[str]:
    steps = []
    cursor = child
    while cursor.tactic is not None:
        steps.append(cursor.tactic.split("\n"))
        if cursor.parent is None:
            break
        cursor = states[cursor.parent]
    return [line for step in reversed(steps) for line in step]


def any_goal_search(repl: LeanRepl, root_proof_state: int, root_goals: list[str],
                    proposer: Callable[[State], list[str]], budget: int,
                    verifier: Callable[[list[str]], bool] | None = None,
                    identify: str = "ordered", export: Callable = export,
                    positions: str = "all", time_limit: float = 7200,
                    clock: Callable[[], float] = time.monotonic) -> dict[str, Any]:
    if identify not in ("text", "ordered", "multiset"):
        raise ValueError("identify must be text, ordered or multiset")
    if positions not in ("all", "first"):
        raise ValueError("positions must be all or first")
    if budget < 0:
        raise ValueError("budget must be nonnegative")
    if time_limit < 0:
        raise ValueError("time_limit must be nonnegative")
    started = clock()
    states = [State(0, root_proof_state, root_goals, None, None, 0)]
    frontier = deque([0] if root_goals else [])
    exports = Exports(repl, export)
    measures = Measures()
    measures.generated_text.add(states[0].multiset_key)
    seen_exact = {states[0].ordered_key}
    seen_typed: set[str] = set()
    key_of = gi.ordered_state_key if identify == "ordered" else gi.unordered_state_key
    if identify != "text":
        root_export = exports.get(root_proof_state, len(root_goals))
        root_key = key_of(root_export) if root_export is not None else None
        if root_key is not None:
            seen_typed.add(root_key)
    expansions = []
    proof = None
    steps = rejected = 0
    steps_at_proof = None
    stopped = None
    reported_failures = 0
    while frontier and len(expansions) < budget and proof is None:
        if clock() - started >= time_limit:
            stopped = "wall-clock"
            break
        state = states[frontier.popleft()]
        failures_before = reported_failures
        exported = exports.get(state.proof_state, len(state.goals))
        measured = measures.expanded(state, exported)
        candidates = proposer(state)
        valid = exact_duplicates = multiset_duplicates = typed_duplicates = tried = 0
        position_counts = {}
        interrupted = False
        for position in range(1, (len(state.goals) if positions == "all" else 1) + 1):
            if clock() - started >= time_limit:
                stopped = "wall-clock"
                interrupted = True
                break
            position_counts[str(position)] = 0
            picks = [f"pick_goal {position}"] if position > 1 else []
            selected = harness_step(repl, state.proof_state, picks) if picks else (state.goals, state.proof_state)
            if selected is None:
                raise RuntimeError(f"pick_goal failed at position {position}")
            for tactic in candidates:
                tried += 1
                steps += 1
                result = repl.tactic(selected[1], tactic)
                if result is None:
                    continue
                goals, proof_state = result
                child = State(len(states), proof_state, goals, state.id,
                              "\n".join(picks + [tactic]), state.depth + 1)
                if not goals:
                    script = script_of(states, child)
                    restarts = repl.restarts
                    accepted = verifier is None or verifier(script)
                    if repl.restarts != restarts:
                        raise ReplTimeout("verification restarted the task environment")
                    if not accepted:
                        rejected += 1
                        continue
                valid += 1
                position_counts[str(position)] += 1
                multiset_duplicates += measures.generated(child)
                exact_duplicate = child.ordered_key in seen_exact
                exact_duplicates += exact_duplicate
                seen_exact.add(child.ordered_key)
                child_key = None
                if identify != "text":
                    child_export = exports.get(proof_state, len(goals))
                    if child_export is not None:
                        child_key = key_of(child_export)
                if not goals:
                    states.append(child)
                    state.children.append(child.id)
                    proof = script
                    steps_at_proof = steps
                    break
                if identify == "text":
                    duplicate = exact_duplicate
                else:
                    duplicate = child_key is not None and child_key in seen_typed
                    typed_duplicates += duplicate
                    if child_key is not None:
                        seen_typed.add(child_key)
                if duplicate:
                    continue
                states.append(child)
                state.children.append(child.id)
                frontier.append(child.id)
            if proof is not None:
                break
        expansions.append({"state": state.id, "depth": state.depth, "goals": len(state.goals),
                           "candidates": len(candidates), "valid": valid, "exactDuplicates": exact_duplicates,
                           "steps": tried, "multisetDuplicates": multiset_duplicates,
                           "typedDuplicates": typed_duplicates, "positions": position_counts,
                           "exportFailures": exports.failures - failures_before} | measured |
                          ({"interrupted": True} if interrupted else {}))
        reported_failures = exports.failures
        if stopped is not None:
            break
    return {"expansions": expansions, "states": len(states), "proof": proof, "timeouts": 0,
            "rejected": rejected, "seconds": round(clock() - started, 1), "restarts": repl.restarts,
            "orderDuplicates": sum(bool(e["orderDuplicate"]) for e in expansions),
            "goalDuplicates": sum(bool(e["goalDuplicate"]) for e in expansions),
            "uniqueFirstGoals": len(measures.firsts), "steps": steps, "stepsAtProof": steps_at_proof,
            "exportFailures": exports.failures, "exportAttempts": exports.attempts,
            "distinctTypedMultisets": len(measures.typed), "stopped": stopped}


def coupling_probe(repl: LeanRepl, proof_state: int, proof: list[str]) -> dict[str, Any]:
    """Replay candidate steps; a preceding pick is reported in the original goal list's coordinates."""
    records = []
    pending = 1
    for step in proof:
        if step.startswith("pick_goal "):
            if pending != 1:
                raise ValueError("consecutive picks are not a goal-selection step")
            pending = int(step.split()[1])
            continue
        goals = export(repl, proof_state)
        partition = gi.groups(goals) if goals is not None else None
        coupled = None if partition is None else any(pending - 1 in g and len(g) > 1 for g in partition)
        selected = harness_step(repl, proof_state, [f"pick_goal {pending}"]) if pending > 1 else ([], proof_state)
        result = repl.tactic(selected[1], step) if selected is not None else None
        records.append({"step": step, "position": pending,
                        "groups": [[i + 1 for i in group] for group in partition] if partition is not None else None,
                        "chosenCoupled": coupled, "exportFailed": goals is None, "valid": result is not None})
        if result is None:
            return {"steps": records, "closed": False}
        proof_state = result[1]
        pending = 1
    if pending != 1:
        raise ValueError("proof ends with a pick")
    final = export(repl, proof_state)
    return {"steps": records, "closed": final == []}
