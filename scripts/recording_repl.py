#!/usr/bin/env python3
"""A REPL session that records what a search does, so a finished search can be re-keyed without changing it.

`RecordingRepl` is a `LeanRepl` whose `tactic` also exports every state a successful tactic reaches with
`goal_identity`, and which notes every state a search expands (the searches of search_keys.py and
search_renaming.py call `trace_state` through `goal_keys` exactly once per expansion, on the expanded state). The
searches themselves run unchanged. The log then holds, in order:

- `("x", s)`: state `s` was expanded;
- `("t", s, t)`: a tactic applied to state `s` succeeded and produced state `t`;

and, for every state reached or expanded, its goals under three keys: the printed default key and coarse key of
search_keys (digests of `canonical_goal` and `coarse_goal`), and the faithful key of `goal_identity`, with the
state's faithful key and its partition into metavariable-coupled groups. A search's candidate results are the
tactic events whose source is the state it is expanding; the harness's own calls (`pick_goal` to bring a goal to
the front, the renaming checks of search_renaming) start from other states.
"""

from __future__ import annotations

import re
import time
from typing import Any

import goal_identity as gi
from lean_repl import LeanRepl, ReplTimeout
from search_harness import canonical_goal
from search_keys import TRACE, coarse_goal, digest

PICK = re.compile(r"pick_goal \d+")


class RecordingRepl(LeanRepl):
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self.events: list[list[Any]] = []
        self.states: dict[int, dict[str, Any]] = {}
        self.export_failures = 0
        self.export_seconds = 0.0
        self.recording = False
        super().__init__(*args, **kwargs)

    def summarize(self, proof_state: int, goals: list[str]) -> dict[str, Any]:
        entry: dict[str, Any] = {"default": [digest(canonical_goal(g)) for g in goals],
                                 "coarse": [digest(coarse_goal(g)) for g in goals]}
        started = time.monotonic()
        exported = gi.export(self, proof_state)
        self.export_seconds += time.monotonic() - started
        if exported is None or len(exported) != len(goals):
            self.export_failures += 1
            entry |= {"faithful": None, "state": None, "groups": None}
        else:
            entry |= {"faithful": [gi.goal_key(g) for g in exported], "state": gi.state_key(exported),
                      "groups": gi.groups(exported)}
        return entry

    def tactic(self, proof_state: int, text: str) -> tuple[list[str], int] | None:
        result = super().tactic(proof_state, text)
        if result is not None and self.recording:
            goals, new_state = result
            # the harness brings a goal to the front with `pick_goal n` just before expanding the result
            self.events.append(["t", proof_state, new_state] + (["p"] if PICK.fullmatch(text) else []))
            if new_state not in self.states:
                self.states[new_state] = self.summarize(new_state, goals)
        return result

    def _exchange(self, request: dict[str, Any], timeout: float) -> dict[str, Any]:
        if self.recording and request.get("tactic") == TRACE:
            state = int(request["proofState"])
            self.events.append(["x", state])
            if state not in self.states:
                self.recording = False  # the export's own calls are not events
                try:
                    goals = self._goals_of(state)
                    self.states[state] = self.summarize(state, goals) if goals is not None else \
                        {"default": None, "coarse": None, "faithful": None, "state": None, "groups": None}
                finally:
                    self.recording = True
        return super()._exchange(request, timeout)

    def _goals_of(self, proof_state: int) -> list[str] | None:
        """A state's goals as the REPL prints them, read by applying a tactic that changes nothing."""
        try:
            response = super()._exchange({"tactic": "skip", "proofState": proof_state}, self.timeout)
        except ReplTimeout:
            return None
        goals = response.get("goals")
        return list(goals) if isinstance(goals, list) else None
