#!/usr/bin/env python3
"""Proposals drawn once per goal and occurrence, shared by the two searches of a task.

A sampled proposer makes every search a draw. In search-v0.5 the two searches met the same first goal and drew
different candidates for it, so a theorem one search proved and the other did not could come from the draw as
easily as from the design. Here the two searches of a task share their draws, the standard way to compare two
systems under the same randomness (common random numbers): the n-th time a search expands a goal, it gets the
n-th set of candidates drawn for that goal in this task, whichever search drew it first.

Both searches therefore see identical candidates the first time each meets a goal. The AND-OR search expands a
goal once, so it only ever uses the first set; the whole-state search may expand one goal in several states,
and on each later expansion it gets a fresh set, as a state search with a sampled proposer does. Goals are
identified by `canonical_goal`, the identity the searches themselves use, so that goals printed with different
metavariable numbers or case tags share their draws.

The draws are made with `step_prover`'s sampling (concurrent single-completion requests, first line of each
reply, duplicates dropped in order), unchanged, and every draw is logged with its prompt, replies, candidates,
occurrence, and the search that made it.
"""

from __future__ import annotations

import time
from typing import Any, Callable

import step_prover as prover
from search_harness import State, canonical_goal


class CommonDraws:
    """The draws of one task. Not shared between tasks, and used by one search at a time."""

    def __init__(self, samples: int, temperature: float, max_tokens: int, model: str) -> None:
        self.samples, self.temperature, self.max_tokens, self.model = samples, temperature, max_tokens, model
        self.sets: dict[str, list[list[str]]] = {}
        self.log: list[dict[str, Any]] = []
        self.counts: dict[str, dict[str, int]] = {}

    def draw(self, goal: str) -> tuple[list[str], dict[str, Any]]:
        prompt = goal.rstrip() + prover.SEPARATOR
        started = time.monotonic()
        replies = prover.complete(prompt, self.samples, self.temperature, self.max_tokens, self.model)
        candidates: list[str] = []
        for text in replies:
            tactic = prover.tactic_of(text, prompt)
            if tactic is not None and tactic not in candidates:
                candidates.append(tactic)
        return candidates, {"prompt": prompt, "replies": replies, "candidates": candidates,
                            "seconds": round(time.monotonic() - started, 2)}

    def proposer(self, search: str) -> Callable[[State], list[str]]:
        occurrences: dict[str, int] = {}
        counts = self.counts.setdefault(search, {"drawn": 0, "shared": 0})

        def propose(state: State) -> list[str]:
            if not state.goals:
                return []
            goal = state.goals[0]
            key = canonical_goal(goal)
            n = occurrences.get(key, 0)
            occurrences[key] = n + 1
            sets = self.sets.setdefault(key, [])
            if n < len(sets):
                counts["shared"] += 1
                return list(sets[n])
            assert n == len(sets), "a search needs its n-th draw of a goal only after its (n-1)-th"
            candidates, entry = self.draw(goal)
            sets.append(candidates)
            counts["drawn"] += 1
            self.log.append(entry | {"search": search, "occurrence": n})
            return list(candidates)
        return propose
