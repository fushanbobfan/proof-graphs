#!/usr/bin/env python3
"""Goals alike up to the names of their hypotheses, and the tactic step that renames one into the other.

`search_keys.coarse_goal` identifies two goals when their printed texts agree once every hypothesis is renamed by
its position. A search that merges such goals must also turn one into the other, since the tactics of a proof
mention hypotheses by name. Two tactics change nothing but names: `rename_i` (Lean core) names the hypotheses
printed with `✝`, inaccessible or shadowed, and `rename'` (Mathlib) renames accessible ones, several at once. No
tactic makes a hypothesis inaccessible, so a goal is renamed toward the names of the hypotheses its target can
mention, and the target's inaccessible hypotheses, which no tactic of the target's proof can mention by name, keep
whatever names they have. `renaming_step` builds the step and `agrees` decides whether the renamed goal is the
target up to those names.
"""

from __future__ import annotations

import re

from search_harness import canonical_goal
from search_keys import IDENTIFIER_TAIL, coarse_goal

MARK = "✝"


def hypotheses(goal: str) -> list[str]:
    """The names of the goal's hypotheses in context order, as printed (`coarse_goal`'s parsing)."""
    lines = canonical_goal(goal).split("\n")
    turnstile = next((i for i, line in enumerate(lines) if line.startswith("⊢")), None)
    if turnstile is None:
        return []
    names: list[str] = []
    for line in lines[:turnstile]:
        if line.startswith(" "):
            continue  # a wrapped hypothesis continues on an indented line
        head, separator, _ = line.partition(" : ")
        if separator:
            names.extend(head.split())
    return names


def substitute(text: str, mapping: dict[str, str]) -> str:
    """Every whole-identifier occurrence of a name in `mapping` replaced at once (`coarse_goal`'s pattern)."""
    if not mapping:
        return text
    pattern = re.compile(r"(?<![\w'✝.!?])(" + "|".join(re.escape(n) for n in sorted(mapping, key=len, reverse=True))
                         + r")(?!" + IDENTIFIER_TAIL + ")")
    return pattern.sub(lambda m: mapping[m.group(1)], text)


def hidden(goal: str) -> list[int]:
    """The positions of the hypotheses no tactic can mention by name."""
    return [i for i, name in enumerate(hypotheses(goal)) if MARK in name]


def masked(goal: str, positions: list[int]) -> str:
    """The goal's canonical text with the hypotheses at `positions` renamed to placeholders."""
    names = hypotheses(goal)
    return substitute(canonical_goal(goal), {names[i]: f"◊{i}" for i in positions if i < len(names)})


def renaming_step(goal: str, target: str) -> list[str] | None:
    """Tactic lines that give `goal`'s hypotheses the names `target` gives the hypotheses it can mention, or None
    when the two do not correspond position by position. The lines are empty when no name needs to change.

    `rename'` runs first, then `rename_i`, which names the last inaccessible or shadowed hypotheses in order; the
    set it counts is computed after the `rename'`, which can shadow a hypothesis by giving a later one its name.
    """
    if coarse_goal(goal) != coarse_goal(target):
        return None
    ours, theirs = hypotheses(goal), hypotheses(target)
    if len(ours) != len(theirs) or len(set(ours)) != len(ours) or len(set(theirs)) != len(theirs):
        return None
    accessible: list[tuple[str, str]] = []
    wanted: dict[int, str] = {}
    for position, (mine, name) in enumerate(zip(ours, theirs)):
        if MARK in name or mine == name:
            continue
        if MARK in mine:
            wanted[position] = name
        else:
            accessible.append((mine, name))
    lines = []
    if accessible:
        lines.append("rename' " + ", ".join(f"{old} => {new}" for old, new in accessible))
    if wanted:
        renamed = dict(accessible)
        after = [renamed.get(name, name) for name in ours]
        unnamed = [i for i, name in enumerate(after) if MARK in name or name in after[i + 1:]]
        if not set(wanted) <= set(unnamed):
            return None
        first = min(wanted)
        lines.append("rename_i " + " ".join(wanted.get(i, "_") for i in unnamed if i >= first))
    return lines


def agrees(renamed: str, target: str) -> bool:
    """Whether `renamed` prints as `target` once the hypotheses `target` cannot mention are masked in both."""
    if len(hypotheses(renamed)) != len(hypotheses(target)):
        return False
    positions = hidden(target)
    return masked(renamed, positions) == masked(target, positions)
