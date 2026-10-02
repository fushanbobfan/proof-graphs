# Reconstructing goal-origin graphs by hand

For each proof in your list, write down the steps of its goal-origin graph and the dependency edges between
them, following the definition below. Work from the proof's source and from the goals Lean displays; do not
look at any extraction, result, dataset, or audit file of this repository, and do not run its extractor or
its scripts.

## The definition

Steps are derived from the nodes:

- a node *produces* the goals present after it and absent before it, and
  *consumes* the goals present before it, absent after it, and never present
  before a later node of the proof (focusing constructs such as `·` and
  `case` hide goals without closing them);
- the *origin* of a goal is the deepest node producing it (a `have ... := by`
  node produces its continuation goal itself; a multi-binder `intro` produces
  through its last child); a goal no node produces (the case goals of
  `induction ... with`, `cases ... with`, `case tag x y =>`, the goal of a
  nested `by`, the steps of a `calc`) originates in the deepest node
  enclosing its first mention that holds some goal but not this one; a goal
  with neither has no origin (the statement's goal, a `decreasing_by`
  obligation);
- a node is a step when it is the origin of a goal or when it consumes a goal
  that none of its descendants consumes; every other node is a container; an
  origin that consumes nothing itself because a descendant consumes the goal
  it held (`simpa ... using (by tac)`, whose `simp` part is a child node) is
  merged into that descendant, so that one tactic is one step;
- a step produces the goals it originates and consumes the goals it consumes
  minus those consumed by its descendant steps;
- a step is *live* when it consumes a goal of a root node (the statement, a
  `decreasing_by` obligation, a nested `by` in a term) or a goal produced by
  a live step; the other steps belong to failed alternatives of `first`,
  `try`, and `repeat`, whose info nodes Lean keeps, and are dropped;
- a step depends on the origin of every goal it consumes.

Correction (count_linearizations_v2.py): a node consumes a goal present before it, absent after it, and never present before a later node of the proof outside the node's own subtree. A later node inside the node's own subtree does not count, so a tactic whose own internal node mentions the goal it closes (the internal node of `simpa ... using h` that leaves the goal as it was) still consumes it.

## How Lean behaves, which the definition relies on

1. Lean's info tree has a node for each tactic it elaborates, which is not always one node per tactic as written: `rw [a, b]` has one node per rewrite rule, and one for its closing `rfl` when that closes the goal; `intro x y` has one per binder; `conv_lhs` and `conv_rhs` insert a `conv` node; `cases h : e with` has two; a named `next` or `case` that renames hypotheses is a node. A tactic that runs on several goals (the second tactic of `t <;> s`, the body of `all_goals`) is one node, hence possibly one step, per goal it runs on. Where this list does not settle a case, Lean's own elaboration does: the goals it displays between tactics, or its source.
2. Almost every tactic that changes a goal (its target or its local context) replaces that goal with a new goal, and a tactic that closes a goal produces no goal, so a step that transforms a goal consumes the old goal and originates the new one.
3. Focusing (`·`, `next`, `case tag =>` without new names) and tactic sequences only select or hide goals; they are containers, not steps.

## What to write down

For each proof: its steps in source order, each with the source line where its tactic starts and the tactic
text, and its edges as pairs [i, j] of step indices (0-based, in your step order) meaning that step i
originated a goal that step j consumes. Note anything you were unsure of. A step's line is the line where its
info-tree node starts (for a rewrite rule, the rule's own line); two steps on one line are listed in the order
they run. Long proofs are expected: list every step.

```json
{"module": "...", "declaration": "...", "steps": [{"line": 12, "tactic": "intro x"}, ...],
 "edges": [[0, 1], ...], "notes": "..."}
```
