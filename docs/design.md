# Design: order redundancy of Lean tactic proofs

Status: active
Corpus: ProofNet-IR v0.10.0 (`f0fd97f8592938165dbffd91656d226b6102adcc`)

## The research object

Proof nets exist for multiplicative linear logic and nowhere near Lean's
dependent types, unification, and rewriting. What the MLL measurements of
ProofNet-IR v0.11 counted, however, was not nets but *rule-order redundancy*:
linear proofs that differ only in the order of independent steps and denote
the same object. That notion transfers to Lean without new theory:

> The goal-dependency graph of a tactic proof: a step is a leaf tactic node
> that consumes or produces goals; it depends on the steps that produced the
> goals it consumes. Two tactic scripts are the same graph exactly when they
> differ only in the order of independent steps.

This is the most conservative Lean analogue of a proof net: it quotients
precisely what exchange and rule permutation quotient in MLL, no more.

## Three steps, each registered before its data exists

1. **Count the redundancy on real proofs** (`experiments/linearizations-v0.1`).
   Extract the goal-dependency graph of every tactic proof in the corpus from
   Lean's info trees and count its linear orderings exactly: the hook-length
   formula `n! / prod(subtree sizes)` for forests, subset dynamic programming
   for other graphs of at most 22 steps. Report the distribution by step
   count, and the structure index `log L / log n!` (0 for a chain, 1 when
   every step is independent) as a side quantity. Hypotheses H10 and H11 are
   in the preregistration.
2. **Measure the redundancy inside a real search.** A minimal best-first
   tactic search over Lean goals (a fixed tactic menu first, a local model
   later) records every expanded state; states are canonicalized as goal
   multisets, and the fraction of expansions that coincide with an earlier
   state after canonicalization is the budget spent on order redundancy.
3. **Equal-budget comparison.** The same proposer and budget, searching over
   ordered states versus canonical states; written so that either can win.
   If the proposer already works one goal at a time, the arms coincide, and
   that is the answer: standard goal management absorbs this redundancy.

## Boundaries

- Only the order of independent steps is quotiented; different proof terms of
  one proposition and different tactic paths to one goal are not.
- Mature searchers already deduplicate by goal, so the expected outcome of
  step 3 is that the graph representation adds little at this level; that
  outcome would locate the MLL gain precisely and is worth writing down.
- Lean 4 tactic proofs only; term-mode proofs are not in the corpus.
