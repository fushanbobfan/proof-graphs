# Design: order redundancy of Lean tactic proofs

Status: the three steps and two follow-ups are done; what they answered, and
what is left, is in "Where this ends" below.
Corpora: ProofNet-IR v0.10.0 (`f0fd97f8592938165dbffd91656d226b6102adcc`) and
Mathlib v4.32.0 (`81a5d257c8e410db227a6665ed08f64fea08e997`)

## The research object

Proof nets exist for multiplicative linear logic and nowhere near Lean's
dependent types, unification, and rewriting. What the MLL measurements of
ProofNet-IR v0.11 counted, however, was not nets but *rule-order redundancy*:
linear proofs that differ only in the order of independent steps and denote
the same object. That notion transfers to Lean without new theory:

> The goal-dependency graph of a tactic proof: a step is a tactic node that
> originates goals or closes a goal none of its sub-tactics closes; it depends
> on the steps that originated the goals it consumes. Two tactic scripts are
> the same graph exactly when they differ only in the order of independent
> steps. (The exact derivation from Lean's info trees is the docstring of
> `scripts/count_linearizations.py`; amendments 1 and 2 of the first
> experiment record how it was corrected before any corpus count.)

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
   in the preregistration. **Done**: H10 holds (medians 15, 6,720, 8.8·10^13,
   1.9·10^51 by step stratum), H11 fails at 51 steps and more (0.502).
   Repeated on a systematic Mathlib slice (`experiments/linearizations-mathlib-v0.1`,
   H12 and H13, both hold): the same distribution, so the counts are not an
   artifact of one library's style.
2. **Measure the redundancy inside a real search.** Step 1 settled the
   original form of this step before it was built: Lean applies a tactic to
   the first goal, and that convention is one linearization of the graph, so
   a search that keeps to it and has no goal-selecting tactic never produces
   two states that differ only in goal order. What a whole-state search
   (the state is the full goal list, as in ReProver-style search) still
   duplicates relative to the graph is the *goal*: every branch that solves
   the first goal differently carries the same remaining goals along and
   attacks each of them again. The revised step therefore drives a
   breadth-first whole-state search with a local model as proposer, through
   the Lean REPL, on theorems the model can make progress on, and records
   two fractions of the expansions: those whose goal multiset already
   appeared in another order (order redundancy, expected negligible; the
   model can emit `swap`, `case`, `rotate_left`), and those whose first goal,
   canonicalized, was already expanded elsewhere (goal sharing, the
   redundancy an AND-OR search over the graph removes). The slice of step
   1b (`experiments/linearizations-mathlib-v0.1`) supplies the theorems.
   **Done** (`experiments/search-v0.1`, H14 and H15, both fail): order
   redundancy is 2 to 3 percent of the expansions, not zero — `symm` before
   `constructor` reverses two subgoals without any goal-selecting tactic —
   and goal sharing is 9 to 11 percent, just under the registered 10 percent
   in both arms.
3. **Equal-budget comparison.** The same proposer and the same number of
   model and Lean calls, searching over whole states versus over goals
   (AND-OR, sharing every canonical goal); written so that either can win.
   Goals that share metavariables (the non-forest graphs of step 1, 8 of
   3,994) are where the AND-OR search can be wrong, and are reported.
   **Done** (H16a and H16b, both fail): at 24 expansions the AND-OR search
   proves 4 and 5 tasks against the whole-state search's 5 and 5, and it
   discards 3 to 4 percent of its candidates as entangled, a tactic on one
   goal having changed another.

## Boundaries

- Only the order of independent steps is quotiented; different proof terms of
  one proposition and different tactic paths to one goal are not.
- Mature searchers (HyperTree Proof Search and its descendants) already
  search over goals, so step 3's comparison quantifies a known design choice
  rather than proposing a new one; a small or absent gain would locate the
  MLL result precisely and is worth writing down.
- Lean 4 tactic proofs only; term-mode proofs are not in the corpus.

## Where this ends

The three steps answer the question they were written for. Rule-order
redundancy is real and explodes with proof length — a 461-step proof admits
10^628 orderings, and a Mathlib slice has the same distribution — but almost
all of it is already quotiented by Lean's convention of acting on the first
goal: in a real tactic search 2 to 4 percent of the expansions are states
that differ only in goal order, and the fraction falls as the search deepens
(`search-v0.2`). Goal sharing, the redundancy a graph representation does
remove, grows with work, from about 10 to 18 percent between 24 and 192
expansions, but at this proposer strength work is not the bottleneck: eight
times the budget found no new proof, and the search over goals proves no
more than the search over states. It proves less where goals share an
existential witness, which a tactic on one goal assigns for both; treating
goals as independent must discard exactly those moves. Mature goal searches
anticipate this: HyperTree Proof Search splits a tactic state into goals
only where they share no metavariable, and Aesop adds the coupled goals, with
the assignment applied, as extra subgoals of the assigning rule. Our search
treats every goal as independent on purpose, to measure how often that
assumption fails. The MLL gain does not
transfer: in a resource logic the graph quotients a factorial, in Lean the
goal stack has already absorbed it, and the dependencies it has not absorbed
are the ones the graph would wrongly cut.

The proposal's third layer, telling good proofs from mediocre ones, was
tested on 294 golf pairs from Mathlib's history (`golf-v0.1`): the proof the
community accepted as better is shorter in 210 of 238 pairs, and its lower
structure index is the shadow of its length, not a structural difference.
The step-dependency graphs of every proof extracted here are in
`datasets/proof-graphs-v0.1.jsonl.gz` (7,285 graphs).

What would extend this is not more of the same:

- a proposer strong enough that searches run deep (here every proof was
  found within a dozen expansions, and the searches that ran longer found
  nothing);
- the redundancy this design explicitly does not touch: different tactic
  paths to the same goal, and different proof terms of one proposition;
- for the third layer, a registered test of another graph quantity (depth,
  width, branching), or of quantities outside the graph (lemmas used, term
  size, elaboration time).

Until one of those is worth doing, the repository is a record, not a
programme.
