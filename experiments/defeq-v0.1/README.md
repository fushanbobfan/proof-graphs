# Defeq v0.1: goal identity up to definitional equality

keys-v0.1 re-keyed finished searches by Lean expressions, with the faithful key of `scripts/goal_identity.py`, and
found the coarse text key right in aggregate. The faithful key is syntactic: two goals that differ only by an instance
path, a universe level written differently, or an unreduced beta redex count as different, although they are
definitionally equal. How much does identifying goals up to definitional equality add, and at what cost? This
experiment replays keys-v0.1's whole-state units unchanged and, after each search, merges the distinct goals it met
as Lean's `Meta.Canonicalizer` would: a hash that ignores implicit arguments, proof arguments, and constants' universe
levels, and `isDefEq` only between goals with equal hashes, separately at reducible, instances, and default
transparency. `scripts/goal_defeq.py` re-implements the canonicalizer, since not every Mathlib module imports it.

A goal is compared as its closed type: its local context, implementation details skipped, abstracted over its target,
printed with `pp.all` and elaborated back, so that goals of different proof states meet in the task's root state.
`h : P ⊢ Q` and `⊢ P → Q` share a closed type but are different goals, so the number of hypotheses is part of the
hash. A goal with a metavariable is not printed and keeps its faithful key.

The units are keys-v0.1's whole-state units: search-v0.7's step-prover search, replayed from its recorded draws, on
200 tasks, and search-v0.4's keys arm, the menu's whole-state search at 24 expansions, on 300 tasks: 500 units.

## Artifacts

- `preregistration.json`: the identity, the measures, hypotheses H90 to H93, and checks C32 to C34;
- `amendment-1.json`: two analyses added during the run, before any result was computed, and why;
- `amendment-2.json`: the merge run as a tactic defined after the imports, and the units whose merge had failed run
  again, and why;
- `results.jsonl`, `logs.jsonl.gz`: per attempt, the replay's outcome and costs, and per unit its log (every expanded
  state with its faithful keys, each distinct goal's round-trip status, and the merge's classes at each transparency);
- `summary.json`, `report.md`: the shares, the costs, the checks, and the decisions;
- `amendment-1-results.json`: the amendment's two analyses.

## Reproduction

```text
python scripts/run_defeq_replay.py --check-committed
python scripts/defeq_v01_amendment.py --check
```

recompute the summary from the rows and logs, and the amendment's analyses; CI runs both. `--run` replays the
searches and merges their goals (a Mathlib REPL per unit; about seven hours on three workers).

## Amendment 1

C32 compares each replay's expanded states, by faithful keys, with keys-v0.1's log. keys-v0.1's export failed on every
state of 10 of the 426 units it recorded among these, and this run's export, a tactic defined after the imports, keys
them; the registered check then counts those units as differing with nothing to compare, which alone exceeds its 2%
allowance. The amendment, committed before any result was computed, keeps the registered check and adds C32 over the
states keys-v0.1 keyed. It also reports H93's ratio with the elaboration of the printed types included, because the
registered code hashes each goal while elaborating it, so hashing is timed with elaboration rather than with the merge
as the preregistration describes.

## Amendment 2

The merge first ran as a `run_tac` block in each task's root state, which Lean elaborates in the declaration's own
scope. In 24 units (19 step-prover, 5 menu, all in CategoryTheory, Polynomial, and MvPolynomial modules) the block
never elaborated: files that open the CategoryTheory namespace turn its `Prod.snd` into `CategoryTheory.Prod.snd`,
and Polynomial and MvPolynomial files stop it with `internal exception abortTermElab`, as they stopped keys-v0.1's
export. Lean's `try` also rethrows heartbeat exceptions, so an `isDefEq` check that exhausted its budget would have
ended the whole pass instead of counting as unequal, as the preregistration states. Amendment 2 runs the merge as a
tactic defined right after the imports, beside the export tactics, with guards that catch runtime exceptions, and runs
the 24 units again. The 188 merges that had completed are kept: no runtime exception occurred in them, and where both
versions complete they agree exactly (checked on four units).

## The run

The run took about seven hours of machine time between 2026-10-07 21:39 and 2026-10-08 13:41 (Los Angeles), on three
workers, with two pauses while the machine was in other use and a ten-minute stop for amendment 2; no runner
crashed. There are 548 attempts for the 500 units: the 24 units of amendment 2 ran twice before it and once after,
and each of the 239 constructed attempts after it completed its merge. 73 units were not constructed (31
step-prover, 42 menu), the same 73 as in keys-v0.1.

## Outcome

| Units | Expansions | Goal duplicates: expression key / up to definitional equality (reducible, instances, default) | Extra state merges (instances) | Printed-key false drops definitionally equal (instances) |
| --- | ---: | --- | ---: | ---: |
| search-v0.7 whole-state search, step prover (169 units) | 4,751 | 27.9% / 31.0%, 31.0%, 31.0% | 3.5% | 138 of 165 (83.6%) |
| search-v0.4 keys arm, menu (258 units) | 3,417 | 28.8% / 28.9%, 28.9%, 29.0% | 2.1% | 349 of 382 (91.4%) |

- **H90 not supported**: in the step prover's whole-state search, identity up to definitional equality adds 3.2
  points of goal duplicates (150 expansions; 95% interval 2.0 to 4.7 points, resampling modules), against a registered
  ceiling of 2. Every one of the 150 is found at reducible transparency already.
- **H91 supported**: in the menu's, it adds 0.1 points (4 expansions; 0.0 to 0.3).
- **H92 supported**: of the printed key's false drops whose goals all round-tripped, 487 of 547 (89.0%) join goals
  that are definitionally equal at instances transparency (482 at reducible, 507 at default). Most of the printed
  key's false drops, counted as keys-v0.1 counted them, thus join goals equal up to unfolding.
- **H93 supported**: the merge, bucket lookups and `isDefEq`, takes a median 0.008% of the step prover's tactic time
  per unit and 0.0004% of the menu's; no check exhausted its heartbeats (560 and 258 checks at instances
  transparency, 536 and 229 accepted). With the elaboration and hashing of the printed types added (amendment 1), the
  median is 16% of the step prover's tactic time and 0.8% of the menu's. That time is mostly the text round trip that
  carries goals from their states to the root state, which a search holding the expressions would not need, but it
  also contains the hashing, which was not timed apart.

C33 holds: 11,382 of the 11,591 distinct goals without a metavariable round-trip (98.2%; 8,992 exactly, 2,390 up to
reducible unfolding). C34 holds: all 427 merges complete, and 11,373 of the 11,382 round-tripped goals elaborate
again in them.

**C32 fails**: 391 of 426 replays match keys-v0.1 by faithful keys, and 401 of 426 over the states keys-v0.1 keyed
(amendment 1). Yet every one of the 426 reaches keys-v0.1's outcome and expands as many states, with the same printed
keys at every expansion: the searches are reproduced, and what differs is the expression key of some states. Ten
units are amendment 1's. In the other 25, 255 expanded states have keys different from keys-v0.1's, and 253 of them
hold a goal with a metavariable. The expression key writes universe metavariables with Lean's internal names, since
its renumbering expects another spelling (`?u.N`), and this run's three added definitions advance Lean's name
generator. Built both ways, the root state of `QPF.Fix.dest_mk` reproduces each run's logged key, and the two exports
differ only in `QPF.{u,?_mvar.12318,v}` against `QPF.{u,?_mvar.193814,v}`. The remaining two states, in
`AlgebraicGeometry.injective_germ_basicOpen`, are not explained.

## A defect in the expression key

That analysis exposes a defect of `goal_identity.py`'s expression key, which keys-v0.1, search-v0.8, and search-v0.9
use. Goals that differ only in the names of universe metavariables get different keys. The defect can only keep
identical goals apart, never join different ones. Within one search a universe metavariable inherited from the root
keeps its name, so only those created during the search can split an identity; here the expansions whose first goal
has a metavariable of either kind are 3.8% of the step prover's and 12.3% of the menu's. It leaves this experiment's
comparisons alone, since the merge takes only goals without metavariables, so that goals with one enter the
expression-key and the definitional measures alike. The typed key of goal-selection-v0.1 numbers universe
metavariables by first occurrence.

## Interpretation boundary

The merge joins goals that `isDefEq` proves equal within 200,000 heartbeats, and only goals with equal hashes are
compared: definitionally equal goals that hash differently (the canonicalizer hashes `@id ℕ a` and `a` differently)
stay apart. The shares are therefore lower bounds on identity up to definitional equality at each transparency. The
goals are compared after the searches, which ran with text keys; the replays do not show what a search keyed by
definitional equality would prove. The logs keep a hash of each printed closed type, not the text, so which
differences the merges bridge is not recorded.
