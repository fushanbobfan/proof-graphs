# Orderings replay v0.2

orderings-replay-v0.1 replayed every ordering of 64 small proofs and found all 197 other orderings of the 41 proofs
whose original order replayed to be Lean scripts. Its sample rule does not test whether goals share a metavariable
(`scripts/check_coupled_orderings.py` shows a proof the rule admits whose other ordering fails), and no goal of its
replayed proofs showed one. This experiment repeats the replay on every proof of the library and of both Mathlib
slices that the mechanism can replay, with 3 to 12 steps and the step derivation as corrected after
extraction-audit-v0.1, and records at every step of every replay whether a goal shows a metavariable, in its target
or in a hypothesis.

## Artifacts

- `preregistration.json`, `sample.json`: the rule (134 proofs: 67 from the library, 27 from the first slice, 40 from
  the second), the procedure, hypotheses H97 to H99 and check C37, registered before any proof of the sample was
  replayed;
- `results.jsonl`: per proof, whether it could be stated, the original order's replay with its metavariable counts,
  and every other ordering's outcome, with Lean's message for a tactic error;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_orderings_replay_v2.py --check-committed
```

recomputes the summary from the committed rows; CI runs it.

## Outcome

97 of the 134 proofs could be stated as an `example` in their module's context (29 library proofs and 8 from the
second slice could not), and the original order replays in 87 of them (10 failed on a tactic error): C37 holds.

- **H97 holds**: over the 86 replayable proofs none of whose goals shows a metavariable, all 909 other orderings
  replay.
- **H98 and H99 fail**: one proof is coupled, `CategoryTheory.Functor.isLeftDerivedFunctor_iff_isRightKanExtension`
  (3 steps, 2 orderings), whose goals show a metavariable in a hypothesis but never in a target; its other ordering
  replays.

## Interpretation boundary

The replay can pose only proofs whose steps are single source lines, and among those, goals that visibly share a
metavariable are rare: one of 87. So the result extends v0.1's to a sample twice as large, three corpora, and proofs
of up to 12 steps, and it shows that such proofs seldom couple their goals; it does not measure how often an
ordering fails when goals are coupled, for which the sample has one case. The constructed proof of
`fixtures/Coupled.lean` shows that such orderings can fail.
