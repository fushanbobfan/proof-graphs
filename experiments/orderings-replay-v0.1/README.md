# Orderings replay v0.1

An ordering of a goal-origin graph respects which step created the goal each
step consumes. Does it therefore run as a Lean script? Goals can share a
metavariable, and a tactic can depend on the order of the goals it sees, so
the graph alone does not guarantee it. This experiment replays every ordering
of 64 small proofs in the theorem's own context.

## Artifacts

- `preregistration.json`, `sample.json`: the sample rule (seed 20260925; per
  corpus up to 40 proofs with one root `by` block, 3 to 8 steps, a forest graph
  whose steps each consume one goal, 2 to 24 orderings, and steps that can be
  cut out of the source one line each), the procedure, and hypothesis H29;
- `results.jsonl`: per proof, whether it could be stated, the original order's
  replay, and every other ordering's outcome;
- `summary.json`, `report.md`.

## Procedure

A fresh REPL per proof states the theorem as an `example` in its module's
context, as the search experiments do. Each ordering is replayed step by step:
`rotate_left k` brings the goal the step consumed in the original proof to the
front, then the step's tactic text runs. An ordering replays when every tactic
succeeds, every step leaves exactly the goals the graph says it creates, no
goal is left, and the script re-verifies from the statement.

## Reproduction

```text
python scripts/run_orderings_replay.py --check-committed
```

recomputes the summary from the committed rows; CI runs it.

## Outcome

45 of the 64 proofs could be stated as an `example` (19 ProofNet-IR proofs
could not), and the original order replays in 41 of them (4 failed on a
tactic error). **H29 holds**: all 197 other orderings of those 41 proofs
replay, 100%.

## Interpretation boundary

The sample is small proofs whose graphs are forests with one goal per step and
whose steps are single lines. The rule does not test whether goals share a
metavariable, and it admits proofs where they do:
`scripts/check_coupled_orderings.py` shows one (`fixtures/Coupled.lean`) whose
other ordering fails. In the sample, no goal of the 41 replayed proofs shows a
metavariable in its target at any step of any ordering (`mvarGoals` is 0 in all
238 replays), so the sample happens to contain no proof whose goals visibly
share one, which is where an ordering is most likely to fail. The 19 proofs
that could not be stated are ProofNet-IR proofs, 17 of them from one module,
`ProofNetIR.Unification`; the 4 originals that failed did so on a tactic error.
The result says that the orderings of such proofs are real alternative scripts,
not that every ordering of every graph is.
