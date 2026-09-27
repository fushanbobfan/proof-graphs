# Keys v0.1: finished searches re-keyed by Lean expressions

The searches of this program identify goals by text: the printed goal with metavariable numbers erased (the
default key), or that text with hypotheses renamed (the coarse key). How do those keys compare with goal
identity taken from Lean's expressions? This experiment replays finished searches unchanged and re-keys every
state they reached with `scripts/goal_identity.py`: each goal's instantiated context and target exported by a
`run_tac` block and written structurally, hypotheses by position, bound variables by de Bruijn index, every
implicit argument and universe written out, metavariables numbered by first occurrence. That is the
faithful key.

The units are search-v0.7's four searches on its 200 tasks, replayed from their recorded draws (a search that
would need a new draw raises), and search-v0.4's keys arm (the menu's whole-state search at 24 expansions) on
its 300 tasks: 1,100 units.

## Artifacts

- `preregistration.json`: the units, the key, the measures, hypotheses H59 to H63, and checks C10 to C12;
- `results.jsonl`, `logs.jsonl.gz`: per unit, the replay's outcome and audit, and its log (every expanded
  state, every successful tactic, every state's keys under the three keys);
- `summary.json`, `report.md`: the shares and the decisions;
- `amendment-1.json`: the rerun of the units the first run's replays failed to reproduce, and why.

## Reproduction

```text
python scripts/run_key_replay.py --check-committed
```

recomputes every unit's audit from its log and the summary from the rows; CI runs it. `--run` replays the
searches (a Mathlib REPL per worker; about three hours on ten workers).

## The run and its amendment

The first run (committed in `470b61d`) shared the machine with search-v0.8 and ran out of Windows commit
memory: 89 replays were not constructed and 12 abandoned although the original searches had finished, and
C10 counted 103 of 932 replays as differing. Amendment 1 replayed those 103 units once more with three
workers: all 103 reproduced their recorded outcomes, including the two whose expansion count had differed.
The hypothesis decisions were the same in both runs. Numbers below are after the amendment.

## Outcome

| Search | Goal duplicates: default / coarse / faithful | Order duplicates, faithful | Drops falsely identified |
| --- | --- | ---: | ---: |
| search-v0.7 whole-state, printed | 4.9% / 26.2% / 27.2% | 0.1% | 170 of 2,905 (5.9%) |
| search-v0.7 whole-state, up to renaming | 4.2% / 5.9% / 8.2% | 0.2% | 214 of 4,335 (4.9%) |
| search-v0.4 keys arm (menu) | 15.9% / 28.0% / 28.5% | 5.2% | 410 of 7,009 (5.8%) |

- **H59, H60 supported**: the coarse key's goal-duplicate share is within a point of the faithful key's, for
  the step-prover searches (26.2% against 27.2%) and the menu searches (28.0% against 28.5%).
- **H61 supported**: under the faithful key, order duplicates stay at 0.1% of the step-prover search's
  expansions; the first-goal convention's effect does not depend on the text key.
- **H62 not supported**: the printed-goal AND-OR search merged 2,809 arriving goals into existing ones, and
  244 of them (8.7%) joined goals whose Lean expressions differ.
- **H63 not supported**: of the 14,249 states the whole-state searches dropped as duplicates, 794 (5.6%) have
  a faithful key different from the state they were taken to duplicate.

The keys also miss identities: 28.6% of the goals the printed AND-OR search created new were faithfully
equal to an existing goal, and 27.0% of the children the printed whole-state search kept duplicate an earlier
kept state faithfully; for the whole-state search up to renaming, which keys states by the coarse key, the
missed share is 3.5%, so most of the printed key's misses are goals that differ only in hypothesis names. So
the coarse key is right in aggregate, while item by item 5% to 9% of the identifications the text keys make
join goals whose expressions differ.

C10 holds after the amendment (0 of 932 replays differ) and C11 holds (763 of 763 reconstructions reproduce
the searches' own counts). **C12 fails**: 1,554 of 70,129 states (2.2%) did not export, against a ceiling of
1%. 1,390 of them are every state of the eight units of `MvPolynomial.coeff_add_pow` and
`MvPolynomial.pow_idealOfVars`, where the `run_tac` block, elaborated inside those declarations' scope, stops
with Lean's `internal exception abortTermElab`; search-v0.8 defines the export as a tactic right after the
imports instead. States that did not export have no faithful key and are left out of the shares.

## Interpretation boundary

The faithful key is syntactic: goals that are definitionally equal but written differently, for instance
through different instance paths, count as different. The replays re-key searches that ran with text keys;
they do not show what a search keyed by Lean expressions would prove.
