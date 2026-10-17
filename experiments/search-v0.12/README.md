# Search v0.12

search-v0.11 found the coupled-group search ahead of the whole-state search on 591 held-out theorems: 7 tasks to 1
(one-sided p = 0.035), +1.0 point of proof rate within 48 expansions. No proof that decided the comparison passed
through a group of several goals. That leaves open whether the gain comes from keeping coupled goals together or from
searching goals at all. This experiment answers it with an independent-goal arm on the same tasks and candidates. It
runs search-v0.10's goal search (single goals merged by the typed key; a candidate that changes another goal is
discarded as entangled) at 48 expansions in a fresh REPL through `search_typed_v2`, on the 591 tasks search-v0.11
stated. Its candidate stream is seeded with the sets search-v0.11 recorded, keyed as there by the goal's printed text,
and it draws fresh sets only where it meets a goal or an occurrence search-v0.11 never drew. Its rows are paired
with search-v0.11's latest rows.

## Artifacts

- `preregistration.json`, `tasks.json`: the 591 tasks, the search, the seeding and attempt rule, hypotheses H112 to
  H114 and checks C45 to C47, registered on 2026-10-13 before any unit ran;
- `results.jsonl`: one row per task and attempt, the latest counting;
- `draws.jsonl.gz`: the candidate sets drawn fresh;
- `summary.json`, `report.md`: the summary, by this experiment's own code.

## Reproduction

```text
python scripts/test_search_goals_holdout.py
python scripts/run_search_goals_holdout.py --check-committed
```

test the seeding, the attempt rule and the summary without Lean, and recompute the summary from the committed rows;
CI runs both.

## Outcome

All 591 tasks were posed, and every unit finished in its first attempt, with no error, abandoned search or repeat
(C45 holds). 2 of 53,501 typed exports failed (C46 holds). Of the 16,852 candidate sets the search took, 16,291 were
sets search-v0.11 recorded and 561 were drawn fresh; every seeded set is one search-v0.11 recorded for that goal and
occurrence (C47 holds).

Within 48 expansions the goal search proves 154 tasks (142 within 24), against 153 for the group search and 147 for
the whole-state search (search-v0.11's rows):

| Pair | Both | First only | Second only | Difference | Newcombe 95% | Modules 95% | One-sided sign test |
| --- | ---: | ---: | ---: | ---: | --- | --- | ---: |
| groups over goals | 153 | 0 | 1 | -0.2 pt | -0.6 to +0.3 | -0.6 to 0.0 | 1.0 |
| goals over whole states | 146 | 8 | 1 | +1.2 pt | +0.2 to +2.2 | +0.3 to +2.2 | 0.020 (Holm 0.039) |
| groups over whole states (search-v0.11) | 146 | 7 | 1 | +1.0 pt | +0.04 to +2.0 | +0.2 to +1.9 | 0.035 |

- **H112 holds**: the group search does not prove significantly more tasks than the goal search (p = 1.0).
- **H113 holds**: the goal search proves significantly more tasks than the whole-state search (8 to 1, p = 0.020,
  Holm-adjusted 0.039).
- **H114 holds**: the upper limit of the 95% interval for the group search's rate minus the goal search's is +0.3
  points, below the registered one point.

Every task the group search proves, the goal search proves too, and the goal search alone proves
`isLocallyInjective_iff_nhds`. The eight tasks the goal search proves and the whole-state search does not are the
group search's seven, among them `DFinsupp.prod_mapRange_index` (here proved in the first attempt), and that one. The
whole-state search's one, `MeasureTheory.LocallyIntegrableOn.congr`, neither goal-level search proves.

## Interpretation boundary

On these theorems and with these candidates, keeping metavariable-coupled goals together adds nothing measurable to
searching goals independently. The group search's gain over whole states is the goal search's gain, and the goal
search's lead over whole states survives Holm's adjustment. The goal search ran after search-v0.11, on the same
machine, REPL, Mathlib and model, and it shares search-v0.11's candidates only where it meets the same goal and
occurrence; its 561 fresh sets are new samples. So the pairing is not a joint run, though it compares like one where
the candidates are shared. The comparison is of the step prover at 48 expansions on one slice, with one set of draws
per task, at an equal number of expansions rather than equal computation; search-v0.13 adds two fresh sets of draws
for all three searches, and search-cost-v0.1 measures what each search costs. (search-v0.13 found that neither the
goal search's lead nor the group search's replicates on the two new sets.)
