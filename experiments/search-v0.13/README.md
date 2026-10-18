# Search v0.13

search-v0.11 found the coupled-group search ahead of the whole-state search on 591 held-out theorems (7 tasks to 1,
one-sided p = 0.035), and search-v0.12 found the independent-goal search ahead by 8 to 1 (Holm-adjusted p = 0.039),
both with one set of draws and each significant by one theorem. This experiment runs the same three searches
(search-v0.10's whole-state, goal and group searches; the typed key, 48 expansions) on the same 591 tasks with two
new sets of draws. Within a unit (a task in one set) the three searches share one fresh candidate stream, keyed by
the goal's printed text, and run in an order that rotates with the task's index and the set; every task's first set
is queued before any second set. A search's score on a task is the number of the two new sets in which it proves the task
within 48 expansions. H115 predicts that the group search scores higher than the whole-state search on significantly
more tasks than the reverse; H116 that the upper limit of the 95% interval for their difference in proof rate,
resampling modules, is below three points; H117 that the group search does not score higher than the goal search on
significantly more tasks, and H118 that the goal search scores higher than the whole-state search on significantly
more, both with Holm's procedure over the two. A simulation from search-v0.10's per-task outcomes, for information
only, gave the H115 sign test a power of 98% at a median difference of 1.35 points.

## Artifacts

- `preregistration.json`, `tasks.json`: the tasks (search-v0.12's), the searches, sets, attempt rule, hypotheses H115
  to H118, checks C48 to C50 and the simulation, registered on 2026-10-13 before any unit ran;
- `results.jsonl`: one row per search, set and attempt, the latest counting;
- `draws.jsonl.gz`: the 42,668 candidate sets drawn;
- `summary.json`, `report.md`: the summary, by this experiment's own code;
- `../search-v0.13-pooled/summary.json`: the descriptive pooling with search-v0.11's set that the registration names
  (`scripts/explore_pooled_v013.py`);
- `../search-v0.13-abandoned/summary.json`: the comparisons with whole states under other treatments of the abandoned
  searches (`scripts/explore_abandoned_v013.py`, not registered).

## Reproduction

```text
python scripts/test_search_replicates_holdout.py
python scripts/run_search_replicates_holdout.py --check-committed
python scripts/explore_pooled_v013.py --check
python scripts/explore_abandoned_v013.py --check
```

test the rotation, the attempt rule and the summary without Lean, recompute the summary from the committed rows, and
recompute the pooled description and the sensitivity analysis; CI runs all four.

## Outcome

All 591 tasks were posed in all six searches. Every unit is final and no latest row records an error (C48 holds);
none of 301,445 typed exports failed (C49 holds); no candidate set was drawn twice for the same goal and occurrence
in a unit, and the 855 sets taken as seeded were drawn by an earlier attempt of the same unit (C50 holds). 19 units
were repeated under the registered attempt rule: four after their unit process failed and 15 after a search was
abandoned by a REPL timeout. 25 searches, in 13 units of 11 tasks, are abandoned in the latest rows and count as
unproved, as registered.

Proved within 48 expansions:

| Search | Set 1 | Set 2 | search-v0.11's set |
| --- | ---: | ---: | ---: |
| whole states | 143 | 143 | 147 |
| independent goals | 140 | 146 | 154 (search-v0.12) |
| coupled groups | 140 | 145 | 153 |

Over the two new sets, counting the tasks whose scores differ:

| Pair | First more | Second more | Difference | Modules 95% | One-sided sign test |
| --- | ---: | ---: | ---: | --- | ---: |
| groups over whole states | 8 | 11 | -0.1 pt | -0.8 to +0.6 | 0.82 |
| groups over goals | 2 | 2 | -0.1 pt | -0.6 to +0.3 | 0.69 (Holm 1.0) |
| goals over whole states | 8 | 9 | 0.0 pt | -0.7 to +0.7 | 0.69 (Holm 1.0) |

- **H115 fails**: the group search does not score higher than the whole-state search on significantly more tasks.
- **H116 holds**: the upper limit of the interval is +0.6 points, below three.
- **H117 holds**: the group search does not score higher than the goal search on significantly more tasks.
- **H118 fails**: the goal search does not score higher than the whole-state search on significantly more tasks.

Pooled with search-v0.11's set, as the registration allows descriptively: groups over whole states 12 tasks to 11
(+0.3 points, -0.3 to +0.9 resampling modules), goals over whole states 12 to 9 (+0.4, -0.2 to +1.0), and groups over
goals 2 to 2 (-0.1, -0.6 to +0.2). Goal duplicates are 4.7% of the whole-state search's expansions and order
duplicates 0.11%; the group search made 3,383 groups of several goals, and 2 of its proofs passed through one.

The 25 abandoned searches count as unproved, as registered. Counted as proved for the goal or the group search alone,
the case most favourable to it, they would give goals over whole states +0.51 points (-0.34 to +1.34) and groups
over whole states +0.76 (-0.15 to +1.85); leaving out their 11 tasks gives 0.00 (-0.73 to +0.76) and -0.09 (-0.77 to
+0.67). This sensitivity analysis is not registered (`../search-v0.13-abandoned/summary.json`,
`scripts/explore_abandoned_v013.py`).

The run took from 2026-10-13 18:13 to 2026-10-17 15:31. Its supervisor stopped the runner, with the units in flight,
three times when the commit charge left fell below 8 GB (five minutes each), three times for a game (Hearthstone for
44 minutes; DOAX Venus Vacation for 2 h 48 min, until Bob exempted it as an idle game; another game for 64 minutes),
and once a Windows Update restart at 06:44 on 10-14 stopped everything until a new supervisor took over at 12:10.
Units in flight leave no rows, except three whose processes the restart killed while the runner still lived: they
recorded error rows (exit codes 0x40010004 and 0xC0000142) and were repeated. The fourth failure was a
`RecursionError` in a unit process for `Equiv.Perm.Basis.toCentralizer_equivariant` in set 1, whose repeat, with
fresh draws, finished.

## Interpretation boundary

The leads search-v0.11 and v0.12 found on one set of draws do not replicate on two new ones: over the new sets the
goal search and the whole-state search prove the same share of the tasks, and the group search no more. The new sets
also show how much a set alone moves the counts (the goal search proves 140 tasks in one and 146 in the other), and
the earlier significance rested on one theorem in each experiment. Pooled over all three sets, searching goals or
coupled groups moves the proof rate by less than one point from that of whole states, with intervals that include
zero, and coupled groups add nothing to independent goals. The upper limits rest on counting abandoned searches as
unproved; the case most favourable to a goal-level search raises them to about 1.3 and 1.9 points, still below three.
The comparison is of the step prover at 48 expansions on one slice, with the number of expansions held equal;
search-cost-v0.1 measures what each search costs.
