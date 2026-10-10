# Search v0.10

search-v0.8 compared a whole-state search, a search over independent goals, and a search over goals coupled by
metavariables, each with 48 expansions in three sets of draws, and search-v0.9 ran the first and third with 256
expansions in the first set. Both identified goals by the expression key of `goal_identity`, whose known defects the
typed key of `goal_identity_typed` corrects. This experiment reruns both with every identity decision made by the
typed key (`search_typed`), each set seeded with the candidate sets recorded for it before, so that where the two keys
decide alike the searches repeat the earlier ones. It is a correction and sensitivity study of search-v0.8 and v0.9,
whose results were known when it was registered, not a fresh confirmation; search-v0.11 is that confirmation.

## Artifacts

- `preregistration.json`: the tasks, the seeds, the searches and budgets, hypotheses H103 to H106 and checks C40 and
  C41, registered before any unit ran;
- `results.jsonl`: one row per search and attempt, the latest row of each search counting; the rows marked
  `"amendment": 1` are amendment 1's repetitions;
- `draws.jsonl.gz`, `amendment-1-draws.jsonl.gz`: the new draws (the amendment needed none);
- `summary.json`, `report.md`: the summary, by search-v0.10's own code; `summary-as-run.json`: the summary before
  amendment 1;
- `amendment-1.json`: the amendment, written before its rerun.

## Reproduction

```text
python scripts/run_search_typed.py --check-committed
python scripts/search_v010_amendment.py --check
python scripts/explore_lost_sessions_v010.py --check
```

recompute the summary from the committed rows, verify the amendment and the summary as run, and recompute the
sensitivity analysis that triggered it; CI runs all three.

## Outcome

169 of the 200 tasks were stated in all nine searches (C40 holds: every unit final, no error; 43 counted searches,
15 whole-state, 12 goal, 16 group, were abandoned on REPL timeouts and count as unproved, as registered). Within 48
expansions, over the three sets of draws (507 task-sets), the whole-state search proves 123, the goal search 129, and
the group search 130.

- **H103 holds**: no comparison is significant after Holm's adjustment. The group search proves more than the
  whole-state search on 8 tasks and fewer on 1 (one-sided p = 0.020, Holm-adjusted 0.059), the goal search on 8 and 2
  (p = 0.055, adjusted 0.11), and the group search than the goal search on 1 and 0 (p = 0.5). The rate differences
  are +1.4 points for groups over whole states (95% interval resampling modules +0.5 to +2.5), +1.2 for goals over
  whole states (+0.2 to +2.3), and +0.2 for groups over goals (0.0 to +0.7).
- **H104 holds**: at 256 expansions in the first set the group search proves 48 and the whole-state search 46, 3
  against 1 (one-sided p = 0.31; difference +1.2 points, interval -0.7 to +3.7).
- **H105 holds**: where both keys exported, they agree on 99.78% of the whole-state searches' 79,719 decisions whether
  a generated state had been generated before (the typed key alone says so 16 times, the expression key alone 157),
  and on 99.66% of the goal and group searches' 124,803 merge decisions.
- **H106 holds**: in every set and at both budgets, each search proves exactly the tasks it proved with the expression
  key (over the tasks stated in both experiments).

C41 holds: none of 206,206 typed exports failed. Under the typed key, goal duplicates are 5.3% of the whole-state
search's first 48 expansions (5.5% under the expression key) and order duplicates 0.21%; at 256 expansions 5.5%
(5.9%). The group search made 3,282 groups of several goals and found one proof through one.

## Amendment 1

When a REPL request timed out inside an expression export or a verification, the harness started a new session and
the helper returned None or False, so the search went on in a session without the task's environment or its proof
states and ended unproved instead of abandoned (`search_typed_v2` explains the mechanism; search-v0.11 abandons such a
search). Four counted searches did so, all goal or group searches, each after one expression export failed. By a rule
fixed before the run ended (`scripts/explore_lost_sessions_v010.py`), every decision was recomputed with these four
counted as proved within 48 expansions; in that best case H103 fails (groups over whole states, one-sided p = 0.011,
Holm-adjusted 0.032), so their units were repeated once under the registered attempt rule with `search_typed_v2`
(`amendment-1.json`, written after the summary as run had been read and before the rerun). `PointedCone.DualFG.dual_of_fg`
is now proved by every search in sets 0 and 2; `MeasureTheory.borel_eq_borel_of_le` runs to the end without a proof;
in set 1 every search of `Algebra.FormallySmooth.adjoin_of_algebraicIndependent` is abandoned during setup, which is
final.

As run, before the amendment, every hypothesis also held: groups over whole states 8 against 2 tasks, p = 0.055, Holm
0.16; at 256 expansions 3 against 2, p = 0.5; and two searches proved less than with the expression key, the group
search of `PointedCone.DualFG.dual_of_fg` in set 0 (at both budgets) and its goal search in set 2, both through a lost
session, which the amendment's repetitions restore.

## Interpretation boundary

The typed key changes no search's outcome against the expression key, so search-v0.8's and v0.9's comparisons stand as
registered under the corrected identity. The estimates favour the goal-level searches by about one point at 48
expansions, with intervals that exclude zero when modules are resampled, while the registered sign tests, adjusted for
three comparisons, are not significant; on these 169 theorems the difference is about one theorem in a hundred, and
search-v0.11 tests it on 720 held-out ones. The draws are shared and seeded, so the sets are not independent samples
of the prover, and the 256-expansion comparison has one set.
