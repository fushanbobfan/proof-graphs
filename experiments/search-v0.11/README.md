# Search v0.11

Every step-prover comparison before this one ran on the same 200 tasks of the second Mathlib slice, and none found a
significant difference between searching whole states and searching goals or goal groups after adjustment; on
search-v0.10's 169 posable tasks the group search led the whole-state search by about one point. This experiment is
the confirmation search-v0.10 deferred to: it runs search-v0.10's whole-state and coupled-group searches, unchanged and
with the typed key throughout, on 720 tasks no search had used, positions 200 to 919 of holdout-v0.1's seeded order
of the slice's candidates. Each task's two searches run in fresh REPLs at 48 expansions and share one set of fresh
draws. A search whose REPL session is lost is abandoned where the loss happens (`search_typed_v2`), the defect behind
search-v0.10's amendment 1. The number of tasks was fixed at registration by a stated rule: the smallest of 480, 560,
640 and 720 for which, simulating from search-v0.10's paired outcomes as run, the upper limit of the 95% interval falls
below three points in at least 80% of 4,000 runs. That was 720 (83.9%; the sign test's simulated power was 58%). The
simulation took 84.5% of the tasks drawn as posable (search-v0.9's share) and drew each task's paired outcome
independently, so it modelled neither the variation of that share nor the clustering of tasks by module. The size
serves H110, the question the registration names; H109 and H111 are decided beside it, each at 0.05, with no
adjustment across the three.

Identity decisions (the whole-state search's drops, the group search's merges and partition) use the typed key. The
candidate stream does not: as in search-v0.6 to v0.10, the nth time a search of a task expands a goal it receives the
nth candidate set drawn for that goal, keyed by the goal's printed text without its case tag and with metavariable
numbers erased, the same key for both searches.

## Artifacts

- `preregistration.json`, `tasks.json`: the rule, the sample-size simulation and its result, the 720 tasks, the
  searches, the budget, hypotheses H109 to H111 and checks C43 and C44, registered on 2026-10-10 before any unit ran;
- `results.jsonl`: one row per search and attempt, the latest row of each search counting;
- `draws.jsonl.gz`: the 21,486 draws, each shared by a task's two searches;
- `summary.json`, `report.md`: the summary, by search-v0.11's own code.

## Reproduction

```text
python scripts/run_search_confirm.py --check-committed
python scripts/explore_readings_v011.py --check
```

recompute the summary from the committed rows, and the exploratory readings below (`../search-v0.11-readings`); CI
runs both.

## Outcome

591 of the 720 tasks were stated in both searches (82%; the rule assumed 84.5%). C43 holds: every unit is final and
no row records an error. Through the attempts:

| Course of a task's unit | Tasks |
| --- | ---: |
| both searches posed in the first attempt, none abandoned | 579 |
| a search abandoned in the first attempt; both complete in the repeat | 10 |
| both searches abandoned in both attempts (count as unproved, as registered) | 2 |
| statement not posed, in both searches and both attempts | 108 |
| "declaration range not found", in both searches and both attempts | 21 |

The 129 tasks that could not be posed failed the same way in every search and attempt, so their exclusion is a
property of the task under this harness, unlike search-v0.8's range failures. 21 searches were abandoned over all
attempts, and 4 in the latest rows: both searches of `Equiv.Perm.card_isConj_mul_eq` and of
`ValueDistribution.proximity_sum_top_le`. No search went on after a REPL restart. Within 48 expansions the
group search proves 153 tasks and the whole-state search 147 (140 and 133 within 24); both prove 146, only the group
search 7, only the whole-state search 1.

- **H109 fails**: the group search proves significantly more tasks (one-sided sign test on the 8 tasks one search
  alone proves, p = 0.035).
- **H110 holds**: the difference is +1.0 point, and the upper limit of its 95% Newcombe interval, 2.0 points, is below
  the three-point margin (interval +0.04 to +2.0; resampling modules +0.2 to +1.9, which does not decide).
- **H111 holds**: under the typed key goal duplicates are 4.4% of the whole-state search's expansions (order
  duplicates 0.12%).

C44 holds: 2 of 102,870 typed exports failed. The run paused once, for 98 minutes while the machine was in other use;
the supervisor stopped the runner with its unit processes, and the units in flight, of which no row had been written,
ran again from the start.

## Readings (exploratory)

`scripts/explore_readings_v011.py` recomputes the paired outcome under other readings of the attempts. The decision
rests on one task. `DFinsupp.prod_mapRange_index` is one of the seven tasks only the group search proves, and it was
decided in a repeat: in its first attempt the group search was abandoned and the whole-state search failed; the repeat,
which runs both searches again with fresh shared draws as registered, proved it by the group search only. On first
attempts alone the counts are 6 against 1 (p = 0.0625). The two tasks abandoned in the latest rows lost both searches
in both attempts, so any reading that gives a task's two searches the same outcome leaves 7 against 1; counting only
their whole-state searches as proved gives 7 against 3 (p = 0.17), and only their group searches 9 against 1
(p = 0.011). In every reading the difference favours the group search (+0.7 to +1.4 points) and the interval's upper
limit stays below three points (at most 2.5). The 591 stated tasks come from 104 modules, and the eight tasks one
search alone proves from eight different modules, so a sign test over modules gives the same 7 against 1. The group
search made 1,776 groups of several goals, and one of its proofs passed through one; it is not among the seven, whose
proofs keep every goal in a group of its own.

## Interpretation boundary

On held-out theorems the coupled-group search proves slightly more than the whole-state search with the same draws:
about one theorem in a hundred, with a gain of three points excluded in every reading. The registered sign test is
significant at 0.05, but by one task, so the direction is better supported than its significance: it matches
search-v0.10's estimate on other theorems (+1.4 points at 48 expansions over three sets). No proof that decides the
comparison passes through a group of several goals. That shows what the winning proofs used, not why the group search
found them: coupled groups that fail can still change what a search expands and when, and an independent-goal arm on
the same tasks and candidates would be needed to separate coupling from searching goals. (search-v0.12 ran it: the
goal search proves every theorem the group search proves and one more.) The gain is in theorems proved
at an equal number of expansions, not an end-to-end speedup, since the two searches apply different numbers of
candidates per expansion. The tasks are held out from this program's earlier searches, not from its counts
(holdout-v0.1 counted all of their proofs, orderings-replay-v0.2 replayed 32 and extraction-audit-v0.3 reconstructed
4), from the prover's training data, or from the slice's modules, and the comparison is of the step prover at 48 expansions on one slice of
Mathlib, with one set of draws per task.
