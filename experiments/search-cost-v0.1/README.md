# Search cost v0.1

The held-out comparisons (search-v0.11 to v0.13) give every search the same 48 expansions. This experiment measures
what each of the three searches (search-v0.10's whole-state, goal and group searches; the typed key, breadth-first,
48 expansions, each through `search_typed_v2`) costs when it runs alone and pays for its own draws, on a seeded
sample of 30 of search-v0.12's 591 held-out tasks. The searches run one at a time, in an order that rotates with the
task's index, each in its own Python process with a fresh REPL, and the model server serves no one else. Each search
draws its own candidates as search-v0.11 draws them, none shared with another search. For every search the runner
records the model's draw requests (16 completions each), their prompt and generated tokens and the time spent
drawing; the REPL's cost summary of candidate tactic calls, identity exports, and setup and verification commands,
each with its time; the largest resident memory of the search's process and its descendants, polled every 0.5 s;
and the elapsed time. H122 predicts that in each search the model's time is the largest recorded component of
elapsed time in more than half of the tasks; H123 that the median over tasks of the group search's elapsed time
divided by the whole-state search's lies between 0.8 and 1.25; H124 that in the goal and group searches the exports
that decide identity take less than a fifth of the elapsed time in the median task. Medians carry percentile
bootstrap intervals over tasks, which do not decide.

## Artifacts

- `preregistration.json`, `tasks.json`: the 30 tasks (`random.Random(20261015)`), the searches, the measures,
  hypotheses H122 to H124 and checks C53 and C54, registered on 2026-10-13 before any search ran;
- `results.jsonl`: one row per task and search, with the model's and the REPL's costs, the peak memory and the
  search's record;
- `summary.json`, `report.md`: the summary, by this experiment's own code.

## Reproduction

```text
python scripts/test_search_cost.py
python scripts/run_search_cost.py --check-committed
```

test the accounting, the rotation, the memory poll and the summary without Lean, and recompute the summary from the
committed rows; CI runs both.

## Outcome

All 90 searches ran to an outcome, and none raised or was abandoned (C53 holds); no other search experiment's
runner ran during any of them (C54 holds). The run took from 2026-10-17 15:34 to 21:50 without a pause.

| Search | Proved | Empty frontier | Expansions | Elapsed, all tasks | Model | Tactics | Exports | Commands | Model largest |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| whole states | 8 | 9 | 716 | 6,310 s | 63% | 10% | 3% | 16% | 16 of 30 |
| independent goals | 9 | 4 | 874 | 8,012 s | 66% | 8% | 4% | 13% | 20 of 30 |
| coupled groups | 5 | 7 | 929 | 8,106 s | 66% | 12% | 3% | 12% | 21 of 30 |

Shares are of each search's total elapsed time; "model largest" counts the tasks in which the model's time is the
largest component. Per task:

| Pair | Median ratio of elapsed time | 95% interval | Slower on |
| --- | ---: | --- | ---: |
| goals over whole states | 1.10 | 1.07 to 1.16 | 23 of 30 |
| groups over whole states | 1.21 | 1.12 to 1.50 | 24 of 30 |

- **H122 holds**: the model's time is the largest component in 16, 20 and 21 of the 30 tasks, in the whole-state
  search by one task.
- **H123 holds**: the median ratio is 1.21, inside 0.8 to 1.25; its interval reaches 1.50.
- **H124 holds**: identity exports take a median 1.2% of the goal search's elapsed time and 1.1% of the group
  search's.

The searches differ in how often they stop before their budget: the whole-state search did on 17 tasks (8 proofs, 9
empty frontiers), the goal search on 13 and the group search on 12. On the 11 tasks where both the goal and the
whole-state search used all 48 expansions, the goal search took a median 1.11 times as long, its model time 1.11
times, at about the same tokens per request; on the 12 such tasks for the group search, 1.15 times. A request of 16
completions took 5.6, 6.1 and 5.8 s on average, and the setup and verification commands about 33 s per search.
Elapsed times fall into a quick group (at most 122 s), every search in which ended before its budget, and a slow one
(at least 166 s), in which 48 of 50 searches used all 48 expansions. The whole-state search has 15
quick tasks, the goal search 13 and the group search 12, so the whole-state search's median falls between the groups
(129 s) and the others' inside the slow one (238 and 253 s); the per-task ratios compare the searches better than
these medians. The peak memory was a median of 3.9, 4.1 and 4.0 GiB, and at most 9.7 GiB.

## Interpretation boundary

At 48 expansions the three searches prove the same share of the held-out tasks (search-v0.13). Run alone with their
own draws, the goal and group searches take a median 10% and 21% longer per task, longer on most tasks, and nearly
two thirds of every search's time is the model's; the exports that decide goal identity take about one percent.
Searching goals, then, buys no proofs and costs a little more time. The proof counts above come from one set of
unshared draws per search and do not compare the designs. The times are of one machine and one llama.cpp server;
with a faster model server the Lean side's share would grow.
