# Whole states and coupled goal groups with 256 expansions (search v0.9)

search-v0.8 compared a whole-state search, a search over independent goals, and a search over goals grouped by the
metavariables they share, each with 48 expansions, and no pair differed significantly. A review of the paper asked
for one stronger search point, so that the goal-sharing result is not confined to searches of that size. This
experiment runs two of search-v0.8's searches, unchanged, with 256 expansions each.

## Two searches

- `whole`: whole states, a child dropped when its faithful state key was generated before
  (`search_faithful.whole_state_search`);
- `groups`: goals grouped by the metavariables they share, a one-goal group merged by faithful goal key behind a
  renaming step (`search_faithful.coupled_search`).

The search over independent goals is left out: in search-v0.8 it proved the same theorems as the group search in
each set except one theorem in one set, and leaving it out saves a third of the REPL time.

## Draws and budget

The proposer is search-v0.5's to v0.8's: BFS-Prover-V2-7B in Q8_0, 16 completions at temperature 1.0, the first
goal followed by `:::`. A task's draws are shared by its two searches, the n-th expansion of a printed goal getting
the n-th set for it. They are seeded with search-v0.8's first set: the 7,731 sets of search-v0.6 and v0.7 that
seeded it, then its 402 new draws, 8,133 sets for 169 tasks. Both searches are breadth-first and the seeds cover
their first 48 expansions, so those expansions repeat search-v0.8's first set (C28), and one run gives the
measures at 48, 96, 192, and 256 expansions.

## Registration

`preregistration.json` was committed before the run (`04b5436`, 2026-10-03). It fixes the tasks, the searches,
the seeds by hash, the budget, the execution, and:

- **H87**: the group search proves more tasks than the whole-state search at 256 expansions (one-sided sign test
  at 0.05 on the tasks exactly one proves);
- **H88**: in the whole-state searches that run past 48 expansions, goal duplicates are a larger share of the
  expansions after the 48th than of the first 48 (95% interval of the difference above 0, resampling modules);
- **H89**: order duplicates stay under 1% of the whole-state search's expansions (upper end of the 95% interval);
- **C28** to **C31**: at least 98% of the searches repeat search-v0.8's first 48 expansions and proof; no goal
  occurrence is drawn twice or replaces a seed; at least 99% of the searches export through the defined tactic;
  at least 99% of the new draws have all 16 completions.

## Artifacts

- `preregistration.json`;
- `results.jsonl`: one row per task, search, and attempt (468), the latest attempt counting;
- `draws.jsonl.gz`: the 22,168 new draws of the final attempts;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_coupled_deep.py --check-committed
```

recomputes the summary from the committed rows and draws; CI runs it. `--run` resumes the run (the model server
on port 8091 and a Mathlib REPL per worker).

## The run

Memory decided the schedule. A REPL holds 4 to 7 GB and the server 11.4 GB, and on this machine other programs
held most of the commit charge, so the runner admits a unit only while 15 GB is left, and a supervisor stopped it
while less than 8 GB was left. Three such stops on 2026-10-03, the last when another program started, led to fewer workers
(three, two, one) until the paging file was enlarged at 17:31, raising the commit limit from 151 to 175 GB; three
workers ran from then on. From 17:26 the supervisor also stopped the runner and the server while the machine was in
other interactive use, four times, for minutes to 9 hours, and the run was stopped on 2026-10-06 at 08:42 while the machine was away, resuming
at 21:19 after a reboot. It ended on 2026-10-07 at 03:47. A unit in flight at a stop leaves no row and runs again
with fresh draws beyond the seeds, as registered; neither the stops nor the number of workers changes what a
unit computes. The server's flags were the same at every start.

Of the 200 tasks, 31 were constructed in neither search, as in search-v0.8, and ran twice by the registered rule;
169 were stated. Three tasks needed a second attempt: one unit raised a recursion error in Python after 46
minutes (`Ideal.exists_spanRank_eq_and_height_eq`) and one was abandoned by REPL timeouts in both searches
(`Algebra.FormallySmooth.adjoin_of_algebraicIndependent`); both completed on the second attempt. In
`DFinsupp.sumZeroHom_apply` the whole-state search was abandoned by a REPL timeout in both attempts and counts as
not proving the theorem; its group search ran all 256 expansions without a proof.

## Outcome

All four checks hold: 331 of 331 searches stated here and in search-v0.8's first set repeat its first 48
expansions exactly; no draw repeats or replaces a seed; all 337 searches exported through the defined tactic;
all 22,168 new draws have 16 completions.

| Theorems proved (of 169) | 48 | 96 | 192 | 256 |
| --- | ---: | ---: | ---: | ---: |
| whole states | 41 | 44 | 46 | 46 |
| coupled groups | 43 | 46 | 47 | 48 |

- **H87 not supported**: at 256 expansions the group search alone proves 3 theorems and the whole-state search
  alone 1 (one-sided p = 0.31; rate difference +1.2 points, 95% interval −1.1 to +3.7). The extra budget found
  five new proofs for each search, the deepest at expansion 174 (whole) and 217 (groups).
- **H88 not supported**: goal duplicates are 5.7% of the first 48 expansions and 5.9% of the later ones in the
  75 whole-state searches that ran past 48 (difference +0.2 points, −1.7 to +2.3); the share stays between 5.6%
  and 5.9% at every checkpoint. Once states are merged by Lean expressions, the goal sharing left does not grow
  with the budget here, unlike the menu searches of search-v0.2 under printed keys.
- **H89 supported**: order duplicates are 40 of 19,106 whole-state expansions (0.21%, 0.12 to 0.32%).

The group search made 2,705 groups of several goals, in 75 of its searches, and no proof passed through one;
three whole-state proofs used a goal's later draw.

At more than five times search-v0.8's budget the picture stands: removing goal sharing gains no established advantage, the
goal sharing a whole-state search meets stays near 6% of its expansions, and order duplicates stay near 0.2%.
