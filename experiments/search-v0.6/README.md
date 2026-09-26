# Both searches with shared draws of a step-level prover (search v0.6)

search-v0.5 gave the AND-OR search its first lead over the whole-state search,
10 theorems against 8, with BFS-Prover-V2-7B as the proposer. But the proposer
samples, so the two searches drew different candidates on the same goals, and
two discordant theorems could not separate the design from the draw. This
experiment runs the same searches with the same proposer on all 200 tasks of
the holdout slice, with the draws shared between the two searches of a task.

## Shared draws

The two searches of a task share their draws, the standard way to compare two
systems under the same randomness (common random numbers): the n-th time a
search expands a goal, it gets the n-th set of candidates drawn for that goal
in this task, whichever search drew it first (`scripts/common_draws.py`). Both
searches therefore see identical candidates the first time each meets a goal.
The AND-OR search expands a goal once and only ever uses the first set; the
whole-state search draws afresh each time it expands a goal again, as a state
search with a sampled proposer does. Goals are identified by `canonical_goal`,
the identity the searches themselves use.

## Artifacts

- `preregistration.json`: the two task sets (the 140 tasks no model search had
  run, which carry the registered test and ran first, and the 60 search-v0.5
  ran), the proposer, the shared draws, the order of the two searches
  (alternating from task to task), hypotheses H50 to H53, and check C7;
- `results.jsonl`: per (task, search), the search with each expansion's three
  goal keys and the counts of drawn and shared expansions;
  `draws.jsonl.gz`: all 6,221 draws, with prompt, replies, candidates,
  occurrence, and the search that made them;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_paired.py --check-committed
```

recomputes every count, test, and fraction from the committed rows and draws;
CI runs it.

## Outcome

122 of the 140 test tasks and 47 of the 60 replication tasks could be stated;
no search was abandoned or errored. C7 holds: no goal was drawn twice for the
same occurrence within a task.

| Set | Whole-state | AND-OR | Whole only | AND-OR only |
| --- | ---: | ---: | ---: | ---: |
| test (122 stated) | 30 | 32 | 0 | 2 |
| replication (47 stated) | 9 | 9 | 0 | 0 |

**H50 is not supported**: on the test set the AND-OR search proves 32 theorems
against 30, both discordant ones in its favour, one-sided p = 0.25. **H51 is
not supported**: of the 30 theorems both prove, 10 took the two searches
different numbers of expansions, and the AND-OR search needed fewer in 6
(p = 0.38). **H53 holds** trivially: on the replication set the two searches
prove the same 9 theorems.

The replication set is the telling one. There, search-v0.5 had the AND-OR
search ahead by 10 to 8, with two theorems it alone proved. Under shared draws
neither search proves either of those two, and the two searches prove exactly
the same theorems. search-v0.5's lead came from the draw.

**H52 holds**: 5 of the 4,751 whole-state expansions are order duplicates
(0.1%). Goal duplicates are 4.9% of the expansions under the default key
(95% interval 3.4 to 6.6) but 26.1% under the coarse key (22.3 to 29.6). With
the step-level prover, four fifths of the goal sharing is between goals that
differ only in the names of their hypotheses, which this AND-OR search, keyed
like the others on printed text, cannot merge.

About a third of all expansions used candidates the other search had already
drawn. On the 60 tasks both experiments ran, a search took a median of two
thirds of the time it took in search-v0.5, with the same number of expansions.

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48
expansions, on the theorems of one Mathlib slice. Shared draws remove the draw
from the comparison of the two searches on the goals both meet; they do not
make the proposer deterministic, so a rerun draws anew. The AND-OR search
identifies goals by their printed text; a goal search that identified goals up
to renaming would have more to merge, and it would have to rename the
hypotheses its tactics mention.
