# A step-level Lean prover as the proposer (search v0.5)

Every search experiment before this one used a proposer too weak for the
question the program set out to answer. The menu proves what it proves with a
one-shot prover in one step, and without those provers it proves nothing
(search-v0.4), so a search over goals never had room to win. This experiment
replaces the proposer with BFS-Prover-V2-7B, a model trained to emit one Lean
tactic for one tactic state, and runs both searches at 48 expansions on 60
tasks of the holdout slice, where holdout-v0.1 has already run the menu at 24.

## Artifacts

- `preregistration.json`: the tasks (the first 60 of holdout-v0.1's seeded
  random draw), the proposer (the model, its Q8_0 quantization, the prompt, 16
  completions at temperature 1.0), the searches, the budget, hypotheses H45 to
  H49, and a full account of what was run and seen before it: two earlier
  launches, stopped for throughput, whose twelve units and model calls were
  deleted, and the menu baseline on these tasks;
- `results.jsonl`: per (task, search), the search with each expansion's three
  goal keys; `model-calls.jsonl.gz`: all 45,680 prompts and replies;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_prover.py --check-committed
```

recomputes every fraction and decision from the committed rows and
holdout-v0.1's committed baseline; CI runs it. Rerunning the searches needs the
model (`D:\ucla\agent-harness\scripts\start-llama-server.ps1 -Profile bfsprover`
on the author's machine) and gives different candidates, since it samples.

## Outcome

47 of the 60 tasks could be stated; one task was abandoned on a REPL timeout
under both searches. A search took a median of 23 minutes, against 33 seconds
for the menu's searches on the holdout slice.

| Search | Proved at 24 | Proved at 48 |
| --- | ---: | ---: |
| menu, whole-state (holdout-v0.1) | 3 | |
| model, whole-state | 7 | 8 |
| model, AND-OR | 9 | 10 |

| Key | Order duplicates | Goal duplicates (95% interval) |
| --- | ---: | --- |
| fine | 0.0% | 5.9% |
| default | 0 of 1,457 | 6.4% (3.0 to 9.9) |
| coarse | 0.1% | 20.6% (15.0 to 25.9) |

**H45 is not supported**: at 24 expansions the model proves 7 theorems against
the menu's 3 on the same tasks, 5 proved only by the model and 1 only by the
menu, but a one-sided sign test on those six gives p = 0.11. The direction is
the one expected; six discordant tasks cannot establish it.

**H46 holds**, and for the first time in this program the AND-OR search proves
more than the whole-state search: 10 against 8, with 2 theorems proved only by
the AND-OR search and none only by the whole-state search (two-sided p = 0.5).
One of the two is the deepest proof any search here has found: in
`MultilinearMap.map_update_sum` the AND-OR search reached, at its 28th
expansion, an eight-step proof that runs an induction and closes the two goals
it creates separately. The other, `map_add_sub_map_add_sub_linearDeriv`, took
it three expansions, while the whole-state search spent all 48 without finding
the `simp_rw` step it opened with. The model samples at temperature 1.0, so the
two searches draw different candidates even on the same first goal, and two
discordant theorems cannot separate the design from the draw.

**H49 holds**: two proofs were found after expansion 24 (the one above at 28,
and `Real.fibRec_charPoly_eq` by the whole-state search at 45). This is the
first experiment in which a search ran deep and the depth paid.

**H47 and H48 hold**, in a way worth stating: across 1,457 whole-state
expansions not one state was an order duplicate. The menu's order duplicates
came from moves such as `symm` before `constructor` that reverse the goals of an
iff; the model does not make them. Goal duplicates fall to 6.4%, from 14 to 16%
with the menu, and to 20.6% under the coarse key, from 28 to 29%. A proposer
that proposes targeted tactics meets even less of the order redundancy that
proof nets remove, and less goal sharing too, but most of what it does meet is
still hidden by hypothesis names.

## Interpretation boundary

One quantized open-weights prover at one sampling setting, on 47 theorems of
one Mathlib slice, at a budget far below what such provers are run at. The
model is shown the first goal only, in both searches, so that the two see the
same context; the model was trained on single tactic states. Its sampling makes
every search a draw: the proof counts here would move on a rerun, and the
differences between searches and against the menu are within what a rerun could
change.
