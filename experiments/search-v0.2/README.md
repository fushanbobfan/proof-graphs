# Search v0.2

The objection to [search-v0.1](../search-v0.1/README.md) is that 24
expansions are too few for redundancy to matter. This experiment reruns the
same searches, with the same proposers and verification, at 192 expansions
on the 20 tasks where v0.1's budget ran out. Both searches are breadth-first,
so one run gives the measures at 24, 48, 96, and 192 expansions.

## Artifacts

- `preregistration.json` and `tasks.json`: the task rule (the v0.1 tasks on
  which some search used all 24 expansions without a proof), the budget and
  checkpoints, the execution (a fresh REPL per task, arm, and search; four
  at a time; the model server with four slots), hypotheses H17 to H19, and
  check C1; committed on `main` before any run;
- `results.jsonl`: one row per task, arm, and search, with every expansion,
  the proof, and the counters;
- `model-calls.jsonl.gz`: the 19,128 prompts and replies of the model arm;
- `summary.json`, `report.md`: the measures at each checkpoint and the
  decisions.

## Reproduction

```text
lake exe cache get && lake build repl
python scripts/run_search_deep.py --check-committed
```

recomputes the summary from the committed rows and re-runs the first task's
menu whole-state search for four expansions; CI runs it. `--run` repeats the
experiment (6.7 hours here) and resumes from `results.jsonl`.

## Outcome

C1 holds: in all 40 menu searches, the first 24 expansions and the proof are
exactly those committed by search-v0.1, so the harness reproduces
bit for bit where the proposer is deterministic. All 80 searches were
stated; one model AND-OR search was abandoned on a REPL timeout.

| Arm | Budget | Whole-state expansions | Order duplicates | Goal duplicates | Proved: whole | Proved: AND-OR |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| menu | 24 | 343 | 3.8% | 12.2% | 1 | 0 |
| menu | 192 | 1,653 | 2.7% | 18.1% | 1 | 0 |
| model | 24 | 382 | 3.7% | 8.9% | 2 | 1 |
| model | 192 | 2,271 | 2.6% | 18.3% | 2 | 1 |

(48 and 96 lie between, monotonically; see `report.md`.)

- **H17 not supported**: goal sharing grows steadily with work, from 12.2% to
  18.1% in the menu arm and from 8.9% to 18.3% in the model arm. That is 2.06
  times in the model arm but only 1.48 times in the menu arm, and the
  hypothesis asked for two in both.
- **H18 not supported**: eight times the budget found no new proof in either
  arm or search. Every proof at 192 expansions was already found by expansion
  12. In 13 of the 20 menu tasks (7 of 20 model tasks) the frontier emptied
  before the budget did.
- **H19 supported**: order duplicates stay under 5% and fall with depth, from
  3.8% to 2.7% and from 3.7% to 2.6%.

Why the AND-OR search proves less: the whole-state search proves
`Set.iUnion_finset_eq_set` with `ext x; aesop; constructor; exact?`. Here
`constructor` on an `∃` goal leaves two goals, a membership `⟨x, ⋯⟩ ∈ ?w`
and the witness `?w : Finset ↑s`, and `exact?` on the first closes both at
once by assigning the witness. A search over independent goals must discard
exactly that candidate as entangled, 511 and 603 times in all at 192
expansions. In Lean, goals that share an existential witness are not
independent, and that is where the graph representation's independence
assumption fails. This is known: HyperTree Proof Search splits a tactic state
only into goals that share no metavariable, and Aesop copies the coupled
goals into the rule application that assigns the witness; both are designed
for exactly this case (neither was run here). What the experiment adds is how
often the assumption fails in a whole-state search on Mathlib theorems.

So deeper search makes goal sharing a larger share of the work, as the
AND-OR design expects, but at this proposer strength the work was never the
bottleneck: what a search can prove it proves early, and what it cannot, no
budget reaches.

## Interpretation boundary

Twenty tasks, all of them ones where v0.1's searches ran out, so the corpus
is selected for difficulty. Breadth-first search with a weak proposer. Every
search elaborated under Lean's default options rather than Mathlib's build
options, as in v0.1.
