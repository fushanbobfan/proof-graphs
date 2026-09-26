# A second, disjoint Mathlib slice (holdout v0.1)

Every Lean search task of this program came from one Mathlib slice, every 50th
module in name order starting at the first, and that slice's counts were
themselves an experiment. This one takes every 50th module starting at the
26th, so no module is in both, extracts and counts it under the corrected step
derivation, and registers again, verbatim, the hypotheses the first slice and
search-v0.3 decided. Nothing here had been extracted or searched before.

## Artifacts

- `preregistration.json`: the module rule and list, the derivation, the search
  tasks' rule, and hypotheses H34 to H39 (H13, H12, and search-v0.3's H22 to
  H24, restated on this slice);
- `extraction.jsonl.gz`, `failures.json`, `counts.jsonl`: the extraction and
  the per-proof counts; `tasks.json`: the 200 drawn search tasks;
- `searches.jsonl`: per (task, search), the search with each expansion's three
  goal keys; `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_holdout.py --check-committed
```

recomputes the counts from the committed extraction, the tasks from the counts,
and the summary from both; CI runs it.

## Outcome

Of the 157 modules, 2 fail to elaborate and 142 contain tactic proofs, 2,244
proofs in all. 169 of the 200 drawn tasks could be stated in their original
context; no search was abandoned or errored.

| Hypothesis | Result |
| --- | --- |
| H34 median orderings at least 10 in every tested stratum | **fails** (8 at 6 to 10 steps) |
| H35 median index within 0.1 of the library's | holds |
| H36 median index within 0.1 of the first slice's | holds |
| H37 order duplicates below 5% | holds (4.6%, 95% interval 3.4 to 5.7) |
| H38 goal duplicates at least twice order duplicates | holds (14.2%, 3.1 times) |
| H39 AND-OR proves at least as many | **fails** by one theorem (10 against 11) |

The counts grow as on the first slice: medians of 8, 1,540, 1.4·10^11, and
4.4·10^40 by step stratum, with the median structure index within 0.1 of both
references everywhere it is tested. What does not replicate is a threshold:
the first slice's median at 6 to 10 steps was exactly 10, the registered bound,
and here it is 8. The growth replicates; the bound was met by a margin of
nothing.

The search measures replicate closely. Order duplicates are 4.6% of the 2,413
whole-state expansions against search-v0.3's 4.5%, goal duplicates 14.2%
against 14.9%. Under the fine key goal duplicates are 14.1%, and under the
coarse key 28.9% — search-v0.4 measured 28.0% on the first slice, so the
finding that most unseen sharing is between goals alike up to the names of
their hypotheses holds on data it was not found on. H39 fails exactly as H24
did, by one theorem out of the one task proved by exactly one search, which no
test can separate from chance.

## Interpretation boundary

The slice samples modules, not proofs, so the proofs of one module share an
author and a subject, and the two slices are drawn from the same Mathlib
revision. The searches use the menu proposer at 24 expansions, which
search-v0.4 shows proves what it proves in one step with a one-shot prover;
search-v0.5 runs a step-level prover on these same tasks.
