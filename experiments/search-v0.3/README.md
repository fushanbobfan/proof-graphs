# Menu searches on every candidate theorem (search v0.3)

search-v0.1 measured order duplicates, goal sharing, and the two search
designs on 47 theorems, every 29th of the 1,347 candidates of the Mathlib
slice. Are its numbers properties of that sample or of the population? This
experiment runs the deterministic menu arm of both searches, unchanged, on all
1,347, at the same budget of 24 expansions. The tasks of search-v0.1 are part
of this corpus, so their searches must reproduce the committed ones exactly
(C2).

## Artifacts

- `preregistration.json`: the corpus rule and hashes, the searches, the budget,
  the measures, hypotheses H22 to H25, check C2, and the two registered
  correlation analyses; `amendment-1.json`: the runner records a unit's
  exception as an error row instead of letting it stop the recording (the
  original loop recorded nothing after the first exception; 1,984 rows and the
  progress log had been seen, no summary);
- `results.jsonl`: per (task, search), the search's expansions and proof;
- `summary.json`, `report.md`; `sensitivity.json`: an unregistered rerun of the
  one error unit, described below.

## Reproduction

```text
python scripts/run_search_wide.py --check-committed
```

recomputes every measure and decision from the committed rows, and replays four
expansions of the first task in a fresh REPL; CI runs it.

## Outcome

1,171 of the 1,347 theorems could be stated in their original context. No unit
was abandoned on a REPL timeout; one AND-OR unit raised an exception and is
recorded as an error row.

| Search | Expansions | Order duplicates | Goal duplicates | Proved | Entangled |
| --- | ---: | ---: | ---: | ---: | ---: |
| whole-state | 16,095 | 728 (4.5%) | 2,400 (14.9%) | 103 | |
| AND-OR | 15,875 | | | 102 | 2,609 (4.1%) |

The sample's findings hold on the population. **H22 holds**: order duplicates
are 4.5% of the whole-state expansions, below the registered 5%. **H23 holds**:
goal duplicates are 3.3 times them. **H24 is not supported**, by one theorem:
the AND-OR search proves 102 against 103. Three theorems are proved only by the
whole-state search and two only by the AND-OR search, and a two-sided sign test
on those five gives p = 1, so the experiment shows no difference between the
designs rather than a deficit. **H25 is not supported**: only one of the three
whole-only theorems had a candidate discarded as entangled, so entanglement is
not the general explanation of the whole-state search's wins, although it is
the explanation of the one case examined in search-v0.1.

Neither registered correlation is there: over the 1,171 stated tasks, the
number of order duplicates has Spearman rho = -0.005 (p = 0.86) against the
log of the original proof's number of orderings, and goal duplicates rho =
0.052 (p = 0.08). How much order redundancy a proof's graph admits does not
predict how much of it the search meets. 586 whole-state searches exhausted
their frontier before their budget.

C2 holds: all 80 searches of search-v0.1's tasks reproduce the committed
expansion records and proofs exactly.

### The error unit, and a sensitivity analysis

In `FirstOrder.Language.BoundedFormula.realize_ex` the AND-OR search recorded a
goal as its own proof — a later candidate of the same expansion returned a goal
whose canonical text equalled the goal being expanded, and overwrote the proof
already recorded for it — so building the proof script did not terminate. The
registered summary counts that unit as not proved. `scripts/search_keys.py`
sets a goal's proof once and never overwrites it; `scripts/search_v03_sensitivity.py`
reruns the unit with that search and recomputes the counts. It proves the
theorem in five expansions, which makes the two searches 103 and 103. This
analysis is not registered and does not replace the summary; both numbers are
reported.

## Interpretation boundary

Breadth-first search with the 26-tactic menu at 24 expansions, on every
candidate theorem of one Mathlib slice. The measures describe where such a
search spends its expansions, not the best achievable prover. Goals are
compared by their printed text with metavariable numbers erased
(search-v0.4 measures what that choice costs).
