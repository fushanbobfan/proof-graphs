# Golf pairs from v4.26.0 to v4.29.0 (golf v0.2)

[recount-v0.1](../recount-v0.1/README.md) found, under the corrected step
derivation, that a golfed proof branches more than its predecessor once length
is accounted for (H28r), where the registered test of
[golf-structure-v0.1](../golf-structure-v0.1/README.md) had not established it.
H28r was registered knowing that result, so it is a re-evaluation, not a test.
This experiment mines the golf commits of the three releases before golf-v0.1's
window, keeps the pairs whose golfed text is still verbatim at v4.32.0,
elaborates both sides there exactly as golf-v0.1 does, counts under the
corrected derivation, and tests the branching difference in the direction seen,
with golf-v0.1's own tests alongside on pairs neither experiment has seen.

## Artifacts

- `preregistration.json`, `pairs.jsonl.gz`: the mining rule and totals, the
  elaboration, the adjustment, and hypotheses H40 to H44; `amendment-1.json`:
  the committed-results check compares floats within 1e-9 (made before any pair
  was elaborated, after recount-v0.1's identical check failed on Linux);
- `results.jsonl`: per pair, both sides' steps, orderings, structure index,
  depth, width, and branching;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_golf_replication.py --check-committed
```

recomputes the per-pair results from the committed extraction and the summary
from the results; CI runs it.

## Outcome

511 pairs from 89 commits, none overlapping golf-v0.1's; 479 elaborate on both
sides, from 84 commits; 261 have at least 3 steps on both sides. The median
proof goes from 8 steps to 4.

| Hypothesis | Result | golf-v0.1 |
| --- | --- | --- |
| H41 golfed has fewer steps | **holds**, 356 of 409, p = 1.6e-56 | holds (H20) |
| H40 golfed branches more, adjusted | **holds**, 137 of 198, p = 3.4e-8 | H28r, supported |
| H42 golfed has the lower structure index | **fails**, 103 of 202, p = 0.42 | holds (H21), 87 of 125 |
| H43 adjusted structure index not different | **fails**, 84 of 224 lower, p = 0.00022 | held, 65 of 136, p = 0.73 |
| H44 some adjusted quantity differs (Holm) | **holds** | H28 failed, H28r held |

| Quantity | Adjusted: differing, golfed lower, Holm | Unadjusted: differing, golfed lower |
| --- | --- | --- |
| depth | 174, 108, 0.0036 | 182, 174 |
| width | 103, 38, 0.010 | 65, 57 |
| branching | 198, 61, 2.1e-7 | 197, 62 |

Two of golf-v0.1's findings replicate and two do not.

**Replicates.** Golfing shortens the proof's graph (H41), overwhelmingly. And,
adjusted for length, the golfed proof branches more (H40): 137 of the 198 pairs
whose adjusted branching differs, at p = 3.4e-8. The effect that only appeared
after the derivation was corrected is real on pairs chosen before it was
measured.

**Does not replicate.** The structure index does not separate the two proofs
here at all (H42: 103 of 202, p = 0.42), where golf-v0.1 found it lower in 87 of
125 at p = 7e-6. And the exploratory finding that length accounts for the
difference (H43) fails in the opposite direction: adjusted for length, the
golfed proof's index is *higher* in 140 of the 224 pairs where it differs
(p = 0.0002). Together with the three quantities, the picture is consistent:
adjusted for length, golfed proofs are shallower, wider, and branch more —
flatter graphs whose steps depend on each other less, which is what a higher
index at the same length means.

So the claim that survives both samples is that golfing shortens a proof and
makes its graph flatter. The claim that the structure index is lower, and that
its being lower is explained by length, holds on golf-v0.1's window and not on
this one.

## Interpretation boundary

The two windows differ in more than their dates. A pair enters only if its
golfed text is still verbatim at v4.32.0, and these commits are three releases
older, so 231 of the 1,329 changed declarations were dropped as changed since
the golf, against 76 of 416 in golf-v0.1: this sample is filtered toward
declarations nobody touched for longer. The adjustment uses one reference
slice, and the pairs of one commit are not independent.
