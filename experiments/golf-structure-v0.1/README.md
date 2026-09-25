# Golf structure v0.1

[golf-v0.1](../golf-v0.1/README.md) found that the golfed proof's lower
structure index follows its shorter length. This experiment asks whether
three other quantities of the goal-origin graph separate golfed proofs from
their predecessors once length is accounted for: depth (the most steps on one
chain of dependencies), width (the most steps at one depth), and branching
(the mean number of dependent steps of a step that has any). Each quantity is
adjusted by subtracting the median of that quantity among the Mathlib slice's
proofs with the same number of steps (pooled from 30 steps on), the reference
of golf-v0.1's exploratory length adjustment.

## Artifacts

- `preregistration.json`: the pairs (golf-v0.1's, at least 3 steps on both
  sides), the quantities, the adjustment, the test (two-sided sign tests with
  Holm's correction over the three quantities), and hypothesis H28; committed
  before any of these quantities had been computed for a pair or a slice
  proof;
- `results.jsonl`: per pair, the three quantities and their adjusted values on
  both sides;
- `summary.json`, `report.md`: the tests and the decision.

## Reproduction

```text
python scripts/run_golf_structure.py --check-committed
```

recomputes everything from the committed extractions of golf-v0.1 and
linearizations-mathlib-v0.1 (no Lean needed); CI runs it.

## Outcome

160 pairs. **H28 not supported**: no quantity differs once length is
accounted for.

| Quantity | Adjusted: pairs that differ, golfed lower, p (Holm) | Unadjusted: pairs that differ, golfed lower |
| --- | --- | --- |
| depth | 104, 51, 0.92 (0.92) | 113, 103 |
| width | 92, 40, 0.25 (0.50) | 75, 65 |
| branching | 120, 48, 0.035 (0.11) | 123, 66 |

Unadjusted, golfed proofs are shallower and narrower in almost every pair, as
shorter proofs are. Adjusted for length, depth and width show nothing, and
the golfed proof branches more in 72 of 120 pairs, which does not survive the
correction for three tests. Together with golf-v0.1: none of the four graph
quantities tested separates the proof reviewers accepted as an improvement
from its predecessor beyond its length.

## Interpretation boundary

The same 160 pairs as golf-v0.1's structure test, so the samples are not
independent of the earlier analysis; the adjustment uses one reference slice.
Quantities outside the graph (lemmas used, term size, elaboration time) are
not tested.
