# What the text keys conflate (keys-v0.1, not registered)

keys-v0.1 found that 8.7% of the printed-goal AND-OR search's merges and 5.6% of the whole-state searches'
drops join goals whose Lean expressions differ. This exploratory check, made after keys-v0.1's results were
read, looks at what differs. It replays from their recorded draws the six units with the most false merges and
the six with the most false drops, records each goal's printed text and faithful serialization in full, and
finds where each conflated pair's serializations first differ.

## Artifacts

- `conflations.json`: per unit, the conflations found against keys-v0.1's recorded count; per conflation, the
  tokens around the first difference and its category.

## Reproduction

```text
python scripts/explore_false_merges.py --units 6 --out FULL.json
python scripts/explore_false_merges.py --summarize FULL.json --out experiments/keys-v0.1-conflations/conflations.json
```

The first replays the twelve units (a Mathlib REPL; about forty minutes) and writes the full serializations,
about 12 MB, which are not committed; the second classifies them.

## Outcome

All twelve replays reproduced their recorded counts: 102 false merges and 68 false drops. By the first
identifier where the two serializations differ:

| First difference | Merges | Drops |
| --- | ---: | ---: |
| an instance path: the same operation reached through different instances of Mathlib's hierarchy, as `AddZero.toZero` against `NegZeroClass.toZero` | 26 | 46 |
| a universe level written differently, as `max (u_1+1) (u_2+1)` against `max u_1 u_2 + 1` | 25 | 8 |
| a different one of two hypotheses that print alike | 33 | 0 |
| an unreduced lambda, as `(fun _ => ℝ) x` against `ℝ` | 15 | 8 |
| an auxiliary proof term | 2 | 2 |
| other (a coercion, or `PNat.val` against `Subtype.val`) | 1 | 4 |

Most conflations join syntactic variants of one term, which are likely equal up to definitional unfolding
(not checked in Lean): an identity up to definitional equality would join them too, and the faithful key
separates them only because it is syntactic. The hypothesis references are different goals. All 33 come from
one theorem, `MeasureTheory.borel_eq_borel_of_le`, whose goals mention one of two topologies on a type and
print alike whichever they mention; no text key can tell them apart.

## Boundary

The units were chosen for having the most conflations, and each theorem contributes mostly one category, so the
shares describe these six theorems, not the population. Categories come from the first differing identifier,
a heuristic (`category` in the script).
