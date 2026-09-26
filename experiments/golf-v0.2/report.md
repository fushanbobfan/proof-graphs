# Golf pairs from v4.26.0 to v4.29.0 (golf v0.2)

Frozen in `preregistration.json` (SHA-256 `ee15be40f91e0dd5ff1b6360179a4afa1c929ab28bd934241ac68029d633d7e8`).

Pairs: 511; both sides elaborate: 479 from 84 commits; excluded: {'before fails': 28, 'original fails': 4}. Pairs with at least 3 steps on both sides: 261.

- H40 (golfed branches more after length adjustment): 137 of 198, one-sided p = 3.427202452158066e-08; supported: True.
- H41 (golfed has fewer steps): 356 of 409, p = 1.6161042753469925e-56; supported: True.
- H42 (golfed has the lower structure index): 103 of 202, p = 0.4164454120223839; supported: False.
- H43 (length-adjusted structure index not different): golfed lower in 84 of 224, two-sided p = 0.00022221771173715923; supported: False.
- H44 (some adjusted quantity differs, Holm): supported: True.

| Quantity | Adjusted: differing pairs, golfed lower, p (Holm) | Unadjusted: differing, golfed lower |
| --- | --- | --- |
| depth | 174, 108, 0.001800199793547577 (0.003600399587095154) | 182, 174 |
| width | 103, 38, 0.010063333265586337 (0.010063333265586337) | 65, 57 |
| branching | 198, 61, 6.854404904316132e-08 (2.0563214712948394e-07) | 197, 62 |
