# Redundancy inside a tactic search (search v0.1)

Whole-state and AND-OR searches with the same proposer and budget on theorems of the
Mathlib slice, in their original context; definitions, tasks, and hypotheses are frozen
in `preregistration.json` (SHA-256 `6e550e29017e14edc6ac5f9eb79599be9476577a8fa71009d06f11ec8d76913f`).

Tasks: 47; stated in context: 40.

| Arm | Tasks | Whole-state expansions | Order duplicates | Goal duplicates | Valid tactics per expansion | Proved: whole | Proved: AND-OR | Closings refused by verification (whole / AND-OR) | Entangled candidates (AND-OR) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| menu | 40 | 448 | 15 (3.3%) | 48 (10.7%) | 3.3 | 5 | 4 | 0 / 0 | 63 |
| model | 40 | 556 | 13 (2.3%) | 48 (8.6%) | 4.0 | 5 | 5 | 0 / 0 | 67 |

## Hypotheses

- H14 (order-duplicate fraction below 1% in both arms): supported: False.
- H15 (goal-duplicate fraction at least 10% in both arms): supported: False.
- H16a (AND-OR proves at least as many tasks in both arms): supported: False.
- H16b (AND-OR proves strictly more in the model arm): supported: False.

Arms run: menu, model.

## Interpretation boundary

Both searches are breadth-first with a small budget and a weak proposer; the
fractions describe where such a search spends its expansions, not the best
achievable prover. A proof counts only when it re-verifies from the statement.
