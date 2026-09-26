# Menu searches on every candidate theorem (search v0.3)

The menu arm of search-v0.1's two searches, unchanged, on all candidate theorems of the Mathlib
slice; definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256
`f0aafd5e3fe4f2a58ca1002114670c62af3044eaf9f40440d7c040c772e661f7`).

Tasks: 1347; stated: 1171; abandoned on a REPL timeout: whole 0, AND-OR 0.

| Search | Expansions | Order duplicates | Goal duplicates | Proved | Entangled candidates |
| --- | ---: | ---: | ---: | ---: | ---: |
| whole-state | 16095 | 728 (4.5%) | 2400 (14.9%) | 103 | |
| AND-OR | 15875 | | | 102 | 2609 (4.1%) |

Proved by the whole-state search only: 3 (1 with an entangled candidate); by the AND-OR search only: 2 (two-sided sign test p = 1).

## Hypotheses

- H22 (order-duplicate fraction below 5%): supported: True.
- H23 (goal duplicates at least 2 times order duplicates): supported: True.
- H24 (AND-OR proves at least as many): supported: False.
- H25 (at least half of the whole-only tasks have an entangled candidate): supported: False.

C2 (the search-v0.1 tasks reproduce exactly): 80 of 80 searches.

## Registered analyses

- Order duplicates against log10 orderings of the original proof: Spearman rho = -0.005, p = 0.86, n = 1171.
- Goal duplicates against log10 orderings: rho = 0.052, p = 0.0785, n = 1171.

## Interpretation boundary

Breadth-first search with the 26-tactic menu at 24 expansions, on every candidate theorem of one
Mathlib slice. The measures describe where such a search spends its expansions, not the best
achievable prover.
