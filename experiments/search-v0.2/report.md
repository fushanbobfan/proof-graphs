# Deeper tactic search (search v0.2)

The searches of search-v0.1, unchanged, at 192 expansions on the tasks where v0.1's budget of 24
ran out; definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256
`47309869cfd3ea84bda96bb85959a6bb1b46d3e747abbb4e370b4329517f6b4c`).

Tasks: 20.

| Arm | Budget | Whole-state expansions | Order duplicates | Goal duplicates | Proved: whole | Proved: AND-OR |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| menu | 24 | 343 | 13 (3.8%) | 42 (12.2%) | 1 | 0 |
| menu | 48 | 568 | 20 (3.5%) | 84 (14.8%) | 1 | 0 |
| menu | 96 | 977 | 32 (3.3%) | 162 (16.6%) | 1 | 0 |
| menu | 192 | 1653 | 44 (2.7%) | 300 (18.1%) | 1 | 0 |
| model | 24 | 382 | 14 (3.7%) | 34 (8.9%) | 2 | 1 |
| model | 48 | 679 | 22 (3.2%) | 84 (12.4%) | 2 | 1 |
| model | 96 | 1215 | 33 (2.7%) | 188 (15.5%) | 2 | 1 |
| model | 192 | 2271 | 60 (2.6%) | 415 (18.3%) | 2 | 1 |

## Hypotheses

- H17 (goal-duplicate fraction at 192 at least 2 times that at 24, both arms): supported: False.
- H18 (AND-OR proves at least as many at 192 in both arms, more in one): supported: False.
- H19 (order-duplicate fraction at 192 below 5%, both arms): supported: True.

C1 (menu arm reproduces search-v0.1's first 24 expansions): 40 of 40 searches.

## Interpretation boundary

Breadth-first search with a weak proposer, on the tasks where v0.1's searches ran out of
budget. The measures describe where such a search spends its work as the budget grows,
not the best achievable prover.
