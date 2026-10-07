# Whole states and coupled goal groups with 256 expansions (search v0.9)

Frozen in `preregistration.json` (SHA-256 `e588177c69aafc0aec2b52cd6c388563ea610d625ee6a691005ada22284586e0`).

Tasks: 200; stated in both searches: 169; unit attempts: 234; errors: 0; abandoned searches: 1.

| Search | proved by 48 | proved by 96 | proved by 192 | proved by 256 | frontier emptied | budget used up |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| whole | 41 | 44 | 46 | 46 | 52 | 70 |
| groups | 43 | 46 | 47 | 48 | 47 | 74 |

| Hypothesis | Pair | Tasks first more | Tasks second more | One-sided p | Rate difference (95% interval) | Supported |
| --- | --- | ---: | ---: | ---: | --- | --- |
| H87 | groups > whole | 3 | 1 | 0.3125 | 0.011834 [-0.011173, 0.037234] | False |

| Discordant tasks (groups only / whole only) | 48 | 96 | 192 | 256 |
| --- | ---: | ---: | ---: | ---: |
| H87's pair | 2 / 0 | 3 / 1 | 3 / 2 | 3 / 1 |

H88 (goal sharing grows past 48 expansions): goal-duplicate share 0.056944 in the first 48 expansions and 0.059153 after them, over the 75 whole-state searches that ran past 48; difference 0.002208, 95% interval [-0.017076, 0.022708]; supported: False.
H89 (order duplicates under 1%): 40 of 19106 whole-state expansions, share 0.002094, 95% interval [0.001199, 0.003188]; supported: True.

| Whole-state expansions up to | Expansions | Order duplicates | Goal duplicates |
| ---: | ---: | ---: | ---: |
| 48 | 4280 | 0.001869 | 0.057243 |
| 96 | 7755 | 0.001934 | 0.056351 |
| 192 | 14626 | 0.00212 | 0.057227 |
| 256 | 19106 | 0.002094 | 0.058725 |

## Cost

| Search | Expansions | Draws (seeded / shared / new) | Completion tokens | REPL calls (tactic / export / harness) | Median search seconds |
| --- | ---: | --- | ---: | --- | ---: |
| whole | 19106 | 4527 / 3502 / 11077 | 2924386 | 240022 / 61738 / 0 | 7.25 |
| groups | 20260 | 5346 / 3839 / 11075 | 2956819 | 254066 / 60644 / 12040 | 12.7 |

Mechanisms: coupled-group candidates discarded as coupled outside their group 86; groups of several goals made 2705, in 75 searches, proofs through one 0; whole-state proofs using a goal's later draw 3.
C28: 331 of 331 searches repeat search-v0.8's first set in their first 48 expansions (True). C29: 0 repeated occurrences and 0 draws of seeded occurrences among 22168 new draws (True). C30: fast export in 337 of 337 searches (True). C31: 22168 of 22168 new draws with all 16 completions (True).

## Interpretation boundary

One quantized open-weights prover at one sampling setting, breadth-first search, and one set of draws,
on the theorems of one Mathlib slice. Identity is syntactic on instantiated Lean expressions; goals
equal up to definitional unfolding stay apart.
