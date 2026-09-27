# Goals and states up to renaming (search v0.7)

Frozen in `preregistration.json` (SHA-256 `2db1517766f77d7a0ddf36de71d3653dfa67205905f3e2e150d43205af5b7214`).

Tasks: 200; stated: {'whole': 169, 'andor': 169, 'wholeRenamed': 169, 'andorRenamed': 169}; abandoned: {'whole': 1, 'andor': 1, 'wholeRenamed': 0, 'andorRenamed': 0}; errors: {'whole': 0, 'andor': 0, 'wholeRenamed': 0, 'andorRenamed': 0}.

| Search | Proved | Expansions | Verifier rejections | Draws (seeded / shared / new) |
| --- | ---: | ---: | ---: | --- |
| whole | 39 | 4703 | 14 | 4703 / 0 / 0 |
| andor | 41 | 4855 | 2 | 4855 / 0 / 0 |
| wholeRenamed | 42 | 4358 | 14 | 3287 / 230 / 841 |
| andorRenamed | 43 | 4512 | 2 | 3638 / 205 / 669 |

| Hypothesis | Pair | First only | Second only | One-sided p | Holm-adjusted | Supported |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| H54 | andorRenamed > whole | 4 | 0 | 0.0625 | 0.25 | False |
| H55 | andorRenamed > andor | 2 | 0 | 0.25 | 0.5 | False |
| H56 | andorRenamed > wholeRenamed | 2 | 1 | 0.5 | 0.5 | False |
| H57 | wholeRenamed > whole | 3 | 0 | 0.125 | 0.375 | False |

andorRenamed merges: 14545 goals created; 2556 merged by print, 2374 by a renaming (2044 printing identically after it, 266 reusing a checked step); 2243 checks, 135 refused; 9615 new goals. H58 supported: False.
wholeRenamed: 1618 child states dropped as duplicates up to renaming only.

| Set | whole | andor | wholeRenamed | andorRenamed |
| --- | ---: | ---: | ---: | ---: |
| test (122 stated) | 30 | 32 | 33 | 33 |
| replication (47 stated) | 9 | 9 | 9 | 10 |

C8 (replay of search-v0.6): 338 units compared, 2 differing, 0 drawing anew; holds: False.
C9: 0 repeated occurrences among 6221 seeded and 1510 new draws.

## Duplicates (whole-state searches, all tasks)

| Search | Key | Expansions | Order duplicates | Goal duplicates |
| --- | --- | ---: | ---: | ---: |
| whole | fine | 4703 | 5 (0.1%) | 224 (4.8%) |
| whole | default | 4703 | 5 (0.1%) | 231 (4.9%) |
| whole | coarse | 4703 | 8 (0.2%) | 1231 (26.2%) |
| wholeRenamed | fine | 4358 | 6 (0.1%) | 176 (4.0%) |
| wholeRenamed | default | 4358 | 6 (0.1%) | 184 (4.2%) |
| wholeRenamed | coarse | 4358 | 9 (0.2%) | 256 (5.9%) |

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the
theorems of one Mathlib slice. Renaming is by position in the printed context and checked in print;
goals equal up to definitional unfolding, or up to the names of bound variables, stay apart.
