# Goal identity and a search without one-shot provers (search v0.4)

Definitions, tasks, and hypotheses are frozen in `preregistration.json` (SHA-256
`860c788816406be41ac9c65e15faa36296b48ebdbdc6a609b733dabeef3f46ed`).

## Keys arm: standard menu, whole-state search, 24 expansions

Tasks: 300; stated: {'whole': 258}; abandoned: {'whole': 0}; errors: {'whole': 0}.

| Key | Expansions | Undefined | Order duplicates | 95% interval | Goal duplicates | 95% interval |
| --- | ---: | ---: | ---: | --- | ---: | --- |
| fine | 3417 | 0 | 179 (5.2%) | 4.1% to 6.1% | 527 (15.4%) | 13.2% to 17.3% |
| default | 3417 | 0 | 181 (5.3%) | 4.2% to 6.1% | 543 (15.9%) | 13.4% to 18.1% |
| coarse | 3417 | 0 | 179 (5.2%) | 4.1% to 6.1% | 956 (28.0%) | 25.2% to 30.9% |

Proved: whole 22.
Searches that exhausted their frontier without a proof: {'whole': 138}.

## Hammer-free arm: 96 expansions

Tasks: 135; stated: {'whole': 115, 'andor': 115}; abandoned: {'whole': 0, 'andor': 0}; errors: {'whole': 0, 'andor': 0}.

| Key | Expansions | Undefined | Order duplicates | 95% interval | Goal duplicates | 95% interval |
| --- | ---: | ---: | ---: | --- | ---: | --- |
| fine | 3367 | 0 | 127 (3.8%) | 2.3% to 5.3% | 824 (24.5%) | 16.2% to 32.0% |
| default | 3367 | 0 | 129 (3.8%) | 2.3% to 5.4% | 873 (25.9%) | 16.2% to 34.6% |
| coarse | 3367 | 0 | 129 (3.8%) | 2.3% to 5.4% | 873 (25.9%) | 16.2% to 34.6% |

Proved: whole 0, andor 0.
Proved by the whole-state search only: 0; by the AND-OR search only: 0 (one-sided sign test p = n/a). Entangled candidates: 398; AND-OR expansions of a goal equal under the coarse key to an earlier one: 1.
Searches that exhausted their frontier without a proof: {'whole': 91, 'andor': 95}.

## Hypotheses

- H30: supported: True.
- H31: supported: True.
- H32: supported: False.
- H33: supported: True.

C5 (the keys arm reproduces search-v0.3): 258 of 258 searches.
C6 (default-key flags from digests equal the search's): 0 of 6784 expansions differ.

## Interpretation boundary

Breadth-first search with fixed menus on theorems of one Mathlib slice. The keys compare printed goals;
definitional equality is not tested.
