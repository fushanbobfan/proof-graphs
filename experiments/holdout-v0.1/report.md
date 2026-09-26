# Holdout slice (holdout v0.1)

A second Mathlib slice, disjoint from the first; frozen in `preregistration.json` (SHA-256
`25293a00adf930a292c35bb528fe22e8fd36142cfdcb9d802a72b93755b1d7ae`).

Modules extracted: 142; dropped: 2. Proofs: 2244; counted: 2244.

| Stratum | Proofs | Median L | Median index | Single order |
| --- | ---: | ---: | ---: | ---: |
| steps-1 | 486 | 1 | n/a | 100.0% |
| steps-2-5 | 975 | 1 | 0.000 | 72.7% |
| steps-6-10 | 410 | 8 | 0.238 | 27.1% |
| steps-11-20 | 239 | 1540 | 0.282 | 7.9% |
| steps-21-50 | 109 | 1.415e+11 | 0.373 | 0.0% |
| steps-51+ | 25 | 4.371e+40 | 0.454 | 0.0% |

Strata tested: steps-6-10, steps-11-20, steps-21-50.

Searches on 200 tasks: whole-state order duplicates 112 of 2413 (4.6%), goal duplicates 343 (14.2%); proved: {'whole': 11, 'andor': 10}; discordant: {'wholeOnly': 1, 'andorOnly': 0, 'signTestTwoSided': 1.0}; entangled candidates: 468.

## Hypotheses

- H34: supported: False.
- H35: supported: True.
- H36: supported: True.
- H37: supported: True.
- H38: supported: True.
- H39: supported: False.
