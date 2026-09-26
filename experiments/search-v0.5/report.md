# A step-level Lean prover as the proposer (search v0.5)

Frozen in `preregistration.json` (SHA-256 `2e0f9161cce26876a759db31b7b00108939df398a5ec9347457412e0fbceb2d6`).

Tasks: 60; stated: {'whole': 47, 'andor': 47}; abandoned: {'whole': 1, 'andor': 1}; errors: {'whole': 0, 'andor': 0}.

| Key | Expansions | Order duplicates | Goal duplicates |
| --- | ---: | ---: | ---: |
| fine | 1457 | 0 (0.0%) | 86 (5.9%) |
| default | 1457 | 0 (0.0%) | 93 (6.4%) |
| coarse | 1457 | 1 (0.1%) | 300 (20.6%) |

Proved at 24 expansions: model 7, holdout-v0.1's menu 3 (model only 5, menu only 1, one-sided p = 0.109).
Proved at 48: whole 8, AND-OR 10; discordant {'wholeOnly': 0, 'andorOnly': 2, 'signTestTwoSided': 0.5}. Proofs found after expansion 24: 2.
Entangled candidates: 75. Frontier exhausted: {'whole': 11, 'andor': 11}.

## Hypotheses

- H45: supported: False.
- H46: supported: True.
- H47: supported: True.
- H48: supported: True.
- H49: supported: True.

## Interpretation boundary

One quantized open-weights prover at one sampling setting, on the theorems of one Mathlib slice.
The model proposes tactics for the first goal only, which is what it was trained on; the
whole-state search therefore sees no more context than the AND-OR search does.
