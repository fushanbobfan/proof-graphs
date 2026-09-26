# Both searches with shared draws of a step-level prover (search v0.6)

Frozen in `preregistration.json` (SHA-256 `0c811dec14a6d5b8e2448f182ce893796f6f05fa8dd0b609b500112f8844c452`).

## Test set (tasks no model search had run)

Tasks: 140; stated: {'whole': 122, 'andor': 122}; abandoned: {'whole': 0, 'andor': 0}; errors: {'whole': 0, 'andor': 0}.
Proved: whole 30, AND-OR 32; by one search only: whole 0, AND-OR 2 (one-sided p = 0.25, two-sided p = 0.5).
Proved by both: 30; with different expansions to proof: 10, AND-OR fewer in 6 (one-sided p = 0.377).
Entangled candidates: 142. Draws: {'whole': {'drawn': 2050, 'shared': 1230}, 'andor': {'drawn': 2236, 'shared': 1149}}.

## Replication set (search-v0.5's tasks)

Tasks: 60; stated: {'whole': 47, 'andor': 47}; abandoned: {'whole': 0, 'andor': 0}; errors: {'whole': 0, 'andor': 0}.
Proved: whole 9, AND-OR 9; by one search only: whole 0, AND-OR 0 (one-sided p = n/a, two-sided p = n/a).
Proved by both: 9; with different expansions to proof: 4, AND-OR fewer in 1 (one-sided p = 0.938).
Entangled candidates: 58. Draws: {'whole': {'drawn': 1098, 'shared': 373}, 'andor': {'drawn': 837, 'shared': 681}}.

## Duplicates (whole-state search, all tasks)

| Key | Expansions | Order duplicates | Goal duplicates |
| --- | ---: | ---: | ---: |
| fine | 4751 | 5 (0.1%) | 226 (4.8%) |
| default | 4751 | 5 (0.1%) | 233 (4.9%) |
| coarse | 4751 | 8 (0.2%) | 1241 (26.1%) |

C7: 0 of 6221 draws repeat a goal and occurrence within a task.

## Hypotheses

- H50: supported: False.
- H51: supported: False.
- H52: supported: True.
- H53: supported: True.

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the
theorems of one Mathlib slice. Shared draws remove the draw from the comparison of the two searches
on the goals both meet; they do not make the proposer deterministic, so a rerun draws anew.
