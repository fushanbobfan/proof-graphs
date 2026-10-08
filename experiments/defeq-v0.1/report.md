# Goal identity up to definitional equality (defeq v0.1)

Frozen in `preregistration.json` (SHA-256 `e60924efe12b586a7f4f74a21501d74997a6a828fc0c74a06a84f7d80cc2d051`).

| Units | Expansions | Goal duplicates: faithful / reducible / instances / default | Extra state merges: reducible / instances / default | Printed-key false drops merged (instances) |
| --- | ---: | --- | --- | --- |
| search-v0.7 whole-state search, step prover (169 of 200) | 4751 | 27.9% / 31.0% / 31.0% / 31.0% | 3.50% / 3.50% / 3.54% | 138 of 165 (83.6%) |
| search-v0.4 keys arm, menu (258 of 300) | 3417 | 28.8% / 28.9% / 28.9% / 29.0% | 2.07% / 2.09% / 2.12% | 349 of 382 (91.4%) |

| Units | Instances minus faithful, goal duplicates (95% interval) | Merge / tactic time, median | isDefEq checks (accepted, exhausted) at instances |
| --- | --- | ---: | --- |
| prover | 3.16% [0.019845, 0.046512] | 0.01% | 560 (536, 0) |
| menu | 0.12% [0.0, 0.003042] | 0.00% | 258 (229, 0) |

Goal statuses: {'exact': 8992, 'reducible': 2390, 'mvar': 1027, 'error': 207, 'differs': 2}.
C32: 391 of 426 replays match keys-v0.1 (False). C33: 11382 of 11591 goals without a metavariable round-trip (True). C34: 427 of 427 passes complete, 11373 of 11382 goals elaborate (True).

## Hypotheses

- H90: supported: False.
- H91: supported: True.
- H92: supported: True.
- H93: supported: True.
