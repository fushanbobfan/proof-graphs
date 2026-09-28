# States, goals, and coupled groups over three sets of draws (search v0.8)

Frozen in `preregistration.json` (SHA-256 `cb900d651179fbb27240146db7a00a98c8c2dd24b8cac7f1bdb0cb9646b007b5`).

Tasks: 200; stated in every set: 158; errors: 0; abandoned: 9.

| Search | set 0 | set 1 | set 2 | pooled (task-sets) |
| --- | ---: | ---: | ---: | ---: |
| whole | 38 | 37 | 41 | 116 |
| goals | 40 | 39 | 42 | 121 |
| groups | 40 | 39 | 43 | 122 |

| Hypothesis | Pair | Tasks first more | Tasks second more | One-sided p | Holm | Rate difference (95% interval) | Supported |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- |
| H64 | groups > goals | 1 | 0 | 0.5 | 0.5 | 0.00211 [0.0, 0.007407] | False |
| H65 | groups > whole | 7 | 1 | 0.03515625 | 0.10546875 | 0.012658 [0.004301, 0.023529] | False |
| H66 | goals > whole | 7 | 2 | 0.08984375 | 0.1796875 | 0.010549 [0.0, 0.022346] | False |

## Cost

| Search | Expansions | Draws (seeded / shared / new) | Completion tokens | REPL calls (tactic / export / harness) | Median search seconds |
| --- | ---: | --- | ---: | --- | ---: |
| whole | 13115 | 4013 / 4322 / 4780 | 1186579 | 155845 / 38987 / 0 | 35.150000000000006 |
| goals | 13560 | 4188 / 5203 / 4169 | 1035052 | 160840 / 37397 / 8624 | 24.299999999999997 |
| groups | 13464 | 4116 / 5942 / 3406 | 865152 | 160595 / 37898 / 8434 | 15.95 |

Mechanisms: independent-goal candidates discarded as entangled 689; coupled-group candidates discarded as coupled outside their group 28; groups of several goals made 1210, proofs through one 1; whole-state proofs using a goal's later draw 4.
C13: 0 repeated occurrences among 12415 new draws. C14: fast export in 1500 of 1500 searches.

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the
theorems of one Mathlib slice. Identity is syntactic on instantiated Lean expressions; goals equal up
to definitional unfolding stay apart.
