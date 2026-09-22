# Golfed proofs and their predecessors (golf v0.1)

Golf pairs of Mathlib between v4.29.0 and v4.32.0, both proofs elaborated at v4.32.0; definitions,
corpus, and hypotheses are frozen in `preregistration.json` (SHA-256
`b3eb3113bb87e2c262fa452febb1d96b0f777ab6c8a43787f7e61f53101a9730`).

Pairs: 306; elaborated on both sides: 294 from 104 commits; predecessor fails at v4.32.0: 11; golfed module fails: 1.

| Quantity | Predecessor | Golfed |
| --- | --- | --- |
| Steps, median (q1, q3) | 11 (4, 20) | 4 (0, 9) |
| Term proofs (no tactic step) | 34 | 82 |
| Structure index, median (q1, q3), both sides at least 3 steps | 0.315 (0.162, 0.398) | 0.236 (0.000, 0.371) |

Pairs whose steps and linearizations are unchanged (golfs the graph does not see): 56 of 294.

## Hypotheses

- H20 (golfed proof has fewer steps, among 238 pairs that differ): fewer 210, more 28, p = 5.73e-36; supported: True.
- H21 (golfed proof has the lower structure index, among 125 pairs that differ): lower 86, higher 39, p = 1.59e-05 (other direction p = 1); supported: True.
- H21 by commit (71 commits with a majority): lower 52, p = 5.61e-05 (other direction p = 1).

## Interpretation boundary

A golf is what Mathlib's reviewers accepted as a better proof of the same statement, which is
one notion of quality among several (shorter, faster, more robust, more idiomatic). Pairs whose
predecessor no longer elaborates at v4.32.0 are excluded, which removes golfs that deleted the
lemmas their predecessors used.
