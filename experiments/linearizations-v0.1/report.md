# Order redundancy of ProofNet-IR's tactic proofs (linearizations v0.1)

Exact numbers of step orderings admitted by the goal-dependency graph of every
tactic proof in ProofNet-IR v0.10.0; definitions, corpus, and hypotheses are frozen
in `preregistration.json` (SHA-256 `7e4a59d0af5cd4dd7b7bf5b96dd6f6b14da15b5cd2846b38ab65412d6ab585de`).

Proofs with tactic steps: 3994; counted exactly: 3992.

| Steps | Proofs | Forests | Multi-root | Linearizations median (q1, q3, max) | log10 median | Structure median (q1, q3) | Single order |
| --- | ---: | ---: | ---: | --- | ---: | --- | ---: |
| steps-1 | 226 | 226 | 0 | 1 (1, 1, 1) | 0.00 | n/a | 100.0% |
| steps-2-5 | 1220 | 1220 | 18 | 1 (1, 2, 60) | 0.00 | 0.000 (0.000, 0.346) | 59.6% |
| steps-6-10 | 828 | 824 | 21 | 15 (3, 54, 51840) | 1.18 | 0.255 (0.140, 0.373) | 15.3% |
| steps-11-20 | 845 | 844 | 14 | 6720 (350, 450450, 8.355e+14) | 3.83 | 0.337 (0.243, 0.418) | 1.8% |
| steps-21-50 | 588 | 586 | 14 | 8.786e+13 (1.992e+9, 1.663e+19, 1.717e+42) | 13.94 | 0.413 (0.349, 0.489) | 0.0% |
| steps-51+ | 263 | 262 | 4 | 1.909e+51 (6.213e+37, 2.450e+80, 1.315e+628) | 51.28 | 0.502 (0.454, 0.544) | 0.0% |

## Hypotheses

- H10 (median linearizations at least 10 in every stratum of at least 6 steps): supported: True.
- H11 (median structure index below 0.5 in every such stratum): supported: False.

## Interpretation boundary

The count is a property of the proofs as written: how many step orders the
goal-dependency graph admits. It says nothing about how a search would explore
them, which is the next step, and nothing about proofs outside this corpus.
