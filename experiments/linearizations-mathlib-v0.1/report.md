# Order redundancy of a Mathlib slice (linearizations-mathlib v0.1)

Exact numbers of step orderings admitted by the goal-dependency graph of every
tactic proof in every 50th Mathlib module; definitions, corpus, and hypotheses are
frozen in `preregistration.json` (SHA-256 `2f682f677bdf786c33dc6dd2b4d6bf5b30108f575c46183a4c2236ae6f7cf473`).

Modules extracted: 147; dropped for elaboration errors: 0. Proofs with tactic steps: 2807; counted exactly: 2806.

| Steps | Proofs | Forests | Multi-root | Linearizations median (q1, q3, max) | log10 median | Structure median (q1, q3) | ProofNet-IR structure median | Single order |
| --- | ---: | ---: | ---: | --- | ---: | --- | ---: | ---: |
| steps-1 | 561 | 561 | 0 | 1 (1, 1, 1) | 0.00 | n/a | n/a | 100.0% |
| steps-2-5 | 1251 | 1250 | 172 | 1 (1, 2, 120) | 0.00 | 0.000 (0.000, 0.346) | 0.000 | 70.2% |
| steps-6-10 | 542 | 541 | 88 | 10 (1, 66, 3628800) | 1.00 | 0.258 (0.000, 0.393) | 0.255 | 28.2% |
| steps-11-20 | 275 | 275 | 38 | 880 (29, 48279, 1.126e+15) | 2.94 | 0.282 (0.132, 0.414) | 0.337 | 14.2% |
| steps-21-50 | 111 | 111 | 11 | 1.067e+11 (1.007e+8, 2.285e+15, 3.911e+46) | 11.03 | 0.388 (0.289, 0.478) | 0.413 | 0.9% |
| steps-51+ | 14 | 13 | 3 | 1.555e+42 (2.057e+32, 1.720e+63, 1.052e+172) | 42.19 | 0.445 (0.334, 0.764) | 0.502 | 0.0% |

Strata tested (at least 6 steps and 30 counted proofs): steps-6-10, steps-11-20, steps-21-50.

## Hypotheses

- H12 (median structure index within 0.1 of ProofNet-IR's in every tested stratum): supported: True.
- H13 (median linearizations at least 10 in every tested stratum): supported: True.

## Interpretation boundary

The slice is a systematic sample of modules, not of proofs; a module's proofs share
an author and a subject. The count says nothing about how a search would explore
the orderings, and Lean's first-goal convention already fixes one of them.
