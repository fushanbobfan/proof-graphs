# Linearizations on a Mathlib slice v0.1

Step 1b of the program ([design](../../docs/design.md)): the count of
[linearizations-v0.1](../linearizations-v0.1/README.md) repeated on a
systematic sample of Mathlib, to ask whether ProofNet-IR's numbers are
typical of proofs written by many hands.

## Artifacts

- `preregistration.json`: Mathlib's revision (`v4.32.0`, the toolchain of
  ProofNet-IR), the population rule (7,835 modules outside `Tactic`, `Util`,
  `Lean`, `Testing`, `Deprecated`, `Mathport`), the 157 modules of stride 50,
  the ProofNet-IR structure medians H12 is judged against and the hash of the
  summary they come from, the unchanged extractor and counter hashes, and
  hypotheses H12 and H13; committed on `main` before any extraction;
- `extraction.jsonl.gz`, `results.jsonl`, `failures.json`, `summary.json`,
  `report.md`: as in the ProofNet-IR experiment, plus the list of modules
  dropped for elaboration errors (none).

## Reproduction

```text
lake exe cache get
python scripts/run_mathlib_slice.py --check-committed
```

recounts every committed graph, re-extracts the three slice modules with the
fewest nodes and compares node shapes, and verifies the hashes; CI runs it.
`--run` re-extracts the 157 modules (50 minutes here; each module is
elaborated in its own process, 15 seconds to several minutes).

## Outcome

147 of the 157 modules have tactic proofs: 2,807 declarations, 2,806
counted exactly (one non-forest of 95 steps excluded, three non-forests in
all). Mathlib's proofs are shorter than ProofNet-IR's (quartiles 2, 3, 7
steps against 4, 8, 18; longest 126 against 461) and more often admit a
single order (48.8% of the proofs with at least two steps, against 23.2%).

| Steps | Proofs | Linearizations median (max) | Structure median | ProofNet-IR | Single order |
| --- | ---: | --- | ---: | ---: | ---: |
| 2–5 | 1,251 | 1 (120) | 0.000 | 0.000 | 70.2% |
| 6–10 | 542 | 10 (3.6·10^6) | 0.258 | 0.255 | 28.2% |
| 11–20 | 275 | 880 (1.1·10^15) | 0.282 | 0.337 | 14.2% |
| 21–50 | 111 | 1.1·10^11 (3.9·10^46) | 0.388 | 0.413 | 0.9% |
| 51+ | 14 | 1.6·10^42 (1.1·10^172) | 0.445 | 0.502 | 0.0% |

Strata tested, as registered: 6–10, 11–20, 21–50 steps (at least 30 counted
proofs).

- H12 supported: in every tested stratum the median structure index is
  within 0.1 of ProofNet-IR's (differences 0.003, 0.055, 0.025). The rise of
  the index with length is the same in both corpora.
- H13 supported: the median number of orderings is 10, 880, and 1.1·10^11 in
  the tested strata.

Two impurities, both small: 198 declarations are generated (derived
instances, `ext`, `ext_iff`), and 26 records in one module are the `by`
blocks of `variable` binders, which have no declaration and were recorded
once per use as `<anonymous>` (removing them moves the 6–10 median from 0.258
to 0.252). The extractor was not changed for this run; both are noted for
its next version.

## Interpretation boundary

The slice samples modules, not proofs, so the proofs of one module share an
author and a subject; 157 modules across 23 top-level directories is broad
enough for medians, not for the tail (14 proofs above 50 steps). The count
says nothing about how a search explores the orderings, and Lean's
first-goal convention already fixes one of them; that is what `search-v0.1`
measures. The extractor elaborates with Lean's default options, not with
those of Mathlib's build (`autoImplicit false`, `maxSynthPendingDepth 3`).
That changes none of these graphs: re-extracting all 157 modules with
Mathlib's options inserted gives the same nodes for every one of the 2,784
distinct declaration names (`options-check.json`, from
`scripts/check_slice_options.py`, 2026-09-24).
