# Recount v0.1

[extraction-audit-v0.1](../extraction-audit-v0.1/README.md) found that the
step derivation loses the closing step of a tactic whose own internal node
mentions the goal it closes, mostly `simpa ... using ...`.
`scripts/count_linearizations_v2.py` corrects the consumption rule (a later
node inside the step's own subtree no longer keeps a goal open) and changes
nothing else. This experiment recounts the three committed extractions with
it, re-evaluates the hypotheses decided on them, re-runs the structural audit
and the blind-reconstruction comparison, and writes the corrected dataset. The
earlier experiments keep their registered rule and numbers.

## Artifacts

- `preregistration.json`: the correction, the input hashes, hypotheses H10r to
  H13r, H20r, H21r, and H28r (the earlier hypotheses, re-evaluated), checks C3
  and C4, and what had been seen before registration (the correction's checks
  and the number of changed graphs; no median or decision under it);
  `amendment-1.json`: the dataset is written compressed (the first run failed
  writing it, before any result was read);
- `library.jsonl`, `slice.jsonl`, `golf.jsonl`: per-proof and per-pair rows;
- `summary.json`, `report.md`; and `datasets/proof-graphs-v0.2.jsonl.gz`.

## Reproduction

```text
python scripts/run_recount.py --check-committed
```

recomputes everything from the committed extractions, including the invariant
audit and the comparison with the reconstructions; CI runs it.

## Outcome

The correction adds steps to 838 of the 3,994 ProofNet-IR graphs (the count
changes in 774), to 114 of the 2,807 slice graphs (54), and to 40 of the 484
golf graphs. C3 holds (no invariant violated; 3,307 graphs brute-forced) and
C4 holds (30 of 30 reconstructions agree).

| Steps | ProofNet-IR: median L | index | Slice: median L | index |
| --- | ---: | ---: | ---: | ---: |
| 6 to 10 | 15 | 0.270 | 10 | 0.270 |
| 11 to 20 | 6,720 | 0.346 | 902 | 0.288 |
| 21 to 50 | 9.3·10^13 | 0.428 | 8.4·10^10 | 0.391 |
| 51 and more | 1.6·10^52 | 0.509 | 1.6·10^42 | 0.465 |

The longest proof now has 471 steps and more than 10^652 orderings. Every
decision of the earlier experiments stands except one:

- H10r, H12r, H13r, H20r, and H21r hold and H11r fails (0.509 at 51 steps and
  more), as before;
- **H28r holds, where H28 did not**: adjusted for length, the golfed proof
  branches more than its predecessor in 78 of the 122 pairs whose branching
  differs (two-sided p = 0.0027, Holm 0.008). Under the earlier rule the same
  direction had shown, 72 of 120 (p = 0.035, Holm 0.11). Depth and width still
  show nothing (Holm 0.70 and 0.23), and the structure index still follows
  length (65 of 136 lower after adjustment, p = 0.73).

## Interpretation boundary

The recount changes the derivation, not the extractions, so it inherits their
boundaries. H28r was registered knowing H28's result under the earlier rule,
including the direction and size of the branching difference.
