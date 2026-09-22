# Golf v0.1

The third layer of the original proposal, telling good proofs from mediocre
ones, tested with the only large, independent judgment of proof quality
available: Mathlib's golf commits. A golf commit is a pull request whose
declared purpose is to shorten or simplify proofs, merged after review. Each
proof it replaces gives a pair: a proof and the proof the community accepted
as better, of the same statement. The proposal's candidate measure was the
structure index of the goal-dependency graph, `log L / log n!`: fewer
orderings relative to `n!` would mean a more structured proof.

## Artifacts

- `preregistration.json` and `pairs.jsonl.gz`: the window (Mathlib v4.29.0
  to v4.32.0), the mining rule (`scripts/mine_golf.py`), the 306 pairs from
  108 golf commits with both proof texts (Mathlib excerpts, Apache-2.0), the
  extractor and counter hashes, and hypotheses H20 and H21; committed on
  `main` before any pair was elaborated;
- `amendment-1.json`, `amendment-2.json`: two defects of the runner and what
  was seen before each fix. Line endings made the splice a no-op for every
  multi-line proof, and some modules needed Mathlib's own elaboration
  options. Then counts were joined to pairs by a key both sides share, so
  one side's count overwrote the other's. The extraction behind these
  results was made after the first fix and never changed;
- `extraction.jsonl.gz`: for every pair, the extractor's record of each side
  with its diagnostics;
- `results.jsonl`, `summary.json`, `report.md`: per-pair steps,
  linearizations, and structure index on both sides, and the tests.

## Reproduction

```text
lake exe cache get
python scripts/run_golf.py --check-committed
```

recounts every pair from the committed extraction, re-extracts the two
smallest modules on both sides and compares node shapes, and verifies the
hashes; CI runs it. `--run` re-elaborates 194 modules and 306 variants (45
minutes with six workers). Both sides are elaborated from the v4.32.0 text,
with Mathlib's `autoImplicit false` and `maxSynthPendingDepth 3` inserted
after the header, the predecessor spliced in for the golfed proof.

## Outcome

294 pairs from 104 commits elaborate on both sides; 11 predecessors no longer
elaborate at v4.32.0 (they use lemmas that were renamed or removed), and one
unmodified module fails under the extractor.

| | Predecessor | Golfed |
| --- | --- | --- |
| Steps, median (q1, q3) | 11 (4, 20) | 4 (0, 9) |
| Term proofs, no tactic step | 34 | 82 |
| Structure index, median (q1, q3), both at least 3 steps | 0.315 (0.162, 0.398) | 0.236 (0.000, 0.371) |

- **H20 supported**: among the 238 pairs whose step counts differ, the golfed
  proof is shorter in 210 (p = 6×10⁻³⁶). Golfing shortens the graph, not
  only the text: the median proof loses 4.5 steps, and 54 tactic proofs
  become term proofs.
- **H21 supported as registered**: among the 125 pairs with at least 3 steps
  on both sides whose indices differ, the golfed proof has the lower index
  in 86 (p = 1.6×10⁻⁵; 52 of 71 commits, p = 5.6×10⁻⁵).
- **But the effect is length, not structure** (exploratory, not
  registered): the index rises with proof length in both corpora of step 1,
  and it follows the length change here. It falls in 83 of the
  111 pairs whose golfed proof is shorter, and rises in 11 of the 14 whose
  golfed proof is longer. No pair of equal length changed its index: all 56
  equal-length golfs keep the ordering count exactly, so as far as the graph
  can tell they reword tactics and nothing else. Measured against the Mathlib
  slice's median index at the same length, golfed proofs and their
  predecessors do not differ (70 of 136 lower, p = 0.40).

So the proposal's candidate does not tell a better proof from a worse one
beyond telling a shorter proof from a longer one. What golfing changes, as
the graph sees it, is how many steps there are, not how they depend on each
other.

## Interpretation boundary

A golf is one notion of quality among several (shorter, faster, more
robust, more idiomatic), and a reviewer accepts it as better on balance,
not on structure. The length adjustment uses the slice's medians and is a
post-hoc check, stated as such. Pairs whose predecessor no longer elaborates
are excluded, which removes the golfs that deleted the lemmas their
predecessors used. Other graph quantities (depth, width, branching) were
not registered and are not tested here; they are in the dataset
(`datasets/proof-graphs-v0.1.jsonl.gz`) for whoever wants to register them.
