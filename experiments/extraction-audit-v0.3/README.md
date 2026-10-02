# Extraction audit v0.3

Does the corrected step derivation (`scripts/count_linearizations_v2.py`) agree with independent
reconstructions on the proofs the earlier audits left out? extraction-audit-v0.1 drew 30 proofs by length and
v0.2 forty by construct, all of 2 to 20 steps. This audit draws, from the library, the first slice, and
holdout-v0.1's second slice, every eligible proof whose graph is not a forest (a step consumes goals of two
origins, and the counts use dynamic programming instead of the hook-length formula), 14 in all, and proofs drawn
at random among the forests of 21 to 50 steps (8) and of 51 to 150 steps (6), seed 20261002. Eligible proofs
have one root `by` block and 2 to 150 steps and are in neither earlier sample. Of the 28, 19 are from the
library, 4 from the first slice, and 5 from the second.

Six reconstructors, four or five proofs each in sample order, rebuilt each graph from the source and Lean's goal
display, following `instructions.md`; they saw each proof's location only, not its stratum. They are separate
language-model agent instances with Lean language-server access, not people. Their outputs went to one folder
outside the repository, and each that finished after another reports not opening the others' files. One of them,
after finishing, also printed Lean's own info tree for copies of its proofs and compared node positions and goal
counts with its graphs, reporting agreement. By their reports, no reconstructor ran the extractor or opened the
repository's extractions, results, datasets, audit files, or scripts. The comparison matches steps by source line and order
within the line, and compares edges.

## Artifacts

- `preregistration.json`, `sample.json`, `instructions.md`: the sample rule, the protocol, hypothesis H82, and
  the text every reconstructor received;
- `reconstructions.json`: the 28 graphs with the reconstructors' notes, committed (`dc116b1`) before the first
  comparison;
- `results.jsonl`, `summary.json`: the comparison;
- `human-kit/`: the same task for a person, with a worksheet of every proof whole and `--compare-hand`. No person
  has done it yet.

## Reproduction

```text
python scripts/run_extraction_audit_v3.py --check-committed
```

recomputes the comparison from the committed reconstructions and extractions; CI runs it.

## Outcome

All 28 graphs agree exactly, steps and edges (1,084 steps, 3 to 138 per proof), so nothing needed adjudication:
**H82 supported**. The ordering counts agree as well; for three of the graphs that are not forests (27, 29 and
95 steps) the dynamic program's limit of 22 steps leaves the count uncomputed on both sides. The reconstructors'
notes record the same conventions the derivation follows where Lean's info tree differs from one step per source
tactic: two nodes for `cases h : e with`, one per rewrite rule, a closing `rfl` of `rw` as a step only when it
closes a goal (placed on the `rw`'s line), a step at a typed `have ... := by` that originates both the inner goal
and the rest of the proof, and one step per binder of a multi-binder `intro`. Where a step's goal was settled by
reading Lean's source rather than seen in the goal display (`use`, `split_ifs`, the second pass of a shared case
body), the notes say so.

The audit leaves out the library's proofs of more than 150 steps (the longest has 471), which no reconstructor
could rebuild by hand reliably, and every audit so far has used model reconstructors, not people.
