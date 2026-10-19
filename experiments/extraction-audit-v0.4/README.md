# Extraction audit v0.4

Does a person, rebuilding goal-origin graphs by hand from the source and Lean's goal display, agree with the
corrected step derivation (`scripts/count_linearizations_v2.py`)? extraction-audit-v0.1 to v0.3 compared the
derivation with reconstructions by language-model agents. Two reviews of the paper (2026-10-18) asked for a short
audit by a person, of difficult syntax and of very long proofs. Among the proofs no earlier audit sampled, this
audit draws two proofs of 5 to 30 steps for each of six constructs (`simpa ... using`; a `by` nested in a term; case
analysis by `induction`, `cases`, `rcases` or `obtain`; `calc`; `<;>`, `all_goals` or `any_goals`; and `try`,
`first` or `repeat` written in the proof), and, in each of three proofs of more than 150 steps, a window of 25
consecutive steps, given as a range of lines. Seed 20261018.

The reconstructor is a person, a co-author of the paper, who receives the bilingual kit in `human-kit/`
(English and Chinese): each item's location and line range, without its construct, size or shape. The
reconstructor works from the source and from the goals Lean displays, may read Lean's and Mathlib's source, does not
open the repository's extractions, datasets, results or scripts or run its extractor, and reconstructs without help
from a language model. A window's reconstruction gives the steps on the window's lines, the edges between them, and
which of them consume a goal created by a step outside the window.

## Artifacts

- `preregistration.json`, `sample.json`: the sample rule, the protocol, hypothesis H127, check C58, and the hashes of
  the kit and the implementation, registered before the kit was handed over;
- `human-kit/README.md`, `human-kit/instructions.md`: the bilingual guide and definition, with two worked examples
  from `fixtures/Fixtures.lean`;
- `human-kit/worksheet.md`, `human-kit/answers.xlsx`: the 15 items with their source, and the answer workbook, one
  sheet per item.

When the filled workbook comes back, `--import-hand` converts it to `reconstructions-by-hand.json`, which is
committed before `--compare` first runs; every disagreement is then adjudicated with Lean's info tree and goal
display as an extractor error, a reconstruction error, or a gap in the definition. H127 predicts that none is an
extractor error.

## Reproduction

```text
python scripts/run_extraction_audit_v4.py --dev
python scripts/run_extraction_audit_v4.py --check-committed
```

run the comparison on extraction-audit-v0.3's committed reconstructions and on a window of its longest proof, and a
round trip through the answer workbook; and verify the hashes and C58 (and, once the reconstructions are in, the
comparison); CI runs the second.

## Status

Registered; the reconstructions are awaited.
