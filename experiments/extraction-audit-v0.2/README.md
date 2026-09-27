# Extraction audit v0.2

Does the corrected step derivation (`scripts/count_linearizations_v2.py`)
agree with independent reconstructions on the proofs most likely to break it,
those using the constructs it handles by special rules or that hide goals?
Forty proofs were drawn (seed 20260927), five per family recognised in the
proof's text: `try`/`first`/`repeat`, tactics run on several goals, `calc`,
`conv`, `case`/`next`, `rcases`/`obtain`/`rintro` patterns, alternatives of
`induction`/`cases`/`match`, and nested `by`. All have 2 to 20 steps, none
comes from extraction-audit-v0.1's sample, 27 are from ProofNet-IR and 13
from the Mathlib slice. Four reconstructors, ten proofs each, rebuilt each
graph from the source and Lean's goal display, following `instructions.md`;
the comparison matched steps by source line and compared edges.

## Artifacts

- `preregistration.json`, `sample.json`, `instructions.md`: the sample rule,
  the protocol, the disagreement categories, hypothesis H67, and the text
  every reconstructor received;
- `reconstructions.json`: the forty graphs with the reconstructors' notes,
  committed (`e215f9b`) before the first comparison. The reconstructors are
  four separate language-model agent instances with Lean language-server
  access, not people;
- `results.jsonl`, `summary.json`: the comparison;
- `human-kit/`: the same task for a person, with a worksheet of the proofs'
  sources and `--compare-hand`, which reports agreement without showing the
  derived graphs. No person has done it yet.

## Reproduction

```text
python scripts/run_extraction_audit_v2.py --check-committed
```

recomputes the comparison from the committed reconstructions and extractions;
CI runs it.

## Outcome

All forty graphs agree exactly, steps and edges (387 steps, 3 to 18 per
proof), so nothing needed adjudication: **H67 supported**. The reconstructors
took a step to be a tactic node of Lean's info tree, as the derivation does,
and the derivation matches them wherever that differs from one step per
source tactic: one step per rewrite rule of `rw` (and one for its closing
`rfl` when that closes the goal), one per binder of a multi-binder `intro`,
the node `conv_lhs` and `conv_rhs` insert, the two nodes of
`cases h : e with`, and a named `next` or `case` that renames hypotheses.

The audit also found three defects in its own materials:

- The instructions say that Lean's info tree has one node per tactic
  invocation. It does not, for the cases above. All four reconstructors
  settled the node structure from the Lean toolchain's source and followed
  the info tree; for 19 of the forty proofs they recorded how the graph would
  differ under one step per source tactic.
- A definition gap, in `SourceLeftChain.reachable_of_head_last`: a `by simp`
  nested in the lemma list of a `simpa` whose simp phase changes nothing has
  its goal originate at the `simpa`'s internal node, which consumes nothing,
  so under the definition's rule neither that node nor the nested `simp` is
  live, although the definition's prose presents non-live nodes as failed
  branches. The derivation and the reconstructor both applied the rule; the
  step count is 13 where one step per source tactic would give 14.
- The family patterns match identifiers: `try`/`first`/`repeat` matched a
  variable or field named `first` in all five of its proofs, and
  `case`/`next` matched a line starting with the identifier `next` in one of
  its five. So 34 of the forty proofs use their family's construct, and no
  proof in the sample uses `try`, `first`, or `repeat`.

## Interpretation boundary

The reconstructors are model agents; a person's reconstruction with
`human-kit/` remains the stronger check. The sample is forty proofs of at most
20 steps, with `try`, `first`, and `repeat` not covered. A cross-check with
LeanTree was not done: it pins Lean v4.27.0 and its own REPL fork, against
this project's v4.32.0.
