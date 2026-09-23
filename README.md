# proof-graphs

Experiments on the order redundancy of Lean tactic proofs: how many orderings
of its steps a proof admits, how much of a real proof search is spent on
orderings of the same steps, and whether searching over goal-dependency
graphs instead of tactic sequences pays at equal budget. The program is the
Lean-scale continuation of the MLL results of
[ProofNet-IR](https://github.com/fushanbobfan/proofnet-ir) v0.11, and its
corpus is that library's own proofs.

Every experiment is registered before its data exists (`preregistration.json`
in its directory), reported whichever way it comes out, and re-verified in CI
from the committed artifacts. [docs/design.md](docs/design.md) states the
research object, the three steps, and the boundaries.

The program is done. A proof's step-dependency graph admits enormous numbers
of orderings (median 8.8·10^13 at 21 to 50 steps, 10^628 for the longest
proof), and a Mathlib slice gives the same distribution; but Lean's
convention of acting on the first goal already fixes one ordering, and in a
real tactic search only 2 to 4 percent of the expansions are states that
differ from an earlier one only in goal order. Searching over goals instead
of whole states proves no more at equal budget, even at eight times the
budget, and loses proofs whose goals share an existential witness. Mathlib's
golfed proofs are shorter than their predecessors, and their lower structure
index is explained by their length. Each experiment's README carries its
numbers and its boundaries;
[docs/design.md](docs/design.md) states the answer in full.

## Layout

```text
ProofGraphs/Extract.lean          goal-dependency graphs from info trees
ProofGraphsExtract.lean           proof_graph_extract <module> <file> ...
scripts/count_linearizations.py   exact orderings per graph
scripts/run_linearizations.py     step 1: register, run, check
scripts/run_mathlib_slice.py      step 1 on a Mathlib slice
scripts/lean_repl.py              a Lean REPL session
scripts/search_harness.py         whole-state and AND-OR tactic searches
scripts/run_search.py             steps 2 and 3: register, run, check
scripts/run_search_deep.py        the same searches at eight times the budget
scripts/mine_golf.py              golf pairs from Mathlib's history
scripts/run_golf.py               golfed proofs against their predecessors
scripts/export_graphs.py          the dataset of step-dependency graphs
fixtures/Fixtures.lean            hand-checkable proofs
experiments/linearizations-v0.1/  step 1 artifacts
experiments/linearizations-mathlib-v0.1/  the Mathlib slice
experiments/search-v0.1/          steps 2 and 3 artifacts
experiments/search-v0.2/          the deeper searches
experiments/golf-v0.1/            golf pairs (Mathlib excerpts, Apache-2.0)
datasets/proof-graphs-v0.1.jsonl.gz  7,285 step-dependency graphs
```

## Dataset

`datasets/proof-graphs-v0.1.jsonl.gz` holds the step-dependency graph of
every proof the experiments extracted: 3,994 tactic proofs of ProofNet-IR
v0.10.0, 2,807 of the Mathlib v4.32.0 slice, and the 484 tactic sides of the
golf pairs, one JSON line each with its source, module, declaration, steps
(tactic kind and line), dependency edges, and exact number of orderings.
`python scripts/export_graphs.py --check` rebuilds it from the committed
extractions; CI runs it.

## Reproduction

```text
lake build && lake build ProofNetIR
lake exe proof_graph_extract Fixtures fixtures/Fixtures.lean | python scripts/count_linearizations.py
python scripts/run_linearizations.py --check-committed
```

`lake build ProofNetIR` compiles the whole dependency, which the extractor
imports module by module (about ten minutes on CI); `lake exe cache get`
fetches Mathlib's build for the slice and search experiments (about 6 GB);
`lake build repl` builds the Lean REPL the searches drive; the model arm of
the search experiment needs a local OpenAI-compatible server on port 8080. On Windows, clone into a short path or set
`git config --global core.longpaths true`; several module names of the
dependency exceed 100 characters.
