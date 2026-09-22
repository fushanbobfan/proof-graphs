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
fixtures/Fixtures.lean            hand-checkable proofs
experiments/linearizations-v0.1/  step 1 artifacts
experiments/linearizations-mathlib-v0.1/  the Mathlib slice
experiments/search-v0.1/          steps 2 and 3 artifacts
```

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
