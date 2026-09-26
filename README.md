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
of orderings (median 9.3·10^13 at 21 to 50 steps, more than 10^652 for the
longest proof, as recounted under the step derivation that a blind audit
corrected; `experiments/recount-v0.1`), and two disjoint Mathlib slices, whose
proofs are shorter, show the same growth;
but Lean's convention of acting on the first goal already fixes one ordering,
and over every one of the 1,171 theorems of a slice that can be posed, 4.5
percent of a real search's expansions are states that differ from an earlier
one only in goal order. What the search does meet is goal sharing: 14.9
percent of its expansions, and 28.0 percent once goals that differ only in
the names of their hypotheses are identified. Searching over goals instead of
whole states proves neither more nor fewer theorems (103 against 102, sign
test p = 1), at eight times the budget, or with the menu's one-shot provers
removed, where neither search proves anything at all; and a goal search that
treats goals as independent loses proofs whose goals share an existential
witness (HyperTree Proof Search and Aesop handle such goals explicitly; ours
deliberately does not). Mathlib's
golfed proofs are shorter than their predecessors and, adjusted for length,
branch more, on two windows of Mathlib's history; the structure index, which
this program proposed as a quality measure, separates the two proofs on one
window and not on the other, so it does not survive replication. Each experiment's README carries its
numbers and its boundaries;
[docs/design.md](docs/design.md) states the answer in full.
[HANDOFF.md](HANDOFF.md) maps every claim to the command that re-verifies
it and lists where an independent cross-check is most valuable.

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
scripts/run_search_wide.py        the same searches on every candidate theorem
scripts/search_keys.py            the searches recording three goal identities
scripts/run_search_keys.py        goal identity, and a menu without hammers
scripts/run_orderings_replay.py   replaying a graph's orderings in Lean
scripts/run_holdout.py            a second, disjoint Mathlib slice
scripts/mine_golf.py              golf pairs from Mathlib's history
scripts/run_golf.py               golfed proofs against their predecessors
scripts/run_golf_structure.py     depth, width, and branching of golf pairs
scripts/run_golf_replication.py   the golf findings on an earlier window
scripts/run_extraction_audit.py   derived graphs against blind reconstructions
scripts/count_linearizations_v2.py the step derivation the audit corrected
scripts/run_recount.py            every extraction under the corrected rule
scripts/export_graphs.py          the dataset of step-dependency graphs
scripts/audit_graphs.py           structural invariants of every derived graph
scripts/check_slice_options.py    the slice's graphs under Mathlib's options
fixtures/Fixtures.lean            hand-checkable proofs
experiments/linearizations-v0.1/  step 1 artifacts
experiments/linearizations-mathlib-v0.1/  the Mathlib slice
experiments/search-v0.1/          steps 2 and 3 artifacts
experiments/search-v0.2/          the deeper searches
experiments/search-v0.3/          every candidate theorem
experiments/search-v0.4/          goal identity, and no one-shot provers
experiments/orderings-replay-v0.1/  orderings replayed as Lean scripts
experiments/holdout-v0.1/         the second slice
experiments/golf-v0.1/            golf pairs (Mathlib excerpts, Apache-2.0)
experiments/golf-structure-v0.1/  depth, width, branching
experiments/golf-v0.2/            the same tests on an earlier window
experiments/extraction-audit-v0.1/  the blind reconstruction
experiments/recount-v0.1/         the corrected counts
datasets/proof-graphs-v0.2.jsonl.gz  7,285 step-dependency graphs (corrected derivation)
datasets/proof-graphs-v0.1.jsonl.gz  the same graphs under the earlier derivation
```

## Dataset

`datasets/proof-graphs-v0.2.jsonl.gz` holds the step-dependency graph of
every proof the experiments extracted, under the corrected derivation of
`scripts/count_linearizations_v2.py` (`python scripts/run_recount.py
--check-committed` rebuilds it); `proof-graphs-v0.1` keeps the earlier
derivation, which loses the closing steps of `simpa ... using ...` and similar
tactics. Both cover 3,994 tactic proofs of ProofNet-IR
v0.10.0, 2,807 of the Mathlib v4.32.0 slice, and the 484 tactic sides of the
golf pairs, one JSON line each with its source, module, declaration, steps
(tactic kind and line), dependency edges, and exact number of orderings.
`python scripts/export_graphs.py --check` rebuilds v0.1 from the committed
extractions; CI runs both checks.

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
