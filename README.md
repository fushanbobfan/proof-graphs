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
removed, where neither search proves anything at all. With a step-level Lean
prover (BFS-Prover-V2-7B) as the proposer, searches run deep and the depth
pays and order duplicates all but vanish; the goal search first led by 10
theorems to 8, but with the prover's draws shared between the two searches the
lead disappears on the same tasks, and over 169 theorems the two prove 41 and
39. Most of the goal sharing such a search meets is between goals alike up to
the names of their hypotheses; identifying goals and states up to those names
lets both searches find their proofs about a fifth sooner and prove a few more
(43 and 42), but the search over goals still does no better than the search
over states. Identified by Lean's expressions instead of text, the sharing
measures hold in aggregate, though item by item about one text
identification in fifteen joins goals whose expressions differ. A goal search that treats goals as
independent also loses proofs whose goals share an existential witness.
Kept together in the groups their shared metavariables make, as HyperTree
Proof Search splits states, such goals arise in a quarter of the searches
and decide one proof: over three sets of draws the group search proves 122
of 474 task-sets against 121 for goals and 116 for whole states, no pair
significant after Holm's adjustment. Mathlib's
golfed proofs are shorter than their predecessors and, adjusted for length,
branch more, on two windows of Mathlib's history; the structure index, which
this program proposed as a quality measure, separates the two proofs on one
window and not on the other, so it does not survive replication. Each experiment's README carries its
numbers and its boundaries;
[docs/design.md](docs/design.md) states the answer in full.
[HANDOFF.md](HANDOFF.md) maps every claim to the command that re-verifies
it and lists where an independent cross-check is most valuable.
[docs/heartbeat-limit.md](docs/heartbeat-limit.md) corrects the per-tactic
heartbeat limit the search registrations state; enforced, it changes no outcome
of search-v0.3's searches (heartbeats-v0.1).

## Layout

```text
ProofGraphs/Extract.lean          goal-dependency graphs from info trees
ProofGraphs/FirstGoal.lean        first-goal completeness, for goals that are values
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
scripts/step_prover.py            a step-level Lean prover as a proposer
scripts/run_search_prover.py      both searches with that proposer
scripts/common_draws.py           the proposer's draws shared by two searches
scripts/run_search_paired.py      both searches with shared draws
scripts/renaming.py               the step that renames one goal into another
scripts/search_renaming.py        both searches up to renaming
scripts/run_search_renaming.py    the four searches, seeded with v0.6's draws
scripts/test_renaming.py          the renaming step on printed goals
scripts/check_renaming_repl.py    the renaming searches in a Mathlib REPL
scripts/audit_goal_keys.py        the text keys audited on the logged goals
scripts/goal_identity.py          goal identity from Lean's expressions
scripts/goal_identity_typed.py    the same on typed expression trees, states up to goal order
scripts/test_goal_identity_typed.py the typed identity on synthetic trees
scripts/check_identity_v2_repl.py the typed identity on adversarial goals in a Mathlib REPL
scripts/audit_key_denominators.py keys-v0.1's shares on matched support (not registered)
scripts/test_audit_key_denominators.py the audit's denominators on synthetic logs
scripts/search_goal_selection.py  whole-state search acting on any open goal
scripts/run_search_goal_selection.py first goal against free goal choice
scripts/test_goal_selection.py    the search and its decisions on a fake REPL
scripts/run_goal_selection_diagnostic.py the same on constructed coupled and independent tasks
scripts/test_goal_selection_diagnostic.py the diagnostic's decisions on synthetic rows
scripts/recording_repl.py         a REPL session that records what a search does
scripts/run_key_replay.py         finished searches re-keyed by Lean expressions
scripts/search_faithful.py        searches over states, goals, and coupled goal groups
scripts/run_search_coupled.py     the three, over three sets of draws
scripts/run_search_coupled_deep.py states and groups at 256 expansions
scripts/explore_range_rerun_v08.py  its eleven setup failures rerun (not registered)
scripts/run_orderings_replay.py   replaying a graph's orderings in Lean
scripts/check_coupled_orderings.py a proof its sample rule admits whose other ordering fails
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
scripts/goal_identity.py          goal identity from Lean's expressions
scripts/recording_repl.py         a REPL session that logs a search for re-keying
scripts/run_key_replay.py         finished searches re-keyed by expressions
scripts/goal_defeq.py             goal identity up to definitional equality
scripts/run_defeq_replay.py       the replays merged up to definitional equality
scripts/defeq_v01_amendment.py    its amendment's analyses beside the registered ones
scripts/defeq_v01_c32_mechanism.py why its replay check fails (not registered)
scripts/explore_defeq_merges.py   what its merges bridge (not registered)
scripts/check_tactic_heartbeats.py what a heartbeat limit set inside a tactic bounds
scripts/explore_false_merges.py   what the text keys conflate (not registered)
scripts/run_extraction_audit_v2.py the audit on the constructs the derivation handles by rule
scripts/run_extraction_audit_v3.py the audit on long proofs and graphs that are not forests
fixtures/Fixtures.lean            hand-checkable proofs
fixtures/Coupled.lean             a proof whose goals share a metavariable
experiments/linearizations-v0.1/  step 1 artifacts
experiments/linearizations-mathlib-v0.1/  the Mathlib slice
experiments/search-v0.1/          steps 2 and 3 artifacts
experiments/search-v0.2/          the deeper searches
experiments/search-v0.3/          every candidate theorem
experiments/search-v0.4/          goal identity, and no one-shot provers
experiments/search-v0.5/          a step-level prover as the proposer
experiments/search-v0.6/          the same, with shared draws
experiments/search-v0.7/          goals and states up to renaming
experiments/search-v0.8/          states, goals, and coupled goal groups
experiments/search-v0.8-range-rerun/  its eleven setup failures rerun (not registered)
experiments/search-v0.9/          states and coupled groups at 256 expansions
experiments/goal-key-audit/       the keys' collisions, measured (not registered)
experiments/orderings-replay-v0.1/  orderings replayed as Lean scripts
experiments/holdout-v0.1/         the second slice
experiments/golf-v0.1/            golf pairs (Mathlib excerpts, Apache-2.0)
experiments/golf-structure-v0.1/  depth, width, branching
experiments/golf-v0.2/            the same tests on an earlier window
experiments/extraction-audit-v0.1/  the blind reconstruction
experiments/extraction-audit-v0.2/  the same on hard constructs, with a kit for people
experiments/extraction-audit-v0.3/  the same on long proofs and non-forest graphs
experiments/keys-v0.1/            finished searches re-keyed by Lean expressions
experiments/keys-v0.1-conflations/  what the text keys conflate (not registered)
experiments/keys-v0.1-matched-support/  its shares on matched support (not registered)
experiments/defeq-v0.1/           the whole-state replays up to definitional equality
experiments/defeq-v0.1-merges/    what its merges bridge (not registered)
experiments/goal-selection-v0.1/  first goal against free goal choice, and the order quotient
experiments/goal-selection-diagnostic-v0.1/  the same on constructed tasks
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
