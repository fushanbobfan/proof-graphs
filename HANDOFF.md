# Handoff

2026-09-22. The project passes from Bob to Rowling, who will investigate and
cross-check it (with Codex) and carry it forward. It came back on 2026-09-24
with one ProofNet-IR commit, `34cd793`, a trust gate over every compiled
library declaration; the cross-check priorities below were not taken up and
remain open. Two public repositories:

- [ProofNet-IR](https://github.com/fushanbobfan/proofnet-ir): the Lean 4
  library for MLL proof nets (stable release `v0.10.0`, `main` is
  `v0.11.0-dev`) and the three preregistered MLL experiments of its v0.11
  program. Its own entry points are `docs/current-status.md`,
  `docs/goal-ledger.md`, and `CONTRIBUTING.md`.
- proof-graphs (this repository): the same founding question at Lean's
  scale, five preregistered experiments and a dataset. The answer is stated
  in [docs/design.md](docs/design.md), "Where this ends".

Everything the conclusions rest on is committed and re-verified by CI on
every push; nothing needed for verification lives outside the two
repositories. When this file was written, both `main` branches were in sync
with GitHub and green in CI, and neither repository had another branch on
GitHub.

## What is claimed, and where it is checked

| Claim | Evidence | Re-verification (CI runs all of these) |
| --- | --- | --- |
| Tactic proofs admit enormous numbers of step orderings (ProofNet-IR median 8.8·10^13 at 21–50 steps as registered; 9.3·10^13 and a maximum above 10^652 under the corrected derivation) | `experiments/linearizations-v0.1`, `experiments/recount-v0.1` | `python scripts/run_linearizations.py --check-committed`, `python scripts/run_recount.py --check-committed` |
| A systematic Mathlib slice shows the same growth (structure index within 0.1 of the library's) | `experiments/linearizations-mathlib-v0.1` | `python scripts/run_mathlib_slice.py --check-committed` |
| In a real search only 2–4% of expansions are order duplicates; searching over goals proves no more than over states | `experiments/search-v0.1` | `python scripts/run_search.py --check-committed` |
| Eight times the budget adds goal sharing (to ~18%) but no proof; goals that share an existential witness defeat a goal search that treats goals as independent (HTPS and Aesop handle them explicitly) | `experiments/search-v0.2` | `python scripts/run_search_deep.py --check-committed` |
| Mathlib's golfed proofs are shorter; their lower structure index is explained by length | `experiments/golf-v0.1` | `python scripts/run_golf.py --check-committed` |
| Adjusted for length, golfed proofs branch more; replicated on 479 unseen pairs, where the structure index does not separate the two proofs at all | `experiments/golf-structure-v0.1`, `experiments/recount-v0.1`, `experiments/golf-v0.2` | `python scripts/run_golf_replication.py --check-committed` |
| The sample's search measures hold on all 1,347 candidate theorems; the two search designs prove 103 and 102 (p = 1) | `experiments/search-v0.3` | `python scripts/run_search_wide.py --check-committed` |
| Goal sharing is 15.9% of expansions by printed text, 28.0% once hypothesis names are normalized; without one-shot provers neither search proves anything | `experiments/search-v0.4` | `python scripts/run_search_keys.py --check-committed` |
| With a step-level prover as proposer no expansion is an order duplicate, and the goal search leads 10 to 8 (p = 0.5) | `experiments/search-v0.5` | `python scripts/run_search_prover.py --check-committed` |
| With the prover's draws shared between the two searches, the lead disappears on the same tasks; over 169 theorems 41 against 39; goal sharing is 4.9% by printed goal and 26.1% up to renaming | `experiments/search-v0.6` | `python scripts/run_search_paired.py --check-committed` |
| Every ordering of 41 small proofs' graphs replays as a Lean script | `experiments/orderings-replay-v0.1` | `python scripts/run_orderings_replay.py --check-committed` |
| A second, disjoint Mathlib slice grows the same way; its 6-to-10-step median is 8, below the first slice's threshold of 10 | `experiments/holdout-v0.1` | `python scripts/run_holdout.py --check-committed` |
| A blind reconstruction of 30 graphs found one extractor defect, since corrected | `experiments/extraction-audit-v0.1` | `python scripts/run_extraction_audit.py --check-committed` |
| 7,285 step-dependency graphs, corrected derivation | `datasets/proof-graphs-v0.2.jsonl.gz` | `python scripts/run_recount.py --check-committed` |
| Every derived graph satisfies the structural invariants below | all three extractions | `python scripts/audit_graphs.py` |

Each experiment directory holds its `preregistration.json` (committed
before any data), `amendment-*.json` (every change made after registration,
with the numbers seen before it), the raw artifacts, and a README with the
outcome and its boundary. The commit history shows the order of events.

What the checks do and do not cover: they recount every committed graph,
re-extract a small sample of modules and compare node shapes, recompute
every summary from the committed rows, re-run one deterministic search for a
few expansions, and verify all artifact hashes. They do not re-run the full
extractions (16 to 50 minutes each), the searches (3 to 7 hours), or the
model arms, which need a local model server.

## Setup

```text
lake build && lake build ProofNetIR   # the extractor and its dependency (about 10 minutes)
lake exe cache get                    # Mathlib's build, about 6 GB
lake build repl                       # the Lean REPL the searches drive
python scripts/<runner>.py --check-committed
```

Lean `v4.32.0` (pinned), Python 3.12 or later. The model arm of the search
experiments calls an OpenAI-compatible server at `127.0.0.1:8080`; the runs
used Qwen3.6-35B-A3B (Q4) through llama.cpp, recorded by model id in the
committed call logs. On Windows, set `git config --global core.longpaths
true`, and beware `core.autocrlf`: a CRLF checkout of Mathlib silently broke
text splicing once (golf amendment 1); the golf runner now reads module text
with `git show`.

## Where a cross-check is most valuable

In order of what an independent pass would most likely catch:

1. **The step derivation** (`scripts/count_linearizations.py`,
   `derive_steps`). It turns Lean's info trees into step graphs and is the
   most amended component (amendments 1, 2, and 4 of `linearizations-v0.1`),
   each fix prompted by an invariant the output violated.
   `scripts/audit_graphs.py` checks those invariants over every committed
   extraction: one `by` block has one root step, a root step consumes only
   goals of the statement, no goal is consumed or originated twice, and
   exact counts match brute force on every graph of 2 to 7 steps (7,285
   graphs, 3,299 brute-forced, no violation). An invariant cannot catch a
   derivation that is consistently wrong: `extraction-audit-v0.1` had two
   model agents rebuild 30 random graphs blind, found one systematic defect
   (closings of `simpa ... using ...` and similar tactics lost), and
   `recount-v0.1` corrects it (`scripts/count_linearizations_v2.py`; all 30
   then agree). A person's reconstruction of a subsample is still the
   strongest check. Constructs worth a look: `first`/`try`/`repeat`
   (Lean keeps the info nodes of failed alternatives), `<;>`, `calc`, `conv`,
   `case`/`next`, `rcases`/`obtain` patterns, `induction ... with`,
   `simpa ... using (by ...)`.
2. **Goal identity in the search harness** (`scripts/search_harness.py`).
   Goals are compared as pretty-printed text, with case tags and
   metavariable numbers erased. Two goals that print alike but differ
   internally would be merged, and the entanglement check compares printed
   carried goals. An independent implementation keyed on goal types up to
   definitional equality would test both duplicate fractions.
3. **Options.** The slice and both search experiments elaborated under
   Lean's default options, not Mathlib's (`autoImplicit false`,
   `maxSynthPendingDepth 3`); golf inserts Mathlib's. For the slice this is
   now checked: re-extracted with Mathlib's options, all 2,784 distinct
   declarations keep identical graphs
   (`scripts/check_slice_options.py`). The searches ran their tactics
   through the REPL under the defaults, which that check does not cover.
4. **Golf mining** (`scripts/mine_golf.py`). Declarations are found by
   regular expression and statements compared as whitespace-normalized
   text; 12 of 306 pairs are excluded. An independent miner using Lean's
   declaration ranges would test the pair set. The length adjustment behind
   "it is length" is exploratory (slice medians per step count); a
   registered, length-matched test is the natural follow-up.
5. **Small samples.** The searches ran on 40 and 20 theorems with a weak
   proposer and breadth-first search. The deterministic menu arm reproduced
   bit for bit across runs (search-v0.2, check C1, 40/40); the model arm
   samples at temperature 0.8 and will not.
6. **ProofNet-IR's formal claims** are kernel-checked: `lake build`, the
   `--trust=0` recheck, and `python scripts/audit_axioms.py` in that
   repository, all in its CI. The one open theorem target, a linear
   whole-program bound (D6-linear), is optional and recorded in its goal
   ledger.

## How the work has been done

- Every experiment is registered before its data exists:
  `preregistration.json` with the corpus, the implementation hashes, and the
  hypotheses, pushed to `main` before the run.
- A registration is never edited. A change after it is an
  `amendment-N.json` that states what was observed, what changed, the
  numbers seen before the change, and the implementation hashes before and
  after; runners take the expected hashes from the latest amendment.
- Negative results are reported as registered, and an exploratory analysis
  is labelled as such next to them.
- Every runner has `--check-committed`, and CI runs it; an experiment is not
  done until CI re-verifies its committed artifacts on Linux.
- History is never rewritten. Commit subjects state the change in one line;
  commits carry no tool or assistant attribution.

## Open directions

From `docs/design.md`, none of them more of the same: a proposer strong
enough that searches run deep (every proof so far was found within a dozen
expansions); the redundancy this design does not touch (different tactic
paths to one goal, different proof terms of one proposition); for the
quality question, a registered test of another graph quantity (depth,
width, branching) or of quantities outside the graph (lemmas used, term
size, elaboration time). Writing the two repositories up together is the
other option on the table.

## Logistics

- Both repositories are public, Rowling has write access to both, and
  `main` has no branch protection.
- Since the handback, Bob's agents push to `main` directly again; if both
  sides work at the same time, agree first on who pushes to `main`.
- Outside the repositories there are only Bob's notes to Rowling (a
  two-month summary, the Beyond-MLL design draft, and its results note),
  which he sends separately. They add context, not evidence.
