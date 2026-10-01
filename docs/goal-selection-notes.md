# Goal-selection search

Lean's tactic searches act on the first open goal. Goal-local steps on goals that share no metavariable
commute and do not disable each other, so the convention should lose no proof except through coupling, and
choosing goals freely should bring back the order redundancy that focusing removes in MLL. These experiments
measure both claims:

| MLL | Lean |
|---|---|
| unfocused sequent search meets the factorial | `any`: every candidate applied to every open goal |
| focusing fixes the order | `first`: candidates applied to the first goal only |
| nets quotient the order | `anyMultiset`: as `any`, states identified up to goal order |

## goal-selection-v0.1 (`scripts/run_search_goal_selection.py`)

- **Tasks and proposer.** search-v0.3's 1,347 candidates (1,171 posable), each posed in its own module in a
  fresh REPL; the deterministic 26-tactic menu.
- **Arms.** `first`, `any` and `anyMultiset` run `search_goal_selection.any_goal_search` and identify states
  by `goal_identity_typed`: `first` and `any` by the ordered key, `anyMultiset` by the unordered key, so each
  pairwise contrast changes one thing. `firstText` is search-v0.3's search unchanged (text keys, no exports),
  run on a 200-task sample (every task search-v0.3 proved, plus a seeded draw) to check that the environment
  reproduces search-v0.3 (C1).
- **Search.** Breadth-first over whole states. Expanding a state applies every candidate at every goal
  position the arm allows, positions in ascending order and candidates in menu order; a non-first position
  is selected with `pick_goal` once per position. A child whose export fails, or whose key is `None`, is
  never merged. Found proofs keep `pick_goal` as separate lines and are verified from the statement.
- **Budget.** 24 expansions; the typed arms also stop after 7,200 seconds of search, checked before each
  expansion and goal position (a stopped search is a completed search without a proof). `steps` counts
  candidate applications; `stepsAtProof` counts them up to the closing one. The secondary comparison counts a
  proof only within 624 applications, the most the first-goal search can spend.
- **Failures.** A REPL timeout abandons the unit; the next run retries it, and a second abandonment is final
  and excluded from the paired comparisons.
- **Decisions.** H78 (`first` proves more than `any`), H80 (`anyMultiset` more than `any`), and H81 (`any`
  has the larger share of typed order duplicates, by a bootstrap over tasks) are decided at 0.05 after
  Holm's adjustment. H79 (every theorem proved only by a free-choice arm owes it to a coupled non-first
  choice) is decided from `--coupling`, which replays those proofs and commits `coupling.json`. Checks: C1;
  C2 (`anyMultiset` expands no typed order duplicate); C3 (exports fail on at most 3% of attempts).

## goal-selection-diagnostic-v0.1 (`scripts/run_goal_selection_diagnostic.py`)

Eighteen constructed tasks, each a statement and a fixed prefix posed in a full-Mathlib REPL, searched by
the same four arms. In the ten coupled tasks the prefix leaves the witness goals first and the equations
that pin them last (for example `∃ n : ℕ, n ^ 2 = 16 ∧ n = 4` after `refine ⟨?_, ?_, ?_⟩`); in the eight
independent ones the goals share no metavariable. Predictions D1 to D4: no first-goal arm proves a coupled
task; both free-choice arms prove every coupled task; every such proof makes a coupled non-first choice; and
`first` proves every independent task any arm proves.

Four other constructed tasks were run during development: on the two coupled ones both first-goal arms
failed within the 24 expansions and both free-choice arms proved them by `pick_goal 3; rfl; simp`, in 703
and 625 applications; the two independent ones every arm proved in two expansions.

## Modes and tests

`--self-test`, `--dev`, `--dev-holdout N` and `--smoke-first N` write outside the repository (`--output-dir`)
with one worker; `--register`, `--run [--workers W]`, `--coupling` and `--check-committed` work on the
experiment folder, and `--run` requires the registration to be committed and pushed.

    python -B scripts/test_goal_selection.py
    python -B scripts/test_goal_selection_diagnostic.py
