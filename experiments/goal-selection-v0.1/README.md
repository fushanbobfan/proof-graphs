# First goal against free goal choice (goal-selection v0.1)

Every search so far acts on the first open goal. Goal-local steps on goals that share no metavariable commute
and do not disable each other, so a proof that chooses goals freely can be reordered into one, as long, that
always acts on the first goal: the convention should lose no proof except through coupling, and choosing goals
freely should bring back the order redundancy that focusing removes in MLL. No search that could choose goals
had been run. This experiment runs three, on search-v0.3's 1,347 candidate theorems with its 26-tactic menu
and 24 expansions.

## Four arms

The searched arms identify states by the typed expression key of `scripts/goal_identity_typed.py`
(`scripts/search_goal_selection.py`), so that each pair differs in one respect:

- `first`: candidates applied to the first goal; states identified by the ordered key;
- `any`: every candidate applied to every open goal, a later goal selected with `pick_goal`; ordered key;
- `anyMultiset`: as `any`, states identified up to goal order and joint renaming (the unordered key).

`firstText`, search-v0.3's whole-state search unchanged (text keys, no exports), runs on a registered sample of
200 tasks, every task search-v0.3 proved and a seeded draw of the rest, to check that the environment reproduces
search-v0.3 (C1). The searched arms also stop after 7,200 seconds of search; a second REPL-timeout abandonment of
a unit is final. H78 (`first` proves more than `any`) and H80 (`anyMultiset` more than `any`) are one-sided
sign tests on the tasks completed in both arms; H81 (`any` has the larger share of expansions that are typed
order duplicates) is a bootstrap over tasks; the three are decided together by Holm's procedure at 0.05. H79
(every theorem proved only by a free-choice arm owes it to a coupled non-first choice) is decided from the
replays of those proofs. C2 checks that `anyMultiset` expands no order duplicate, C3 that exports fail on at
most 3% of attempts. Constructed coupled and independent tasks are registered separately as
goal-selection-diagnostic-v0.1.

## Artifacts

- `preregistration.json`, `tasks.json`: the arms, the sample, the hypotheses and checks, the implementation
  hashes;
- `amendment-1.json`: `pick_goal` defined where a task's module lacks it, and the rerun of the 20 units it
  had stopped;
- `results.jsonl`: one row per task and arm (4,241), with the search's expansion records;
- `coupling.json`: the replays of the free-choice-only proofs (none);
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_goal_selection.py --check-committed
python scripts/test_goal_selection.py
```

The first recomputes the summary and report from the committed rows; the second tests the search and its
decisions on a fake REPL. CI runs both. `--run` resumes the searches (a Mathlib REPL per worker; about
22 hours on six, then three, workers).

## The run

The run started on 2026-10-01 at 00:46 with six workers. At 16:22 another job started a local model server
holding 21.6 GB, the Windows commit limit came within 1 GB, and the runner was stopped with its results intact
and resumed at 16:25 with three workers; it finished at 22:26. In 20 units, the free-choice searches of ten
tasks in Mathlib.Logic.Nontrivial.Defs, Mathlib.Combinatorics.Quiver.Path and Mathlib.Data.Sigma.Basic, every
`pick_goal` failed with "unknown tactic": Batteries defines it, and these modules do not import it. Amendment 1,
whose code was committed before the first pass ended, defines `pick_goal` with Batteries' semantics where it is
missing and reruns those units; the first pass's rows were committed unchanged before the rerun, and all 20
units then completed, none with a proof. Two units
abandoned once by a REPL timeout completed on their rerun. No search reached the time limit, and none of the
292,200 exports failed.

## Outcome

| Arm | Posed | Proved | Expansions | Candidate applications | Typed order duplicates |
| --- | ---: | ---: | ---: | ---: | ---: |
| `first` | 1,171 | 103 | 15,831 | 409,860 | 4.5% |
| `any` | 1,171 | 98 | 16,851 | 770,864 | 7.7% |
| `anyMultiset` | 1,171 | 98 | 16,649 | 739,378 | 0% |

**H81 holds; H78, H79 and H80 do not.**

- Free goal choice proves no theorem that the first-goal search misses. The first-goal search proves five
  that both free-choice searches miss, each at depth four or five after 18 to 23 expansions, a depth the
  wider searches do not reach in 24: 5 against 0, one-sided p = 0.031, above Holm's threshold of 0.025 (H78).
- With no free-choice-only proof there is nothing to replay, and H79 is untested; the constructed diagnostic
  shows the mechanism it names.
- Free choice brings back order redundancy: 7.7% of `any`'s expansions are typed order duplicates against
  4.5% of `first`'s, a difference of 3.2 points (95% interval 2.6 to 3.9, p < 0.001; H81). The order quotient
  removes all of them (C2) but proves exactly the theorems `any` proves (H80 has no discordant task).
- 28% to 30% of the exported multi-goal states each arm expanded have goals coupled by a metavariable; none of
  the free-choice searches turned that into a proof the first-goal search lacked.
- C1 holds: all 200 sample units reproduce search-v0.3. On the sample the typed identity costs the first-goal
  search one theorem: `firstText` proves `QuadraticAlgebra.mul_C_eq_smul` in 18 expansions, and `first` does not
  within 24.
- The comparisons at equal candidate applications are the same: no proof used more than 588 applications, and
  no free-choice proof more than 354.
