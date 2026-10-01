# goal-selection-diagnostic-v0.1: constructed coupled and independent tasks

Eighteen constructed tasks, each a statement and a fixed prefix posed in a full-Mathlib REPL, searched by the
four arms of goal-selection-v0.1 (`firstText`, `first`, `any`, `anyMultiset`; 24 expansions, the 26-tactic
menu). In the ten coupled tasks the prefix leaves the witness goals first and the equations that pin them
last, for example `∃ n : ℕ, n ^ 2 = 16 ∧ n = 4` after `refine ⟨?_, ?_, ?_⟩` leaves `ℕ`, `?n ^ 2 = 16`,
`?n = 4`; two of them have two witnesses. In the eight independent tasks the goals share no metavariable.
The tasks and four predictions were registered before the run; the four constructed tasks used in
development are not among them.

## Artifacts

- `preregistration.json`: the tasks, the predictions D1 to D4, and the implementation hashes;
- `results.jsonl`: the 72 units (18 tasks by four arms), each with its search record and, for proofs found by
  the typed arms, the step-by-step coupling replay;
- `summary.json` and `report.md`: outcomes per task and arm, and the predictions decided.

## Reproduction

```text
python scripts/run_goal_selection_diagnostic.py --check-committed
```

recomputes the summary and report from the rows; CI runs it. `--run` reruns the units (Mathlib REPLs, about
fifteen minutes on six workers).

## Outcome

- D1 holds: neither first-goal arm proves a coupled task; each spends all 24 expansions (624 applications).
- D3 holds: both free-choice arms prove the eight one-witness tasks, all with `pick_goal 3; rfl; simp`,
  closing the pinning equation first so that it assigns the witness. The replay of each of the 16 proofs
  shows that choice acting on a goal coupled to the others. `any` takes 11 expansions and 703
  applications (12 and 781 on one task), `anyMultiset` 10 and 625 (11 and 703): the order quotient saves an
  expansion.
- D2 fails: neither free-choice arm proves the two two-witness tasks within the budget (2,860 and 2,756
  applications). Their root state has five goals, so an expansion tries up to 130 applications, and the
  24 expansions run out before depth three.
- D4 holds: every arm proves all eight independent tasks, `first` in two expansions (27 applications) except
  on the three-goal task, where it takes 5 and 105 against 11 and 703 for the free-choice arms.
- Every free-choice proof needs more than 624 applications, so at equal steps no arm proves a coupled task.
