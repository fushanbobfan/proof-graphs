# Goal-selection search v0.1

The new search applies the deterministic menu to every open goal, with either ordered text identity
(`any`) or joint typed unordered identity (`anyMultiset`). The runner supplies the unchanged first-goal
baseline, registration hashes and hypothesis placeholders, resumable units in their original modules,
summary and report reconstruction, paired exact sign tests, and stepwise coupling replay. The experiment
uses search-v0.3's 1,347 candidates and 24 expansions. No experiment artifacts have been created.

Files: `scripts/search_goal_selection.py`, `scripts/run_search_goal_selection.py`,
`scripts/test_goal_selection.py`, and this note.

## Interpretations

- Applications visit goal positions in ascending order, then menu candidates in menu order. A position's
  `pick_goal` is run with `search_faithful.harness_step` from the original parent and reused for its
  candidate trials; proof scripts contain the pick and candidate as separate lines.
- `steps` counts actual candidate applications, including failed tactics and rejected closures. Picks,
  exports, verification, and control prefixes are excluded. A closing expansion stops early, so its steps
  can be smaller than candidates times goals. `stepsAtProof` includes the accepted closing application.
- `exactDuplicates` and `multisetDuplicates` observe valid children's text identities, including children
  discarded by typed identity; the histories include the root. Rejected closures are not valid children.
  `typedDuplicates` separately counts actual typed merges. Text multisets never decide typed merges.
- Typed order duplicates compare unordered typed keys against ordered typed keys. An unavailable
  unordered key also yields `null`, without being an export failure. Failed or wrong-length exports are
  failures; cached failed exports are not counted again. In `anyMultiset`, valid children, including the
  accepted closing child, are exported; expanded states reuse their cached exports.
- The first arm calls `search_harness.whole_state_search` through passive proposer and REPL observers.
  Its module session is unchanged and uses the plain exporter, preserving the baseline environment.
  Free-choice module sessions define the typed tactic once, with the specified plain-export fallback.
  Sessions close the Windows launcher and child process tree. An export that restarts the REPL abandons
  the unit because its proof states and module environment are no longer usable.
- Typed fractions divide by observations with known keys; coupling fractions divide by exported
  multi-goal expansions. Their support counts and export failures are reported. Distinct typed multisets
  are counted within each search and summed across task environments. Pairwise tests use completed
  results in both arms, excluding missing or abandoned units. Both directional exact binomial tails are
  given; no discordances gives `null`. The secondary comparison applies the 624-step cutoff to both
  free-choice arms, without changing the primary searches.
- C1 compares posing, proof-found status, and the full original expansion records (including their
  count), as specified; elapsed times and proof text are not replication criteria. `--smoke-first N`
  selects the first N previously posed tasks, with N at most five, outside registration and execution.
- Development defaults to four named theorems excluded from the entire original slice and candidate
  list, posed with `make_task`; `--dev-count` permits zero to ten. One extra coupled control and one
  extra independent control were added. Prefixes are applied before search and included in verification.
  Probes attach each pick to its candidate and report the original state's positions and groups, both
  1-based. The raw development `rootGroups` retain the identity module's 0-based indices.
- Development, smoke, and coupling outputs require an external `--output-dir` and one worker.
  The future experiment run checks that registration was committed and reached a local remote-tracking
  ref; that check performs no network access. Registration refuses to overwrite existing artifacts;
  implementation amendments follow the existing convention. Hypotheses remain `TO BE WRITTEN`.

## Fast tests

```text
python -B -m unittest discover -s scripts -p "test_*.py"
........................................................................
----------------------------------------------------------------------
Ran 72 tests in 0.282s

OK
```

Includes 32 new fake-REPL and runner tests.

## Lean smoke tests

All commands exited 0, ran serially, and wrote outputs under
`D:/ucla/codex-worktrees/specs/goal-selection-smoke/`. Full stdout is in `self-test.log`, `dev.log`, and
`first.log`; full rows and coupling traces are in the adjacent JSON/JSONL files.

```text
python -B scripts/run_search_goal_selection.py --self-test --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke
{"self-test": {"fastExporterDefined": true, "namedEqualsPlain": true, "independentGroups": true, "first": true, "any": true, "anyMultiset": true, "pickReplay": true}, "ok": true}
```

```text
python -B scripts/run_search_goal_selection.py --dev --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke
```

All 24 units completed, with zero export failures, errors, or abandonments. Output below is
`expansions / steps`; a dash means no proof. All found proofs verified from the statement.

| Task | first | any | anyMultiset | Proof |
| --- | --- | --- | --- | --- |
| Nat.add_assoc | 1 / 3 | 1 / 3 | 1 / 3 | `omega` |
| Nat.mul_assoc | 1 / 10 | 1 / 10 | 1 / 10 | `ring` |
| List.reverse_reverse | 1 / 1 | 1 / 1 | 1 / 1 | `simp` |
| List.map_id | 1 / 1 | 1 / 1 | 1 / 1 | `simp` |
| coupled_square | 24 / 624, dash | 11 / 703 | 10 / 625 | free-choice: `pick_goal 3; rfl; simp` |
| independent_arithmetic | 2 / 27 | 2 / 53 | 2 / 53 | `simp; simp` |
| coupled_sum | 24 / 624, dash | 11 / 703 | 10 / 625 | free-choice: `pick_goal 3; rfl; simp` |
| independent_true | 2 / 27 | 2 / 53 | 2 / 53 | `simp; simp` |

The two coupled controls start with the witness first after `refine ⟨?_, ?_, ?_⟩`:
`∃ n : ℕ, n * n = 9 ∧ n = 3` and `∃ n : ℕ, n + n = 6 ∧ n = 3`.
The independent controls start after `refine ⟨?_, ?_⟩`: `2 + 2 = 4 ∧ 3 * 3 = 9` and `True ∧ True`.
Neither control was tuned. Both free-choice proofs in each coupled control select goal 3 while the
typed groups are `[[1, 2, 3]]`; the chosen goal is coupled. The subsequent `simp` acts on an independent
remaining goal, with groups `[[1]]`. Every replay closes. Both independent controls have singleton groups.
The coupled successes meet the primary expansion budget but **neither free-choice arm meets the
secondary 624-step cutoff** on either control (703 and 625 steps respectively).

```text
python -B scripts/run_search_goal_selection.py --smoke-first 5 --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke
```

All five tasks posed, each with three expansions, 78 steps, no proof, and zero export failures:
`AddConstMapClass.map_const_add`, `AddConstMapClass.map_nsmul_add`,
`AddConstMapClass.map_sub_nsmul`, `AddConstMapClass.map_add_int'`, and
`AddConstMapClass.map_sub_int'`.

```text
{"first-replication": {"compared": 5, "matched": 5, "mismatches": []}}
```

## Boundaries

Registration, the corpus run, and committed-result check/coupling modes were not executed, as required;
there are no goal-selection experiment rows to check or probe yet. Coupling replay was exercised by
the development proofs and self-test. Only five candidate tasks received a fresh baseline search;
the other 1,342 were not rerun. Development outcomes do not establish corpus-level results.
No build, package update, cache command, model server, push, or external contact was used.
All 226 pre-existing tracked files retain their original SHA-256 byte hashes. New files use LF.
No Lake or REPL processes remain after the checks.
