# Goal-selection search v0.1

The experiment compares four arms using the fixed 26-candidate menu and a 24-expansion budget:
`firstText` is the unchanged text-key baseline, `first` selects only the first goal with joint typed
ordered identity, `any` selects every goal with that same identity, and `anyMultiset` selects every goal
with joint typed unordered identity. The three typed arms cover all 1,347 candidates. `firstText` covers
only a registered 200-task replication sample; no experiment artifacts have been created.

## Interpretations

- The replication sample contains all 103 tasks proved by search-v0.3's menu/whole search and 97 other
  posed tasks. Remaining tasks are sorted by `(module, declaration)` before
  `random.Random(20260930).sample`; the sorted selected keys and seed are in the registration payload.
  C1 requires the registered task set and compares posing, proof-found status, and every original
  expansion record for all 200 units.
- `firstText` uses `ModuleSession` and `whole_state_search` without exports or observers. Its step count
  is derived afterwards from candidate counts and the closing menu candidate; the original result is
  preserved. Typed and coupling fractions, distinct typed totals, and generated-text-multiset measurements
  unavailable in this arm are null.
- Typed identity exports the root and every valid child, including verified closures. Expanded states
  reuse cached exports. Failed or wrong-length exports are failures; a `None` key is unavailable identity,
  not an export failure. Neither is a merge key. Text keys measure duplicates but never prune typed arms.
- Positions are visited in ascending order, then candidates in menu order. `first` never picks a goal.
  A non-first position's `pick_goal` runs from the parent and is reused for candidate trials; found proofs
  keep picks and candidates as separate lines. Steps count candidate applications, including failures and
  rejected closures, but exclude picks, exports, verification, and control prefixes.
- Search time includes root/child exports, identity computation, proposals, picks, and verification,
  and excludes module setup and later coupling replay. The 7,200-second limit is checked before each
  expansion and goal position, without interrupting an in-flight position. Wall-clock stops have no
  proof, retain their records, and stay paired. A cut expansion records only tried positions and is
  marked `interrupted`. Unknown typed keys and coupling use explicit support denominators.
- A REPL timeout abandons the environment. The next run retries it; the second abandonment is final.
  Cumulative `abandonments` survive result compaction and intervening errors. Abandoned units stay in
  results and arm counts and are excluded from paired comparisons. Ordinary errors remain retryable.
- The four registered pairs are `firstText:first` (identity, on the sample), `first:any` (goal choice),
  `any:anyMultiset` (order quotient), and `first:anyMultiset`. Every arm uses the 624-step secondary cap.
  Comparisons use completed units in both arms, with both one-sided exact sign tails; no discordances
  gives null. Hypotheses remain `TO BE WRITTEN`.
- Development retains the four theorems outside the original slice and the four fixed-prefix controls.
  Prefixes are included in verification. Only typed arms receive coupling replays. Holdout development
  selects tasks whose committed whole-state search expanded at least three goals, sorts by module and
  declaration, and runs all four arms through fresh module units. There are 44 eligible tasks.
- Development, holdout, smoke, and coupling outputs require an external directory and one worker.
  Registration refuses overwrites; the future run requires its registration to be committed and present
  in a local remote-tracking ref, without network access. Implementation amendments retain the existing
  convention.

## Fast tests

```text
python -B -m unittest discover -s scripts -p "test_*.py"
..............................................................................................
----------------------------------------------------------------------
Ran 94 tests in 0.632s

OK
```

## Lean smoke tests

Outputs are under `D:/ucla/codex-worktrees/specs/goal-selection-smoke-round2/`.
The logs contain full stdout; the adjacent JSON/JSONL files contain complete results and replays.

```text
python -B scripts/run_search_goal_selection.py --self-test --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke-round2
{"self-test": {"firstText": true, "fastExporterDefined": true, "namedEqualsPlain": true, "independentGroups": true, "first": true, "any": true, "anyMultiset": true, "pickReplay": true}, "ok": true}
```

```text
python -B scripts/run_search_goal_selection.py --dev --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke-round2
```

All 32 units completed: 28 proofs, zero export failures, wall-clock stops, errors, or abandonments.
Each cell is `expansions / applications`; a dash marks no proof.

| Task | firstText | first | any | anyMultiset | Proof |
| --- | --- | --- | --- | --- | --- |
| Nat.add_assoc | 1 / 3 | 1 / 3 | 1 / 3 | 1 / 3 | `omega` |
| Nat.mul_assoc | 1 / 10 | 1 / 10 | 1 / 10 | 1 / 10 | `ring` |
| List.reverse_reverse | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | `simp` |
| List.map_id | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | `simp` |
| coupled_square | 24 / 624, dash | 24 / 624, dash | 11 / 703 | 10 / 625 | `pick_goal 3; rfl; simp` |
| independent_arithmetic | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 | `simp; simp` |
| coupled_sum | 24 / 624, dash | 24 / 624, dash | 11 / 703 | 10 / 625 | `pick_goal 3; rfl; simp` |
| independent_true | 2 / 27 | 2 / 27 | 2 / 53 | 2 / 53 | `simp; simp` |

The coupled controls retain `refine ⟨?_, ?_, ?_⟩`: `∃ n : ℕ, n * n = 9 ∧ n = 3` and
`∃ n : ℕ, n + n = 6 ∧ n = 3`. Free-choice proofs choose goal 3 in group `[[1,2,3]]`,
then `simp` acts on a singleton remaining goal. Every replay closes. Neither free-choice success
meets the secondary 624-step cap (703 and 625 applications). Independent controls retain
`refine ⟨?_, ?_⟩`: `2 + 2 = 4 ∧ 3 * 3 = 9` and `True ∧ True`; their typed groups are singleton.

```text
python -B scripts/run_search_goal_selection.py --smoke-first 3 --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke-round2
{"task": "AddConstMapClass.map_const_add", "arm": "firstText", "constructed": true, "seconds": 11.2, "setupSeconds": 11.2, "expansions": 3, "steps": 78, "stepsAtProof": null, "proof": null, "exportFailures": 0, "stopped": null, "error": null, "abandoned": null}
{"task": "AddConstMapClass.map_nsmul_add", "arm": "firstText", "constructed": true, "seconds": 2.1, "setupSeconds": 10.9, "expansions": 3, "steps": 78, "stepsAtProof": null, "proof": null, "exportFailures": 0, "stopped": null, "error": null, "abandoned": null}
{"task": "AddConstMapClass.map_sub_nsmul", "arm": "firstText", "constructed": true, "seconds": 2.2, "setupSeconds": 11.1, "expansions": 3, "steps": 78, "stepsAtProof": null, "proof": null, "exportFailures": 0, "stopped": null, "error": null, "abandoned": null}
{"first-replication": {"compared": 3, "matched": 3, "mismatches": []}}
```

```text
python -B scripts/run_search_goal_selection.py --dev-holdout 2 --workers 1 --output-dir D:/ucla/codex-worktrees/specs/goal-selection-smoke-round2
{"dev-holdout": {"eligibleTasks": 44, "tasks": 2, "units": 8, "completed": true}}
```

Both tasks are in `Mathlib.Algebra.Module.SpanRank`; the table abbreviates the common
`Submodule.FG.` declaration prefix. Seconds are search time; setup is measured separately.

| Declaration | Arm | Seconds | Setup seconds | Expansions | Applications | Proof | Export failures | Stopped |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | --- |
| finite_generators | firstText | 7.2 | 14.4 | 21 | 546 | null | 0 | null |
| finite_generators | first | 7.7 | 13.8 | 20 | 520 | null | 0 | null |
| finite_generators | any | 14.9 | 13.8 | 24 | 2080 | null | 0 | null |
| finite_generators | anyMultiset | 16.2 | 13.7 | 24 | 2080 | null | 0 | null |
| spanRank_le_iff_exists_span_set_card_le | firstText | 110.3 | 13.4 | 24 | 624 | null | 0 | null |
| spanRank_le_iff_exists_span_set_card_le | first | 91.2 | 14.0 | 24 | 624 | null | 0 | null |
| spanRank_le_iff_exists_span_set_card_le | any | 233.1 | 13.7 | 24 | 1404 | null | 0 | null |
| spanRank_le_iff_exists_span_set_card_le | anyMultiset | 209.0 | 13.8 | 24 | 1404 | null | 0 | null |

All eight units posed and completed, with no proofs, export failures, stops, errors, or abandonments.

## Boundaries

All four smoke commands exited 0, ran serially within one hour of Lean wall time, and wrote only
external outputs. No Lake or REPL processes remain. All 226 other tracked files retain their original
byte hashes; only the four named files changed, and they use LF.

Registration, the corpus run, and committed-experiment checking/coupling were not executed. There are
no registered goal-selection artifacts. C1 received three fresh searches, not the full 200-task sample;
holdout development covered two of 44 eligible tasks. Wall-clock stops and the two-abandonment resume
rule were tested with fakes, without waiting two hours or inducing real REPL timeouts. Development and
holdout outcomes do not establish corpus results. No build, package update, cache command, model server,
push, or external contact was used. No requested implementation change or permitted smoke check remains
unfinished.
