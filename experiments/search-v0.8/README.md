# States, goals, and coupled goal groups (search v0.8)

search-v0.7 found goals and whole states level once hypotheses are renamed (43 against 42 proved), and
keys-v0.1 found that the text keys every search so far has used join, item by item, 5 to 9 percent of goals
whose Lean expressions differ. A search over goals also treats goals as independent: it discards a candidate
that assigns a metavariable another open goal shares, and search-v0.2 found goals sharing an existential
witness defeat it. This experiment asks whether a search over the groups of goals that metavariables couple
proves more than a search over independent goals or over whole states, with every search identifying goals
by their Lean expressions and the prover's draws repeated three times.

## Three searches

All three identify goals by the faithful key of `scripts/goal_identity.py`
(`scripts/search_faithful.py`):

- `whole`: whole states; a child is dropped when its state key was generated before.
- `goals`: single goals, merged by goal key, behind a renaming step when only hypothesis names differ; a
  candidate that assigns a metavariable another open goal shares is discarded as entangled.
- `groups`: goals grouped by the metavariables they share; a candidate that changes goals of its own group
  is kept; a one-goal group is merged as in `goals`, a larger one only when it prints identically.

The key is exported by a tactic defined once per task environment, right after the imports; keys-v0.1's
export failed inside some declarations' scope, and C14 checks that the defined tactic was used.

## Three sets of draws

The proposer is search-v0.5's to v0.7's: BFS-Prover-V2-7B in Q8_0, 16 completions at temperature 1.0. Each
search has 48 expansions, and within a set a task's draws are shared by its three searches as in search-v0.6.
Set 0 is seeded with the 7,731 sets search-v0.6 and search-v0.7 recorded; sets 1 and 2 are drawn afresh. A
unit is one task in one set: its three searches in turn, in an order that rotates with the task and the set,
each in a fresh REPL. Per task, a search scores the number of sets in which it proves the theorem. H64 to H66
compare the three pairs by a one-sided sign test on the tasks where the scores differ, decided together by
Holm's procedure at 0.05.

## Artifacts

- `preregistration.json`: the searches, the sets, hypotheses H64 to H66, and checks C13 and C14;
- `amendment-1.json`: the rerun of units that failed to set up while memory ran out, and why;
- `results.jsonl`: one row per task, set and search (1,800), with the search's expansions, draws and costs;
  `draws.jsonl.gz`: the 12,415 new draws;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_coupled.py --check-committed
python scripts/check_faithful_repl.py
```

The first recomputes the summary from the committed rows and draws; the second tests the three searches in a
Mathlib REPL with a fixed proposer. CI runs both. `--run` resumes the searches (a Mathlib REPL per worker and
the model server; about eighteen hours on six to eight workers).

## The run

For its first two hours keys-v0.1 ran ten REPL workers beside this run's eight and the model server, the
Windows commit limit ran out, and searches failed to set up although other searches of the same unit, on the
same task, did. Amendment 1, made before any summary was computed, reruns once every unit with a search not
constructed without a reason or abandoned by a REPL timeout. At 04:58 the machine stopped with a bugcheck
(0x1A, a corrupted page-table entry while a REPL process exited), with 291 of the 600 units finished. The
resume, from 13:47 with six workers and no other REPL on the machine, ran the 309 unfinished units and the 69
the amendment marks. No unit raised an error.

Of the 200 tasks, 31 set up in no set and no search, as in search-v0.7, which could pose 169. Three units of
two tasks, first run in the resume, were abandoned by REPL timeouts in all three searches; they count as
unproved for each search, and the amendment's one resume had passed. Eleven tasks set up in eight of their nine
searches (one in seven): in one set, one or two searches stopped with "declaration range not found" while the
others set up. The amendment took that reason for a property of the task, which it is not, so these eleven
tasks fall outside the comparison, which covers the 158 tasks that set up in all nine searches.

## Outcome

| Theorems proved (of 158) | set 0 | set 1 | set 2 | pooled (of 474) |
| --- | ---: | ---: | ---: | ---: |
| whole states | 38 | 37 | 41 | 116 |
| goals | 40 | 39 | 42 | 121 |
| coupled groups | 40 | 39 | 43 | 122 |

**None of H64 to H66 holds.**

| | Pair | Tasks the first proves in more sets | The second | One-sided p | Holm |
| --- | --- | ---: | ---: | ---: | ---: |
| H64 | groups, goals | 1 | 0 | 0.50 | 0.50 |
| H65 | groups, whole states | 7 | 1 | 0.035 | 0.11 |
| H66 | goals, whole states | 7 | 2 | 0.090 | 0.18 |

For groups against whole states, the registered interval of the mean per-task difference in proof rate,
1.3 points [0.4, 2.4] by resampling modules, excludes zero; the decision rule is the sign test under Holm's
procedure, and by that rule H65 does not hold.

Coupling rarely mattered. The goal search discarded 689 entangled candidates and the group search made 1,210
groups of several goals, but one proof passed through such a group; the group search discarded 28 candidates
that changed a goal outside their group. The whole-state search found four proofs with a goal's later draw.

What differed was cost. The three searches spent about the same expansions (13,115 for whole states, 13,560
for goals, 13,464 for groups), but the group search drew fewer new sets (3,406, against 4,169 and 4,780) and
generated fewer completion tokens (0.87 million, against 1.04 and 1.19 million), and its median search took
16 seconds, against 24 for goals and 35 for whole states.

C13 holds: no goal has two new draws for one occurrence among the 12,415 new draws. C14 holds: all 1,500
searches that set up exported through the defined tactic.

## The eleven tasks, rerun (exploratory)

After these results were read, `experiments/search-v0.8-range-rerun` (not registered) reran the eleven units
once, as the amendment reruns a unit, and recomputed the comparisons with their new rows. All eleven set up in
all three searches, so all 169 tasks that can be posed enter. The three searches then prove 123, 128 and 129
of 507 task-sets, and every added task scores the same under all three searches: the discordant tasks and the
p-values are those above.

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48 expansions, on the theorems of
one Mathlib slice. Identity is syntactic on instantiated Lean expressions; goals equal up to definitional
unfolding stay apart. The tests count tasks, not task-sets, so a task contributes once whatever the size of
its difference.
