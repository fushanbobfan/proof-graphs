# Goals and states up to renaming (search v0.7)

search-v0.6 left one version of the goal search untested. With BFS-Prover-V2-7B
as the proposer and its draws shared, the AND-OR search proved 41 theorems and
the whole-state search 39, and four fifths of the goal sharing the whole-state
search met was between goals that differ only in the names of their
hypotheses: `intro x` and `intro n` on the same goal give two goals that print
differently and are the same goal. A search keyed on printed goals cannot merge
them. This experiment adds the two searches that can, and runs all four on the
same 200 tasks under the same draws.

## Two by two

| | printed | up to renaming |
| --- | --- | --- |
| whole states | `whole` (search-v0.6) | `wholeRenamed` |
| goals | `andor` (search-v0.6) | `andorRenamed` |

`wholeRenamed` drops a child state whose goals agree, in order, with those of a
state already generated once hypotheses are renamed by position (the coarse key
of search-v0.4). This is the deduplication LEAN-GitHub's prover applies to
states, which renames hypotheses in Lean's storage order where this search
renames them by position in the printed context. No proof passes through a
dropped state, so nothing else changes.

`andorRenamed` merges a new goal into an earlier goal alike up to renaming and
proves it with the earlier goal's proof behind a renaming step
(`scripts/renaming.py`, `scripts/search_renaming.py`). The step uses two
tactics that change nothing but names: `rename'` (Mathlib) for accessible
hypotheses and `rename_i` (Lean) for those printed with a dagger. It is run in
the REPL on the new goal where it arose, and the merge stands only if the
renamed goal then prints as the earlier one, up to the names of the earlier
goal's own inaccessible hypotheses, which no tactic of its proof can mention by
name. No tactic makes a hypothesis inaccessible, so where the earlier goal's
hypothesis is inaccessible and the new goal's is not, the new goal keeps its
name; a proof that depended on that difference (one that names inaccessible
hypotheses with `rename_i`, which counts them by position) would be rejected by
the verification. The earlier goal keeps its names, so the prover sees each
goal as it arose, and the step becomes a line of the proof script, which is
verified from the statement like every other proof.

## Seeded shared draws

The draws are shared by the four searches of a task and seeded with
search-v0.6's: the n-th time a search expands a goal it gets the n-th set of
candidates for that goal, first the sets search-v0.6 drew, then sets drawn
anew by whichever search needs them first. A draw is an independent sample
from the prover, so a set drawn in search-v0.6 is distributed as one drawn now.
Run again with those sets, search-v0.6's two searches replay it exactly if
Lean does, and that replay is a registered check (C8); the two renaming
searches then differ from them only in what they identify.

## Artifacts

- `preregistration.json`: the four searches, the seeded draws, hypotheses H54
  to H58 with Holm's procedure over H54 to H57, checks C8 and C9, and the
  development runs made before registration;
- `results.jsonl`: per (task, search), the search with each expansion's goal
  keys, the renaming search's merge counts, and the seeded, shared, and new
  draws it used; `draws.jsonl.gz`: the 1,510 new draws;
- `summary.json`, `report.md`;
- `diagnostic_replay.py` and `diagnostic_replay.json`: a check made after the
  run and outside the registration (see C8 below).

## Reproduction

```text
python scripts/run_search_renaming.py --check-committed
python scripts/test_renaming.py
python scripts/check_renaming_repl.py
```

The first recomputes every count, test, and check from the committed rows, the
new draws, and search-v0.6's rows and draws; the other two test the renaming
step on printed goals and in a Mathlib REPL. CI runs all three.

## Outcome

All 169 statable tasks ran under all four searches; no unit errored.

| Theorems proved (of 169) | printed | up to renaming |
| --- | ---: | ---: |
| whole states | 39 | 42 |
| goals | 41 | 43 |

**None of H54 to H57 holds.** Every discordance between a search up to
renaming and a printed one favours the search up to renaming (each theorem a
printed search proves, both renaming searches prove too), but there are few:

| | Pair | Only the first | Only the second | One-sided p | Holm |
| --- | --- | ---: | ---: | ---: | ---: |
| H54 | goals up to renaming, whole states | 4 | 0 | 0.063 | 0.25 |
| H55 | goals up to renaming, goals | 2 | 0 | 0.25 | 0.50 |
| H56 | goals up to renaming, states up to renaming | 2 | 1 | 0.50 | 0.50 |
| H57 | states up to renaming, whole states | 3 | 0 | 0.13 | 0.38 |

What renaming does is make the searches faster. Among the tasks both
versions of a design prove, those that took them different numbers of
expansions took the version up to renaming fewer in every case: 14 of 14 for
the goal search and 14 of 14 for the whole-state search (one-sided p = 6e-5
each, a registered analysis outside the hypothesis family). Over the tasks both
prove, the renaming versions needed 321 expansions against 402 (goals) and 292
against 367 (states), a fifth fewer. Goals and states up to renaming are level:
43 against 42 proved, and 7 of the 15 tasks with different expansion counts
faster for the goal search.

**H58 does not hold.** Of the 14,545 goals the renaming goal search created,
4,930 were merged into an existing goal: 2,556 because they printed alike and
2,374 by a renaming (2,044 of them printing identically after it). Inside the
goal search, renamed goals are about half of what it merges, not the four
fifths that search-v0.6's whole-state measure found: that measure counts
first goals expanded again across states, while the goal search also merges the
many identical goals that different tactics make from one goal, which a
whole-state search drops as exact duplicates before expanding them. Of the
2,243 renaming steps tried, 135 (6%) failed, in the REPL or in the comparison
of prints, and their goals stayed nodes of their own. No proof the renaming
goal search found passes through a renaming step: what renaming bought was
budget, the expansions not spent on renamed goals, not the reuse of a proof.
The renaming whole-state search dropped 1,618 child states that were
duplicates only up to renaming, and the goal duplicates it still expanded fell
from 26.2 to 5.9 percent under the coarse key.

**C8 fails, on one task.** Of the 338 replayed units, 336 reached
search-v0.6's outcome exactly (one of its proofs with a different script,
since search_keys settles a goal's parents in hash order) and none drew anew.
The two replays of `MultilinearMap.map_update_sum` were abandoned when a REPL
request exceeded its 60-second wall clock during the eighth expansion, where
search-v0.6 had run 48 expansions without a proof; the wall clock, unlike the
heartbeat limit, depends on the machine's load. This changes no decision: the
renaming goal search proved that theorem (at expansion 33, with an induction),
and search-v0.6's rows show the two searches not proving it under the same
draws, so every discordance counted above holds against them as well. Run
again alone after the run, a diagnostic outside the registration
(`diagnostic_replay.py`), both replays of that task reproduce search-v0.6: 48
expansions without a proof and no new draw, in about 46 seconds each
(`diagnostic_replay.json`).

C9 holds: no goal has two sets for one occurrence among the 6,221 seeded and
1,510 new draws.

## Interpretation boundary

One quantized open-weights prover at one sampling setting and a budget of 48
expansions, on the theorems of one Mathlib slice. Renaming is by position in
the printed context and checked in print; goals equal up to definitional
unfolding, or up to the names of bound variables, stay apart. The expansions
saved are measured under shared draws, where the two versions of a search see
the same candidates until the renaming one skips a goal, so they are the
budget renaming frees in this search, not a speed-up of the prover.
