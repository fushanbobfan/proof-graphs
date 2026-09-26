# Goal identity, and a menu without one-shot provers (search v0.4)

Two questions the earlier search experiments left open.

*Goal identity.* Searches v0.1 to v0.3 compare goals by their pretty-printed
text with the case tag removed and metavariable numbers erased. That text hides
implicit arguments, so two different goals can print alike, and it keeps
hypothesis names, so two goals that differ only by renaming print differently.
Both would move the duplicate measures, in opposite directions. This arm
records every expanded state's goals under three keys at once — *fine* (printed
with `pp.all`), *default* (the earlier key), and *coarse* (the default text with
hypotheses renamed by position) — while the search itself behaves exactly as
search-v0.3 (C5).

*A regime where architecture could matter.* At the menu's strength, searches
proved what they proved within a dozen expansions and then ran out of states,
so a design that removes goal sharing had nothing to gain. Removing the menu's
one-shot provers (`simp`, `simp_all`, `aesop`, `norm_num`, `exact?`,
`simp at *`, `simp [*]`) leaves tactics that close goals only inside a decision
procedure or by a step of logic, which should make proofs longer and searches
deeper. This arm runs both searches with that menu at 96 expansions.

## Artifacts

- `preregistration.json`: the tasks (search-v0.3's 1,347 candidates in a seeded
  random order; the first 300 for the keys arm, the first 135 of those for the
  hammer-free arm), the three keys, the budgets, hypotheses H30 to H33, checks
  C5 and C6, and the analyses;
- `results.jsonl`: per (arm, task, search), the search with each expansion's
  three keys as digests;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_keys.py --check-committed
```

recomputes every fraction, interval, and decision from the committed rows; CI
runs it.

## Outcome

258 of the 300 keys-arm tasks and 115 of the 135 hammer-free tasks could be
stated in their original context. No unit was abandoned or errored. C5 holds
(all 257 comparable searches reproduce search-v0.3 exactly) and C6 holds (the
default-key flags recomputed from the digests equal the search's own on all
6,784 expansions).

| Arm | Key | Order duplicates | Goal duplicates (95% interval) |
| --- | --- | ---: | --- |
| keys (24) | fine | 5.2% | 15.4% (13.2 to 17.3) |
| keys (24) | default | 5.3% | 15.9% (13.4 to 18.1) |
| keys (24) | coarse | 5.2% | **28.0%** (25.2 to 30.9) |
| hammer-free (96) | default | 3.8% | 25.9% (16.2 to 34.6) |

**H30 holds** (goal duplicates are at least twice order duplicates under each
key) and **H31 holds**: printing with `pp.all` changes almost nothing (15.4%
against 15.9%), so goals that print alike but differ in their implicit
arguments are not what the goal-duplicate measure is counting. Renaming
hypotheses by position, however, nearly doubles it: 28.0%. Most of the sharing
the default key misses is goals that differ only in the names of their
hypotheses.

**H33 holds**: without one-shot provers the searches run deeper and goal
sharing grows from 15.9% to 25.9% of expansions, while order duplicates stay
below 5%. **H32 is not supported**, and in the strongest way: at 96 expansions
neither search proved a single one of the 115 tasks. 91 whole-state and 95
AND-OR searches exhausted their frontier first. The AND-OR search discarded 398
candidates as entangled, and exactly one of its expansions was of a goal equal
under the coarse key to one it had already expanded.

Removing the hammers therefore does not produce the regime in which a search
over goals could win; it produces a search that proves nothing. What the menu
proves, it proves with a one-shot prover in one step. The missing ingredient is
the strength of the proposer, not the budget or the search architecture.

## Interpretation boundary

Breadth-first search with fixed menus on the theorems of one Mathlib slice. The
keys compare printed goals; definitional equality is not tested, and the coarse
key normalizes hypothesis names by position in the context, which is a
sufficient condition for two goals to be the same up to renaming, not a
necessary one. The hammer-free arm's tasks are the first 135 of the same random
order as the keys arm's, so the two arms are not independent samples.
