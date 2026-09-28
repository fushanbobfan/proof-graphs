# search-v0.8's declaration-range failures, rerun (not registered)

In eleven units of search-v0.8, one or two of the three searches stopped with "declaration range not found"
while another search of the same unit, on the same task, set up; each of the eleven tasks set up in its other
eight searches (one in seven). search-v0.8's amendment 1 reruns every other kind of setup failure once, but
took this one for a property of the task, so the eleven tasks fall outside its comparison. This check, made
after search-v0.8's results were read, reruns each of the eleven units once as the amendment reruns a unit (set
0 with its seeded draws, sets 1 and 2 with fresh draws) and recomputes search-v0.8's comparisons with the new
rows in place of the old. search-v0.8's registered results and decisions do not change.

## Artifacts

- `rows.jsonl`: the 33 rows of the rerun, in search-v0.8's format; `draws.jsonl`: their new draws;
- `summary.json`: the units rerun, those that failed again, and the comparisons recomputed.

## Reproduction

```text
python scripts/explore_range_rerun_v08.py --check
```

recomputes the summary from these rows and search-v0.8's committed results; CI runs it. `--run` reruns the
units (Mathlib REPLs and the model server; about twenty minutes on six workers).

## Outcome

All eleven units set up in all three searches, so the comparison covers all 169 tasks that can be posed,
against 158 in the registered analysis. The three searches prove 123 (whole states), 128 (goals) and 129
(coupled groups) of 507 task-sets, against 116, 121 and 122 of 474. Each added task scores the same under all
three searches, so the discordant tasks are unchanged: 1 to 0 for groups against goals, 7 to 1 for groups
against whole states (one-sided p = 0.035, 0.11 after Holm's adjustment), and 7 to 2 for goals against whole
states (p = 0.090, 0.18). The exclusion did not change any comparison.
