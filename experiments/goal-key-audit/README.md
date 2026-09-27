# Goal-key audit (not registered)

A review of 2026-09-26 showed two ways the text keys of the searches can merge
different goals, and noted that neither had been measured on the goals the
experiments met:

- the default key erases metavariable numbers, so `R ?m.1 ?m.1` and
  `R ?m.1 ?m.2` coincide although only the first reuses an unknown (the fine
  key erases them the same way);
- the coarse key renames hypotheses to `h0`, `h1`, ... by text substitution,
  which can capture a bound variable already named that way: with `x : Nat`,
  `∀ h0, x = h0` and `∀ h0, h0 = h0` coincide.

This audit, made after the fact and outside any registration, measures both on
the step-prover searches of search-v0.6 and v0.7, the only searches that logged
goal text. No registered result changes.

## Method

Every draw was logged with its goal text, and every expansion used a draw of
its first goal's default key in its task, so the default text of each
whole-state expansion's first goal can be recovered. It was, for all 13,812
expansions, and its coarse digest matched the recorded one in every case.
Each first goal is then re-keyed with a capture-free coarse key: hypotheses are
renamed to placeholders (`◊0`, `◊1`, ...) that no Lean goal prints, so that two
goals coincide only if they are alike up to a consistent renaming.

The recovered text is one logged goal per default key and occurrence, not
necessarily the one each expansion saw, so metavariable patterns can only be
compared among logged goals, and few keys have two of them. What bounds the
erasure's effect is the number of goal duplicates whose first goal has a
metavariable at all.

## Outcome

| Whole-state search | Expansions | Goal duplicates, coarse key | Capture-free key | First goals with a metavariable | Goal duplicates with one |
| --- | ---: | ---: | ---: | ---: | ---: |
| search-v0.6 | 4,751 | 1,241 (26.1%) | 1,241 (26.1%) | 109 | 1 of 233 |
| search-v0.7 | 4,703 | 1,231 (26.2%) | 1,231 (26.2%) | 109 | 1 of 231 |
| search-v0.7, up to renaming | 4,358 | 256 (5.9%) | 256 (5.9%) | 119 | 0 of 184 |

The capture-free key gives the coarse key's shares exactly, and among the 707
coarse classes of logged goals that merge several default keys it splits none:
the capture collision did not occur in these searches. Erasing metavariable
numbers can have merged at most one goal duplicate in each search, so the
default-key shares move by at most 0.02 points; that bound is what the audit
supports, since only one key with a metavariable has two logged goals to
compare.

The coarse-key shares of the menu searches (28.0% in search-v0.4 and 28.9% on
the holdout slice) come from searches that logged no goal text, so they are not
audited, and neither are goals alike up to the names of bound variables, which
every text key keeps apart.

## Reproduction

```text
python scripts/audit_goal_keys.py --check
```

recomputes `audit.json` from the committed logs and results; CI runs it.
