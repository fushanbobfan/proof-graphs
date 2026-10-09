# Heartbeats v0.1

The search registrations state a limit of 40,000 heartbeats per candidate tactic, which the harness sends as
`set_option maxHeartbeats 40000 in (tac)`. In Lean 4.32 that form reaches the kernel but not the elaborator
(`docs/heartbeat-limit.md`), so the candidates of search-v0.3 and of the later searches elaborated under the limit of
the theorem's context, 200,000 by default. This experiment reruns search-v0.3's two menu searches on all 1,347 of its
tasks with the limit in force in the elaborator as well as in the kernel. Each module session defines, right after its
imports,

```lean
open Lean Elab Tactic in
elab "pg_hb_limited " t:tactic : tactic =>
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 40000 * 1000 }) <| withCurrHeartbeats do
    evalTactic t
```

and every candidate is sent as `set_option maxHeartbeats 40000 in pg_hb_limited (tac)`. Everything else is
search-v0.3's code, unchanged, each (task, search) unit in a fresh REPL.

## Artifacts

- `preregistration.json`: the tasks (search-v0.3's, by hash), the limiting tactic and where it is defined, the
  measures, hypotheses H100 to H102 and checks C38 and C39, registered before any unit ran;
- `results.jsonl`: one row per (task, search) unit with search-v0.3's fields, whether the session defined the limiting
  tactic, and the candidate applications that stopped on the limit, by tactic;
- `summary.json`, `report.md`.

## Reproduction

```text
python scripts/run_search_heartbeats.py --check-committed
```

recomputes the summary from the committed rows; CI runs it.

## Outcome

All 2,694 units ran, with no error and none abandoned; every session defined the limiting tactic (C38). The limit
stopped 2,650 candidate applications in 413 searches (C39): 1,314 `exact?`, 1,061 `aesop`, 62 `rcases`, 55
`simp_all`, and 158 others.

- **H100 holds**: over the 1,170 tasks both experiments posed to both searches, each search proves 102 tasks, the same
  102 as in search-v0.3.
- **H101 holds**: 2 tasks are proved by the AND-OR search alone and 2 by the whole-state search alone, two-sided
  p = 1.0.
- **H102 holds**: the whole-state search spends 4.53% of its expansions on order duplicates (729 of 16,093) and 14.91%
  on goal duplicates (2,399), against 4.52% and 14.91% in search-v0.3.

Of the 2,341 searches that produced a result in both experiments, 2,273 took the same steps, expansion by expansion.
The other 68, 34 of each search, differ in which candidate applications succeeded (132 fewer valid applications among
them), none in its outcome or its proof. Three of the 68 had no stop at all and differ by one valid application each,
so not every difference comes from a stop; the rows do not show whether the wrapping tactic or the wall clock made
them.

One task lies outside the 1,170: search-v0.3's AND-OR search of
`FirstOrder.Language.BoundedFormula.realize_ex` ended on a `RecursionError` in the harness, which search-v0.3 counts
as unproved. Here both searches prove it, so over all 1,171 tasks posed here the two searches prove 103 each, where
search-v0.3 reported 103 for the whole-state search and 102 for the AND-OR search.

## Interpretation boundary

The rerun covers the menu searches of search-v0.3 at 24 expansions. The searches with the step prover (search-v0.8 to
search-v0.10) and the other menu experiments still ran under the context's limit; at 24 expansions the enforced limit
changed no outcome here, which makes a large effect on them unlikely but does not test them. The options of Mathlib's
build remain untested: all searches ran under Lean's defaults, which nest pending instance problems less deeply
(`maxSynthPendingDepth` 1, where Mathlib builds with 3).
