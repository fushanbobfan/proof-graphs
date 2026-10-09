# The per-tactic heartbeat limit

The registrations of search-v0.1 and search-v0.3 to search-v0.9 state a limit of 40,000 heartbeats per candidate
tactic, and `scripts/lean_repl.py` sets it by sending each candidate as `set_option maxHeartbeats 40000 in (tac)`. In
Lean 4.32 a `set_option` inside a tactic changes the options the tactic runs under, which the kernel reads, but not
the elaborator's heartbeat limit, which is fixed when the command begins: the tactic goes through `withOptions`,
which updates the options, the diagnostics flag and the recursion limit, and leaves `Core.Context.maxHeartbeats`
alone. The candidates' elaboration therefore ran under the heartbeat limit of the declaration's context, Lean's
default of 200,000 in the proof states checked (a declaration may set its own with `set_option ... in`, which the
harness keeps), and the 40,000 bounded only kernel checks made inside a tactic. The 60-second wall-clock limit per
tactic applied as stated.

Every search of every comparison ran under the same harness, so no comparison is affected; the budget per tactic was
larger than the registrations state. The other `set_option maxHeartbeats` prefixes the replays send in tactic mode
behave alike: the expression-key and closed-type exports, written with 400,000, ran under the default, and
defeq-v0.1's merge, written with 200,000, which is the default, ran under what it states.

`scripts/check_tactic_heartbeats.py` shows the mechanism in a few seconds: `omega` under a limit of 1 fails in the
elaborator when the limit is set at the command level, and when it is set inside the tactic, also in the REPL's
tactic mode as the harness sends it, `omega` elaborates and only the kernel's check fails. This was found on
2026-10-08, while classifying defeq-v0.1's merges, when a limit of 2,000,000 sent the same way left 200,000 in force.

A tactic can bound its own elaboration by setting the limit in its context, which the same script checks:

```lean
open Lean Elab Tactic in
elab "pg_limited_omega" : tactic =>
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 1000 }) <| withCurrHeartbeats do
    evalTactic (← `(tactic| omega))
```

Here `maxHeartbeats` is in heartbeats, a thousand per unit of the option, and `withCurrHeartbeats` counts from the
call; `omega` then stops in the elaborator at the limit.
