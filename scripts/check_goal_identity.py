#!/usr/bin/env python3
"""Goal identity from Lean's expressions, checked on hand-made goals in a full-Mathlib REPL.

  python scripts/check_goal_identity.py

Each case poses statements, runs a tactic, and compares the keys of `goal_identity` with the expected identity:
the review's two counterexamples to the text keys must come apart, goals alike up to the names of hypotheses or
of bound variables must coincide, implicit arguments must count, and goals coupled by a metavariable must be
grouped. Prints one line per case and exits non-zero on any mismatch.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_identity as gi  # noqa: E402
from lean_repl import LeanRepl  # noqa: E402
from run_linearizations import find_lake  # noqa: E402


def goals_after(repl: LeanRepl, statement: str, tactic: str | None = None) -> list[dict]:
    response = repl.command(f"example {statement} := by\n  sorry")
    state = int(response["sorries"][0]["proofState"])
    if tactic is not None:
        result = repl.tactic(state, tactic)
        assert result is not None, (statement, tactic)
        state = result[1]
    exported = gi.export(repl, state)
    assert exported is not None, statement
    return exported


def main() -> int:
    repl = LeanRepl(find_lake())
    failures = 0

    def check(name: str, ok: bool, detail: object = "") -> None:
        nonlocal failures
        failures += not ok
        print(json.dumps({"case": name, "ok": ok, "detail": detail}, ensure_ascii=False, default=str))

    try:
        # the review's first counterexample: one reused unknown against two
        same = goals_after(repl, "(R : Nat → Nat → Prop) (h : ∀ a, R a a) : ∃ x, R x x", "refine ⟨?_, ?_⟩")
        two = goals_after(repl, "(R : Nat → Nat → Prop) (h : ∀ a b, R a b) : ∃ x y, R x y", "refine ⟨?_, ?_, ?_⟩")
        r_same = next(g for g in same if "?[" in g["target"])
        r_two = next(g for g in two if "?[" in g["target"])
        check("metavariable reuse is kept", gi.goal_key(r_same) != gi.goal_key(r_two),
              [r_same["target"][:120], r_two["target"][:120]])
        # the review's second counterexample: capture of a bound name
        a = goals_after(repl, "(x : Nat) : ∀ h0 : Nat, x = h0")
        b = goals_after(repl, "(x : Nat) : ∀ h0 : Nat, h0 = h0")
        check("a bound name is not captured", gi.goal_key(a[0]) != gi.goal_key(b[0]), [a[0]["target"], b[0]["target"]])
        # alike up to the names of hypotheses
        a = goals_after(repl, "(a b : Nat) (h : a < b) : a + 1 ≤ b")
        b = goals_after(repl, "(x y : Nat) (hxy : x < y) : x + 1 ≤ y")
        check("renamed hypotheses coincide", gi.goal_key(a[0]) == gi.goal_key(b[0]))
        # alike up to the names of bound variables
        a = goals_after(repl, ": ∀ n : Nat, n + 0 = n")
        b = goals_after(repl, ": ∀ m : Nat, m + 0 = m")
        check("renamed bound variables coincide", gi.goal_key(a[0]) == gi.goal_key(b[0]))
        # implicit arguments count: the same printed statement at two types
        a = goals_after(repl, ": (0 : Nat) = 0")
        b = goals_after(repl, ": (0 : Int) = 0")
        check("types of numerals count", gi.goal_key(a[0]) != gi.goal_key(b[0]))
        # coupling: the witness goal and the goal that mentions it are one group
        coupled = goals_after(repl, "(p : Nat → Prop) (h : p 3) : ∃ x, p x", "refine ⟨?_, ?_⟩")
        check("a witness couples its goals", gi.groups(coupled) == [[0, 1]], gi.groups(coupled))
        independent = goals_after(repl, "(p q : Prop) (hp : p) (hq : q) : p ∧ q", "constructor")
        check("independent goals are apart", gi.groups(independent) == [[0], [1]], gi.groups(independent))
        # the state key depends on goal order and on each goal
        swapped = goals_after(repl, "(p q : Prop) (hp : p) (hq : q) : q ∧ p", "constructor")
        check("states in another order differ", gi.state_key(independent) != gi.state_key(swapped)
              and sorted(gi.goal_key(g) for g in independent) == sorted(gi.goal_key(g) for g in swapped))
    finally:
        repl.close()
    print(json.dumps({"failures": failures}))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
