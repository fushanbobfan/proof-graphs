#!/usr/bin/env python3
"""The renaming searches on hand-made theorems with a fixed proposer, in a full-Mathlib REPL.

  python scripts/check_renaming_repl.py

Each case states a theorem, a proposer (candidates chosen by the first goal's target), and the proof script the
AND-OR search up to renaming must find, which exercises one kind of renaming step: `rename'`, `rename_i`, none
(the earlier goal's hypothesis is inaccessible), several hypotheses at once, and a merged goal behind another
(`pick_goal`). Every found script is verified from the statement. A last case checks that the whole-state search
drops states alike up to renaming. Prints one line per case and exits non-zero on any mismatch.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import search_renaming as renamed  # noqa: E402
from lean_repl import LeanRepl  # noqa: E402
from run_linearizations import find_lake  # noqa: E402
from search_harness import State  # noqa: E402

Rules = list[tuple[str, list[str]]]


def proposer(rules: Rules) -> Callable[[State], list[str]]:
    def propose(state: State) -> list[str]:
        target = state.goals[0].split("⊢", 1)[1].strip()
        return next((list(c) for pattern, c in rules if pattern == target), ["simp"])
    return propose


CASES: list[tuple[str, str, Rules, list[str]]] = [
    ("rename'", "(∀ x : ℕ, x + 0 = x) ∧ (∀ y : ℕ, y + 0 = y)",
     [("(∀ (x : ℕ), x + 0 = x) ∧ ∀ (y : ℕ), y + 0 = y", ["constructor"]), ("∀ (x : ℕ), x + 0 = x", ["intro n"]),
      ("∀ (y : ℕ), y + 0 = y", ["intro k"])],
     ["constructor", "· intro n", "  simp", "· intro k", "  rename' k => n", "  simp"]),
    ("rename_i", "(∀ x : ℕ, x + 0 = x) ∧ (∀ y : ℕ, y + 0 = y)",
     [("(∀ (x : ℕ), x + 0 = x) ∧ ∀ (y : ℕ), y + 0 = y", ["constructor"]), ("∀ (x : ℕ), x + 0 = x", ["intro n"]),
      ("∀ (y : ℕ), y + 0 = y", ["intro"])],
     ["constructor", "· intro n", "  simp", "· intro", "  rename_i n", "  simp"]),
    ("no step", "(∀ x : ℕ, x + 0 = x) ∧ (∀ y : ℕ, y + 0 = y)",
     [("(∀ (x : ℕ), x + 0 = x) ∧ ∀ (y : ℕ), y + 0 = y", ["constructor"]), ("∀ (x : ℕ), x + 0 = x", ["intro"]),
      ("∀ (y : ℕ), y + 0 = y", ["intro k"])],
     ["constructor", "· intro", "  simp", "· intro k", "  simp"]),
    ("swap", "(∀ a b : ℕ, a + b = b + a) ∧ (∀ c d : ℕ, c + d = d + c)",
     [("(∀ (a b : ℕ), a + b = b + a) ∧ ∀ (c d : ℕ), c + d = d + c", ["constructor"]),
      ("∀ (a b : ℕ), a + b = b + a", ["intro a b"]), ("∀ (c d : ℕ), c + d = d + c", ["intro b a"]),
      ("a + b = b + a", ["omega"])],
     ["constructor", "· intro a b", "  omega", "· intro b a", "  rename' b => a, a => b", "  omega"]),
    ("pick_goal", "(∀ n : ℕ, n * 1 = n) ∧ (∀ k : ℕ, k + 0 = k ∧ k * 1 = k)",
     [("(∀ (n : ℕ), n * 1 = n) ∧ ∀ (k : ℕ), k + 0 = k ∧ k * 1 = k", ["constructor"]),
      ("∀ (n : ℕ), n * 1 = n", ["intro n"]), ("∀ (k : ℕ), k + 0 = k ∧ k * 1 = k", ["intro k"]),
      ("k + 0 = k ∧ k * 1 = k", ["constructor"])],
     ["constructor", "· intro n", "  simp", "· intro k", "  constructor", "  · simp", "  · rename' k => n",
      "    simp"]),
]


def main() -> int:
    repl = LeanRepl(find_lake())
    failures = 0
    try:
        for name, statement, rules, expected in CASES:
            response = repl.command(f"example : {statement} := by\n  sorry")
            sorry = response["sorries"][0]

            def verify(script: list[str], s: str = statement) -> bool:
                body = f"example : {s} := by" + "".join(f"\n  {t}" for t in script)
                messages = repl.command(body).get("messages", [])
                return not any(m.get("severity") == "error" or "sorry" in m.get("data", "") for m in messages)

            result = renamed.and_or_search(repl, int(sorry["proofState"]), [sorry["goal"]], proposer(rules), 16,
                                           verifier=verify)
            ok = result["proof"] == expected and result["rejected"] == 0
            failures += not ok
            print(json.dumps({"case": name, "ok": ok, "proof": result["proof"], "merges": result["merges"]},
                             ensure_ascii=False))
        response = repl.command("example : ∀ x : ℕ, x + 0 = x := by\n  sorry")
        sorry = response["sorries"][0]
        result = renamed.whole_state_search(repl, int(sorry["proofState"]), [sorry["goal"]],
                                            proposer([("∀ (x : ℕ), x + 0 = x", ["intro a", "intro b", "intro"])]), 4)
        ok = result["renamedDuplicates"] == 2 and result["proof"] == ["intro a", "simp"]
        failures += not ok
        print(json.dumps({"case": "whole-state", "ok": ok, "proof": result["proof"],
                          "renamedDuplicates": result["renamedDuplicates"]}, ensure_ascii=False))
    finally:
        repl.close()
    print(json.dumps({"failures": failures}))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
