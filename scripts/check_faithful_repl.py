#!/usr/bin/env python3
"""The searches of search_faithful.py on hand-made theorems with a fixed proposer, in a full-Mathlib REPL.

  python scripts/check_faithful_repl.py

- a witness shared by two goals: the group search proves the theorem, the goal search discards the candidates
  that assign the witness and does not, and the whole-state search proves it;
- goals alike up to bound names: the goal search merges them without a renaming step;
- goals alike up to hypothesis names: the goal search merges them behind `rename'`;
- states alike up to hypothesis names: the whole-state search drops the second.
Every proof is verified from the statement. Prints one line per case and exits non-zero on any mismatch.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
import search_faithful as sf  # noqa: E402
from run_linearizations import find_lake  # noqa: E402
from search_harness import State  # noqa: E402

Rules = list[tuple[str, list[str]]]


def proposer(rules: Rules, default: list[str]) -> Callable[[State], list[str]]:
    def propose(state: State) -> list[str]:
        target = state.goals[0].split("⊢", 1)[1].strip()
        return next((list(c) for pattern, c in rules if pattern == target), list(default))
    return propose


def run(repl: sf.CountingRepl, search: Callable, statement: str, rules: Rules, default: list[str],
        budget: int = 8) -> dict:
    response = repl.command(f"example : {statement} := by\n  sorry")
    sorry = response["sorries"][0]

    def verify(script: list[str]) -> bool:
        body = f"example : {statement} := by" + "".join(f"\n  {t}" for t in script)
        messages = repl.command(body).get("messages", [])
        return not any(m.get("severity") == "error" or "sorry" in m.get("data", "") for m in messages)

    return search(repl, int(sorry["proofState"]), [sorry["goal"]], proposer(rules, default), budget, verifier=verify)


def main() -> int:
    repl = sf.CountingRepl(find_lake())
    defined = repl.command(sf.DEFINITION)  # the export tactic, as ExportingSession defines it in a task's environment
    repl.env = defined["env"]
    repl.fast_export = True
    failures = 0

    def check(name: str, ok: bool, detail: object) -> None:
        nonlocal failures
        failures += not ok
        print(json.dumps({"case": name, "ok": ok, "detail": detail}, ensure_ascii=False, default=str))

    try:
        witness = "∃ x : ℕ, x + 1 = 3"
        rules = [("∃ x, x + 1 = 3", ["refine ⟨?_, ?_⟩"]), ("ℕ", ["exact 2"]), ("?w + 1 = 3", ["rfl"]),
                 ("2 + 1 = 3", ["rfl"])]
        grouped = run(repl, sf.coupled_search, witness, rules, ["rfl"])
        check("the group search keeps a shared witness", grouped["proof"] == ["refine ⟨?_, ?_⟩", "exact 2", "rfl"]
              and grouped["groupsInProof"] == 1,
              {"proof": grouped["proof"], "groups": grouped["groups"], "inProof": grouped["groupsInProof"]})
        single = run(repl, sf.and_or_search, witness, rules, ["rfl"])
        check("the goal search discards what assigns it", single["proof"] is None and single["entangled"] > 0,
              {"proof": single["proof"], "entangled": single["entangled"]})
        whole = run(repl, sf.whole_state_search, witness, rules, ["rfl"])
        check("the whole-state search proves it", whole["proof"] is not None, whole["proof"])
        bound = run(repl, sf.and_or_search, "(∀ x : ℕ, x + 0 = x) ∧ (∀ y : ℕ, y + 0 = y)",
                    [("(∀ (x : ℕ), x + 0 = x) ∧ ∀ (y : ℕ), y + 0 = y", ["constructor"]),
                     ("∀ (x : ℕ), x + 0 = x", ["intro n"]), ("∀ (y : ℕ), y + 0 = y", ["intro m"])], ["simp"])
        check("bound names do not keep goals apart",
              bound["proof"] == ["constructor", "· intro n", "  simp", "· intro n", "  simp"]
              and bound["merges"]["renamed"] == 1, {"proof": bound["proof"], "merges": bound["merges"]})
        renamed = run(repl, sf.and_or_search, "(∀ n : ℕ, n * 1 = n) ∧ (∀ k : ℕ, k + 0 = k ∧ k * 1 = k)",
                      [("(∀ (n : ℕ), n * 1 = n) ∧ ∀ (k : ℕ), k + 0 = k ∧ k * 1 = k", ["constructor"]),
                       ("∀ (n : ℕ), n * 1 = n", ["intro n"]), ("∀ (k : ℕ), k + 0 = k ∧ k * 1 = k", ["intro k"]),
                       ("k + 0 = k ∧ k * 1 = k", ["constructor"])], ["simp"])
        check("hypothesis names are carried by a renaming step",
              renamed["proof"] == ["constructor", "· intro n", "  simp", "· intro k", "  constructor", "  · simp",
                                   "  · rename' k => n", "    simp"],
              {"proof": renamed["proof"], "merges": renamed["merges"]})
        dropped = run(repl, sf.whole_state_search, "∀ x : ℕ, x + 0 = x",
                      [("∀ (x : ℕ), x + 0 = x", ["intro a", "intro b"])], ["simp"], budget=4)
        check("the whole-state search drops a renamed state",
              dropped["expansions"][0]["duplicates"] == 1 and dropped["proof"] == ["intro a", "simp"],
              {"proof": dropped["proof"], "first": dropped["expansions"][0]})
        print(json.dumps({"costs": repl.cost_summary()}))
    finally:
        repl.close()
    print(json.dumps({"failures": failures}))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
