#!/usr/bin/env python3
"""What a heartbeat limit set inside a tactic bounds, in this project's Lean.

  python scripts/check_tactic_heartbeats.py

The search harness (`lean_repl.LeanRepl.tactic`) sends each candidate as `set_option maxHeartbeats 40000 in (tac)`.
Lean's tactic-level `set_option` changes the options it runs under (`withOptions`), which update the recursion limit
but not the elaborator's heartbeat limit (`Core.Context.maxHeartbeats`, fixed when the command began). The kernel reads
the option, so kernel checks made inside the tactic do see it. This runs `omega`, whose elaboration needs more than a
thousand heartbeats, under a limit of 1 set at the command level and inside the tactic, and in the REPL's tactic
mode as the harness sends it, and asserts which phase fails: the elaborator at the command level, the kernel inside
the tactic. Lean core only, a few seconds.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_repl import LeanRepl  # noqa: E402
from run_linearizations import find_lake  # noqa: E402

GOAL = "∀ (a b c d : Nat), a < b → b < c → c < d → a + 3 ≤ d"


def text(response: dict[str, Any]) -> str:
    return " ".join([m.get("data", "") for m in response.get("messages", [])] + [response.get("message", "")])


def main() -> int:
    repl = LeanRepl(find_lake(), imports="import Lean")
    try:
        plain = repl._exchange({"cmd": f"example : {GOAL} := by omega", "env": 0}, 120)
        command = repl._exchange({"cmd": f"set_option maxHeartbeats 1 in\nexample : {GOAL} := by omega", "env": 0},
                                 120)
        inside = repl._exchange({"cmd": f"example : {GOAL} := by\n  set_option maxHeartbeats 1 in omega", "env": 0},
                                120)
        made = repl._exchange({"cmd": f"example : {GOAL} := by sorry", "env": 0}, 120)
        harness = repl._exchange({"tactic": "set_option maxHeartbeats 1 in (omega)",
                                  "proofState": made["sorries"][0]["proofState"]}, 120)
    finally:
        repl.close()
    checks = {
        "omega succeeds without a limit": not text(plain).strip(),
        "a command-level limit stops the elaborator": "maximum number of heartbeats (1)" in text(command),
        "a limit inside the tactic does not stop the elaborator":
            "maximum number of heartbeats" not in text(inside) and "(kernel) deterministic timeout" in text(inside),
        "so in the REPL's tactic mode, as the harness sends it":
            "maximum number of heartbeats" not in text(harness) and "(kernel) deterministic timeout" in text(harness),
    }
    for name, ok in checks.items():
        print(f"{'ok  ' if ok else 'FAIL'} {name}")
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
