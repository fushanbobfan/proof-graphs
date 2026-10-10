#!/usr/bin/env python3
"""search_typed's searches, run so that a search whose REPL session is lost is abandoned.

A REPL request that times out restarts the session (`lean_repl.LeanRepl._exchange`), and the new session has
neither the task's environment nor any of the search's proof states. Helpers on the searches' path catch the
`ReplTimeout` that follows and return None or False (`search_faithful.export`, `goal_identity.export`,
`goal_identity_typed.export`, `search_harness.ModuleSession.verify`), so in search-v0.10 a search whose
expression export or verification timed out went on in the empty session: each later candidate failed with
"Unknown proof state.", and the search ended unproved instead of abandoned. Here the session is not
restarted. `GuardedRepl.restart` closes it and raises `SessionLost`, which is not a `ReplTimeout`, so no helper
catches it, and `run_one` records the search as abandoned, as search-v0.10 records a candidate's timeout.
The searches, the exports and the accounting are search-v0.10's, unchanged, and search-v0.10 keeps its own
runner, as registered.
"""

from __future__ import annotations

import time
from typing import Any, Callable

import run_search_typed as rt
import search_typed as st
from lean_repl import ReplTimeout
from run_linearizations import find_lake
from search_harness import State

FUNCTIONS = rt.FUNCTIONS


class SessionLost(Exception):
    """The REPL session ended: a request timed out, or the REPL's output ended."""


class GuardedRepl(st.TypedCountingRepl):
    """search_typed.TypedCountingRepl, which ends at its first lost session instead of starting another."""

    def restart(self) -> None:
        self.close()
        self.restarts += 1
        raise SessionLost("the REPL session ended, and with it the task's environment and proof states")


def run_one(task: dict[str, Any], search: str, propose: Callable[[State], list[str]], budget: int) -> dict[str, Any]:
    """run_search_typed.run_one in a GuardedRepl: a lost session abandons the search wherever it happens."""
    head = {"module": task["module"], "declaration": task["declaration"], "search": search}
    repl = GuardedRepl(find_lake(), imports=None)
    started = time.monotonic()
    try:
        path = rt.ROOT / ".lake" / "packages" / "mathlib" / (task["module"].replace(".", "/") + ".lean")
        session = st.TypedSession(repl, task["module"], path, [(task["declaration"], task["line"])])
        for _, made in session.tasks_in_order():
            if made is None:
                return head | {"constructed": False}
            result = FUNCTIONS[search](repl, made.proof_state, [made.goal], propose, budget,
                                       verifier=lambda script, m=made: session.verify(m, script))
            return head | {"constructed": True, "result": result,
                           "typedFastExport": getattr(repl, "typed_fast_export", False),
                           "fastExport": getattr(repl, "fast_export", False),
                           "pickGoalDefined": getattr(repl, "pick_goal_defined", False),
                           "costs": repl.cost_summary(),
                           "setupSeconds": round(time.monotonic() - started - result["seconds"], 1)}
        return head | {"constructed": False, "reason": "declaration range not found"}
    except (ReplTimeout, SessionLost):
        return head | {"constructed": True, "abandoned": "repl timeout", "costs": repl.cost_summary(),
                       "seconds": round(time.monotonic() - started, 1)}
    finally:
        repl.close()
