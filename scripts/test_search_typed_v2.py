#!/usr/bin/env python3
"""A search whose REPL session is lost, under search-v0.10's runner and under search_typed_v2's, without Lean.

  python scripts/test_search_typed_v2.py

The REPL here dies at its first request, as it does when a request times out or the process ends. In
search-v0.10 the session restarts, the helpers that catch `ReplTimeout` return None or False, and the search
goes on in the new, empty session. In search_typed_v2 the session ends, nothing catches `SessionLost`, and the
search is abandoned.
"""

from __future__ import annotations

import contextlib
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Callable, Iterator
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_identity as gi  # noqa: E402
import goal_identity_typed as gt  # noqa: E402
import lean_repl  # noqa: E402
import run_search_typed as rt  # noqa: E402
import search_faithful as sf  # noqa: E402
import search_harness as harness  # noqa: E402
import search_typed as st  # noqa: E402
import search_typed_v2 as guarded  # noqa: E402
from test_lean_repl import FakeProcess  # noqa: E402

TASK = {"module": "Mathlib.Logic.Basic", "declaration": "t0", "line": 1}
POSED = harness.ModuleTask("t0", "example : True", "⊢ True", 0, 0)


def dying() -> FakeProcess:
    """A REPL whose output ends at its first request."""
    process = FakeProcess(answers=False)
    process.on_request = process.end
    return process


@contextlib.contextmanager
def launches(*processes: FakeProcess) -> Iterator[MagicMock]:
    """`lake exe repl` returns `processes` in turn; `taskkill` is recorded, not run."""
    try:
        with patch.object(lean_repl.subprocess, "Popen", side_effect=list(processes)) as popen, \
                patch.object(lean_repl.subprocess, "run"):
            yield popen
    finally:
        for process in processes:
            process.end()


def faithful_export(repl: lean_repl.LeanRepl) -> Any:
    repl.fast_export = True
    return sf.export(repl, 0)


HELPERS: dict[str, Callable[[lean_repl.LeanRepl], Any]] = {
    "search_faithful.export": faithful_export,
    "goal_identity.export": lambda repl: gi.export(repl, 0),
    "goal_identity_typed.export": lambda repl: gt.export(repl, 0),
    "ModuleSession.verify": lambda repl: harness.ModuleSession.verify(SimpleNamespace(repl=repl), POSED, ["trivial"]),
}


class Helpers(unittest.TestCase):
    """The helpers on the searches' path that catch ReplTimeout, on a session that dies."""

    def test_the_registered_session_restarts_and_the_helper_goes_on(self) -> None:
        for name, helper in HELPERS.items():
            with self.subTest(name), launches(dying(), FakeProcess()) as popen:
                repl = st.TypedCountingRepl("lake", imports=None)
                self.assertIn(helper(repl), (None, False))
                self.assertEqual((repl.restarts, popen.call_count), (1, 2))

    def test_the_guarded_session_ends_and_no_helper_catches_it(self) -> None:
        self.assertFalse(issubclass(guarded.SessionLost, lean_repl.ReplTimeout))
        for name, helper in HELPERS.items():
            with self.subTest(name), launches(dying()) as popen:
                repl = guarded.GuardedRepl("lake", imports=None)
                with self.assertRaises(guarded.SessionLost):
                    helper(repl)
                self.assertEqual((repl.restarts, popen.call_count), (1, 1))
                self.assertIsNone(repl.process)

    def test_a_timeout_ends_the_guarded_session(self) -> None:
        with launches(FakeProcess(answers=False)) as popen:
            repl = guarded.GuardedRepl("lake", timeout=0.05, imports=None)
            with self.assertRaises(guarded.SessionLost):
                repl.tactic(0, "trivial")
            self.assertEqual((repl.restarts, popen.call_count), (1, 1))


class Session:
    """search_typed.TypedSession without Lean: the task is posed at proof state 0."""

    def __init__(self, repl: lean_repl.LeanRepl, *args: Any) -> None:
        self.repl = repl

    def tasks_in_order(self) -> Iterator[tuple[str, harness.ModuleTask]]:
        yield POSED.name, POSED

    def verify(self, task: harness.ModuleTask, tactics: list[str]) -> bool:
        return harness.ModuleSession.verify(self, task, tactics)  # type: ignore[arg-type]


def search(repl: lean_repl.LeanRepl, proof_state: int, goals: list[str], propose: Any, budget: int,
           verifier: Any = None) -> dict[str, Any]:
    """A search's first steps: export the root, then try a candidate."""
    exported = sf.export(repl, proof_state)
    tried = repl.tactic(proof_state, "trivial")
    return {"proof": None, "expansions": [], "exported": exported, "tried": tried, "seconds": 0.0,
            "restarts": repl.restarts}


class Runner(unittest.TestCase):
    def run_one(self, run_one: Callable[..., dict[str, Any]], *processes: FakeProcess) -> tuple[dict[str, Any], int]:
        with launches(*processes) as popen, patch.object(st, "TypedSession", Session), \
                patch.dict(rt.FUNCTIONS, {"whole": search}), patch.object(rt, "find_lake", lambda: "lake"), \
                patch.object(guarded, "find_lake", lambda: "lake"):
            return run_one(TASK, "whole", lambda state: [], 48), popen.call_count

    def test_search_v010_goes_on_in_an_empty_session(self) -> None:
        row, launched = self.run_one(rt.run_one, dying(), FakeProcess())
        self.assertNotIn("abandoned", row)
        self.assertEqual((row["result"]["restarts"], launched), (1, 2))
        self.assertIsNone(row["result"]["exported"])

    def test_a_lost_session_abandons_the_search(self) -> None:
        row, launched = self.run_one(guarded.run_one, dying())
        self.assertEqual((row["constructed"], row["abandoned"], launched), (True, "repl timeout", 1))
        self.assertNotIn("result", row)
        self.assertEqual(row["costs"]["export"]["calls"], 1)

    def test_rows_are_search_v010s_while_no_session_is_lost(self) -> None:
        rows = [self.run_one(run_one, FakeProcess())[0] for run_one in (rt.run_one, guarded.run_one)]
        for row in rows:
            self.assertGreaterEqual(row.pop("setupSeconds"), 0)
            row["costs"] = {kind: cost["calls"] for kind, cost in row["costs"].items()}
        self.assertEqual(rows[0], rows[1])
        self.assertEqual(rows[1]["result"]["restarts"], 0)


if __name__ == "__main__":
    unittest.main()
