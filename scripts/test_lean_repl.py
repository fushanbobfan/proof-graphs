#!/usr/bin/env python3
"""A restarted REPL session against the output of the session it replaced, without Lean.

  python scripts/test_lean_repl.py

A fake process stands in for `lake exe repl`. The test decides when a killed process's output ends and waits
for its pump to finish, so that the pump finishes after `restart` has put the next session's queue in place,
which with Lean happens when the pump thread is held up for a few milliseconds. `lean_repl.LeanRepl`, which the
registered experiments use, lets that output into the next session; `lean_repl_v2.LeanRepl` keeps it in the
queue of the killed session.
"""

from __future__ import annotations

import json
import queue
import sys
import threading
import unittest
from pathlib import Path
from typing import Callable
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_repl  # noqa: E402
import lean_repl_v2  # noqa: E402

STALE = ['{"proofState": 3, "goals": []}\n', "\n"]  # a response the killed process had finished writing


class FakeStdin:
    def __init__(self, process: FakeProcess) -> None:
        self.process = process
        self.text = ""

    def write(self, text: str) -> int:
        self.text += text
        while "\n\n" in self.text:
            request, self.text = self.text.split("\n\n", 1)
            self.process.receive(json.loads(request))
        return len(text)

    def flush(self) -> None:
        pass


class FakeProcess:
    """Answers request n with `{"env": n}` unless told not to; its output ends when the test ends it, killed
    or not."""

    pid = 0

    def __init__(self, answers: bool = True, on_request: Callable[[], None] | None = None) -> None:
        self.answers = answers
        self.on_request = on_request
        self.requests: list[dict] = []
        self.output: queue.Queue[str | None] = queue.Queue()
        self.stdin = FakeStdin(self)
        self.stdout = iter(self.output.get, None)
        self.killed = False

    def receive(self, request: dict) -> None:
        self.requests.append(request)
        if self.on_request is not None:
            self.on_request()
        if self.answers:
            self.emit(json.dumps({"env": len(self.requests)}) + "\n", "\n")

    def emit(self, *lines: str) -> None:
        for line in lines:
            self.output.put(line)

    def end(self) -> None:
        self.output.put(None)

    def kill(self) -> None:
        self.killed = True

    def poll(self) -> int | None:
        return 0 if self.killed else None

    def wait(self) -> int:
        return 0


class Sessions(unittest.TestCase):
    def started(self, session: type, *processes: FakeProcess, imports: str | None = None) -> lean_repl.LeanRepl:
        """A session whose launches return `processes` in turn, their pumps kept in `self.pumps`; a launch
        beyond them fails the test, and a reply that never comes fails it after five seconds."""
        self.pumps: list[threading.Thread] = []
        pumps = self.pumps

        class Recorded(threading.Thread):
            def start(self) -> None:
                pumps.append(self)
                super().start()

        for process in processes:
            self.addCleanup(process.end)
        for patcher in (patch.object(lean_repl.subprocess, "Popen", side_effect=list(processes)),
                        patch.object(lean_repl.threading, "Thread", Recorded)):
            patcher.start()
            self.addCleanup(patcher.stop)
        return session("lake", timeout=5.0, import_timeout=5.0, imports=imports)

    def finish(self, process: FakeProcess, launch: int = 0) -> None:
        """End the output of the process of launch `launch` and wait until its pump has put all of it."""
        process.end()
        self.pumps[launch].join(5)
        self.assertFalse(self.pumps[launch].is_alive())


class RegisteredSession(Sessions):
    """lean_repl.LeanRepl, as the registered experiments run it."""

    def test_the_killed_sessions_end_reaches_the_next_session(self) -> None:
        old, new = FakeProcess(), FakeProcess()
        repl = self.started(lean_repl.LeanRepl, old, new)
        before = repl.lines
        repl.restart()
        self.finish(old)
        self.assertTrue(before.empty())
        self.assertIsNone(repl.lines.get_nowait())

    def test_the_next_exchange_restarts_again_on_it(self) -> None:
        old, new, spare = FakeProcess(), FakeProcess(), FakeProcess()
        repl = self.started(lean_repl.LeanRepl, old, new, spare)
        repl.restart()
        self.finish(old)
        with self.assertRaises(lean_repl.ReplTimeout):
            repl._exchange({"cmd": "def x := 1"}, 5)
        self.assertEqual(repl.restarts, 2)
        self.assertEqual(new.requests, [{"cmd": "def x := 1"}])  # answered, and killed before it was read
        self.assertTrue(new.killed)

    def test_a_restart_that_imports_fails_on_it(self) -> None:
        old, spare = FakeProcess(), FakeProcess()
        new = FakeProcess(on_request=lambda: self.finish(old))
        repl = self.started(lean_repl.LeanRepl, old, new, spare, imports=lean_repl.IMPORT)
        with self.assertRaises(lean_repl.ReplTimeout):
            repl.restart()
        self.assertEqual(repl.restarts, 2)
        self.assertEqual(new.requests, [{"cmd": lean_repl.IMPORT}])

    def test_a_response_of_the_killed_session_answers_the_next_request(self) -> None:
        old, new = FakeProcess(), FakeProcess()
        repl = self.started(lean_repl.LeanRepl, old, new)
        repl.restart()
        old.emit(*STALE)
        self.finish(old)
        self.assertEqual(repl._exchange({"cmd": "import Mathlib.Logic.Basic"}, 5), json.loads(STALE[0]))


class CorrectedSession(Sessions):
    """lean_repl_v2.LeanRepl."""

    def test_the_killed_sessions_output_stays_in_its_queue(self) -> None:
        old, new = FakeProcess(), FakeProcess()
        repl = self.started(lean_repl_v2.LeanRepl, old, new)
        before = repl.lines
        repl.restart()
        old.emit(*STALE)
        self.finish(old)
        self.assertEqual([before.get_nowait() for _ in range(3)], STALE + [None])
        self.assertTrue(repl.lines.empty())
        self.assertEqual(repl._exchange({"cmd": "import Mathlib.Logic.Basic"}, 5), {"env": 1})
        self.assertEqual(repl.restarts, 1)

    def test_a_restart_that_imports_reads_its_own_process(self) -> None:
        old = FakeProcess()
        new = FakeProcess(on_request=lambda: self.finish(old))
        repl = self.started(lean_repl_v2.LeanRepl, old, new, imports=lean_repl.IMPORT)
        before = repl.lines
        repl.restart()
        self.assertIsNone(before.get_nowait())
        self.assertEqual((repl.env, repl.restarts), (1, 1))
        self.assertEqual(new.requests, [{"cmd": lean_repl.IMPORT}])

    def test_a_timeout_restarts_and_raises_the_registered_exception(self) -> None:
        old, new = FakeProcess(answers=False), FakeProcess()
        repl = self.started(lean_repl_v2.LeanRepl, old, new)
        self.assertIs(lean_repl_v2.ReplTimeout, lean_repl.ReplTimeout)
        with self.assertRaises(lean_repl.ReplTimeout):
            repl._exchange({"tactic": "skip", "proofState": 0}, 0.05)
        self.assertTrue(old.killed)
        self.assertEqual(repl.restarts, 1)
        self.assertEqual(repl._exchange({"cmd": "def x := 1"}, 5), {"env": 1})


if __name__ == "__main__":
    unittest.main()
