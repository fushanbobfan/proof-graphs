#!/usr/bin/env python3
"""`lean_repl.LeanRepl` with one correction: a session's output goes only to that session's queue.

`lean_repl.LeanRepl.start` gives each session a new queue, but its pump thread puts every line it reads, and
the `None` that ends the output, into `self.lines` as it is at the moment of the put. After `restart`, the pump
of the killed process can still be draining it when the next session's queue is in place, and what it puts
then lands in the next session: the `None` makes that session's next exchange restart again and raise
`ReplTimeout`, and a response the killed process had finished writing is returned as the answer to the next
request (`test_lean_repl.py` shows both without Lean). Here each pump is handed the queue of its own session.
Everything else is `lean_repl.py`, unchanged, and `ReplTimeout` is its class, so code that catches
`lean_repl.ReplTimeout` catches it from either session. The registered experiments keep `lean_repl.py`, whose
SHA-256 their registrations record.
"""

from __future__ import annotations

import queue
import subprocess
import threading

import lean_repl
from lean_repl import HEARTBEATS, IMPORT, ROOT, ReplTimeout  # noqa: F401 - the names of lean_repl


class LeanRepl(lean_repl.LeanRepl):
    def start(self) -> None:
        self.process = subprocess.Popen([self.lake, "exe", "repl"], cwd=ROOT, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                                        encoding="utf-8", bufsize=1)
        self.lines = queue.Queue()
        threading.Thread(target=self._pump, args=(self.process, self.lines), daemon=True).start()
        if self.imports is not None:
            response = self._exchange({"cmd": self.imports}, self.import_timeout)
            self.env = response["env"]

    @staticmethod
    def _pump(process: subprocess.Popen[str], lines: queue.Queue[str | None]) -> None:  # type: ignore[override]
        assert process.stdout is not None
        for line in process.stdout:
            lines.put(line)
        lines.put(None)
