#!/usr/bin/env python3
"""A session of the Lean REPL (`lake exe repl`) with a full-Mathlib environment.

`LeanRepl.command(text)` runs a command in the imported environment and
returns the response; `LeanRepl.tactic(proof_state, text)` applies one tactic
to a proof state and returns `(goals, proof_state)` on success, `None` on a
Lean error, and raises `ReplTimeout` when the tactic exceeds the wall-clock
limit, after which the session is restarted (about a minute with the OS cache
warm). Every tactic runs under a heartbeat limit so that runaway tactics fail
inside Lean instead of hanging the session.
"""

from __future__ import annotations

import json
import queue
import subprocess
import threading
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
IMPORT = "import Mathlib"
HEARTBEATS = 40000


class ReplTimeout(Exception):
    pass


class LeanRepl:
    def __init__(self, lake: str, timeout: float = 60.0, import_timeout: float = 900.0,
                 imports: str | None = IMPORT) -> None:
        self.lake = lake
        self.timeout = timeout
        self.import_timeout = import_timeout
        self.imports = imports
        self.process: subprocess.Popen[str] | None = None
        self.lines: queue.Queue[str | None] = queue.Queue()
        self.env: int | None = None
        self.restarts = 0
        self.start()

    def start(self) -> None:
        self.process = subprocess.Popen([self.lake, "exe", "repl"], cwd=ROOT, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                                        encoding="utf-8", bufsize=1)
        self.lines = queue.Queue()
        threading.Thread(target=self._pump, args=(self.process,), daemon=True).start()
        if self.imports is not None:
            response = self._exchange({"cmd": self.imports}, self.import_timeout)
            self.env = response["env"]

    def _pump(self, process: subprocess.Popen[str]) -> None:
        assert process.stdout is not None
        for line in process.stdout:
            self.lines.put(line)
        self.lines.put(None)

    def _exchange(self, request: dict[str, Any], timeout: float) -> dict[str, Any]:
        assert self.process is not None and self.process.stdin is not None
        self.process.stdin.write(json.dumps(request, ensure_ascii=False) + "\n\n")
        self.process.stdin.flush()
        deadline = time.monotonic() + timeout
        chunks: list[str] = []
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                self.restart()
                raise ReplTimeout(request)
            try:
                line = self.lines.get(timeout=remaining)
            except queue.Empty:
                self.restart()
                raise ReplTimeout(request)
            if line is None:
                self.restart()
                raise ReplTimeout(request)
            if line.strip() == "" and chunks:
                text = "".join(chunks)
                try:
                    return json.loads(text)
                except json.JSONDecodeError:
                    continue  # a blank line inside a pretty-printed response
            if line.strip() != "" or chunks:
                chunks.append(line)

    def restart(self) -> None:
        if self.process is not None:
            self.process.kill()
            self.process.wait()
        self.restarts += 1
        self.start()

    def command(self, text: str) -> dict[str, Any]:
        return self._exchange({"cmd": text, "env": self.env}, self.timeout * 4)

    def tactic(self, proof_state: int, text: str) -> tuple[list[str], int] | None:
        guarded = f"set_option maxHeartbeats {HEARTBEATS} in ({text})"
        response = self._exchange({"tactic": guarded, "proofState": proof_state}, self.timeout)
        if "goals" not in response or "proofState" not in response:
            return None
        if any(m.get("severity") == "error" for m in response.get("messages", [])):
            return None
        return list(response["goals"]), int(response["proofState"])

    def close(self) -> None:
        if self.process is not None:
            self.process.kill()
            self.process.wait()
            self.process = None
