#!/usr/bin/env python3
"""search-cost-v0.1's accounting, rotation, memory poll, and summary, without Lean or a model."""

from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import run_search_cost as cost
from search_harness import State


def state(goal: str) -> State:
    return State(0, 0, [goal], None, None, 0)


def row(declaration: str, search: str, elapsed: float, model: float, export: float, proof: bool = False,
        **extra) -> dict:
    return {"module": "M", "declaration": declaration, "search": search, "constructed": True, "index": 0,
            "elapsedSeconds": elapsed, "peakMemoryMB": 5000.0,
            "model": {"requests": 3, "completions": 48, "promptTokens": 300, "completionTokens": 40, "seconds": model},
            "costs": {"tactic": {"calls": 10, "seconds": 1.0}, "export": {"calls": 5, "seconds": export},
                      "command": {"calls": 2, "seconds": 2.0}},
            "result": {"proof": ["simp"] if proof else None, "expansions": []}} | extra


class AccountingTests(unittest.TestCase):
    def test_a_search_pays_for_its_own_draws(self):
        def run_one(task, search, propose, budget):
            self.assertEqual((search, budget), ("groups", cost.BUDGET))
            propose(state("A")), propose(state("A")), propose(state("B"))
            return {"module": task["module"], "declaration": task["declaration"], "search": search,
                    "constructed": True, "result": {"proof": None, "expansions": []}}

        def draw(self_, goal):
            return ["t"], {"prompt": goal + ":::", "replies": [], "candidates": ["t"], "promptTokens": 100,
                           "completionTokens": 7, "seconds": 2.5}

        with patch.object(cost.guarded, "run_one", run_one), patch.object(cost.v8.ReplicateDraws, "draw", draw):
            got = cost.run_search({"module": "M", "declaration": "t0", "index": 4, "search": "groups", "position": 1})
        self.assertEqual(got["model"], {"requests": 3, "completions": 3 * cost.v8.SAMPLES, "promptTokens": 300,
                                        "completionTokens": 21, "seconds": 7.5})
        self.assertEqual((got["index"], got["position"]), (4, 1))

    def test_components(self):
        self.assertEqual(cost.components(row("t0", "whole", 10, 6, 0.5)),
                         {"model": 6, "tactic": 1.0, "export": 0.5, "command": 2.0})

    def test_the_peak_memory_of_a_running_process(self):
        with cost.PeakMemory(os.getpid()) as memory:
            pass
        self.assertGreater(memory.peak, 0)


class RunTests(unittest.TestCase):
    def test_searches_rotate_and_a_resume_skips_what_ran(self):
        tasks = [{"module": "M", "declaration": f"t{i}", "index": i} for i in range(2)]
        calls = []

        def child(task):
            calls.append((task["declaration"], task["search"], task["position"]))
            return row(task["declaration"], task["search"], 10, 6, 0.5)

        with tempfile.TemporaryDirectory() as tmp, patch.object(cost, "RESULTS", Path(tmp) / "results.jsonl"), \
                patch.object(cost, "search_in_child", child), patch.object(cost, "other_runners", lambda: []), \
                patch.object(cost.deep, "server_alive", lambda: True):
            cost.run_all(tasks)
            self.assertEqual(calls[:3], [("t0", s, p) for p, s in enumerate(cost.ORDERS[0])])
            self.assertEqual(calls[3:], [("t1", s, p) for p, s in enumerate(cost.ORDERS[1])])
            calls.clear()
            cost.run_all(tasks)
            self.assertEqual(calls, [])

    def test_other_runners_are_found_by_their_command_lines(self):
        procs = [SimpleNamespace(info={"cmdline": ["python", "scripts/run_search_replicates_holdout.py", "--run"]}),
                 SimpleNamespace(info={"cmdline": ["python", "other.py"]})]
        with patch.object(cost.psutil, "process_iter", lambda attrs: procs):
            self.assertEqual(len(cost.other_runners()), 1)


class SummaryTests(unittest.TestCase):
    def summarize(self, rows: list[dict], tasks: list[dict]) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            prereg, results = Path(tmp) / "preregistration.json", Path(tmp) / "results.jsonl"
            prereg.write_text("{}", encoding="utf-8")
            results.write_text("", encoding="utf-8")
            with patch.object(cost, "PREREG", prereg), patch.object(cost, "RESULTS", results):
                return cost.summarize(rows, tasks)

    def test_ratios_shares_and_hypotheses(self):
        tasks = [{"module": "M", "declaration": f"t{i}", "index": i} for i in range(3)]
        rows = []
        for i, t in enumerate(tasks):
            rows += [row(t["declaration"], "whole", 10.0, 6.0, 0.5), row(t["declaration"], "goals", 11.0, 6.0, 3.0),
                     row(t["declaration"], "groups", 12.0 + i, 7.0, 1.0)]
        s = self.summarize(rows, tasks)
        self.assertAlmostEqual(s["ratios"]["groupsOverWhole"]["median"], 1.3)
        self.assertFalse(s["hypotheses"]["H123"]["holds"])
        self.assertTrue(s["hypotheses"]["H122"]["holds"])
        self.assertAlmostEqual(s["searches"]["goals"]["medianExportShare"], 3 / 11)
        self.assertFalse(s["hypotheses"]["H124"]["holds"])  # the goal search's exports take more than a fifth
        self.assertTrue(s["checks"]["C53"]["holds"])
        self.assertTrue(s["checks"]["C54"]["holds"])

    def test_an_error_or_a_crowded_run_fails_the_checks(self):
        tasks = [{"module": "M", "declaration": "t0", "index": 0}]
        rows = [row("t0", "whole", 10, 6, 0.5, othersRunning=["python run_search_goals_holdout.py"]),
                row("t0", "goals", 10, 6, 0.5), {"declaration": "t0", "search": "groups", "error": "x"}]
        s = self.summarize(rows, tasks)
        self.assertFalse(s["checks"]["C53"]["holds"])
        self.assertFalse(s["checks"]["C54"]["holds"])


if __name__ == "__main__":
    unittest.main()
