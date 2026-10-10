#!/usr/bin/env python3
"""search-v0.11's units, attempt rule, sample-size rule, and summary, without Lean or a model."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import run_search_confirm as confirm
from search_harness import State


def state(goal: str) -> State:
    return State(0, 0, [goal], None, None, 0)


def row(declaration: str, search: str, proof: bool = False, expansions: int = 3, **extra) -> dict:
    out = {"module": f"M{declaration[-1]}", "declaration": declaration, "search": search, "constructed": True,
           "result": {"proof": ["simp"] if proof else None, "exportAttempts": 10, "exportFailures": 0,
                      "expansions": [{"orderDuplicate": False, "goalDuplicate": i == 0} for i in range(expansions)]}}
    return out | extra


class UnitTests(unittest.TestCase):
    def test_a_clean_unit_is_final(self):
        self.assertTrue(confirm.unit_done([row("t0", "whole"), row("t0", "groups")]))
        self.assertFalse(confirm.unit_done([row("t0", "whole")]))

    def test_an_error_is_retried_up_to_the_attempts_allowed(self):
        error = {"module": "M", "declaration": "t0", "constructed": None, "error": "RuntimeError: x"}
        once = [error | {"search": "whole"}, error | {"search": "groups"}]
        self.assertFalse(confirm.unit_done(once))
        self.assertTrue(confirm.unit_done(once * confirm.MAX_ATTEMPTS))
        self.assertTrue(confirm.unit_done(once + [row("t0", "whole"), row("t0", "groups")]))

    def test_a_task_not_posed_is_tried_twice(self):
        unposed = [{"module": "M", "declaration": "t0", "search": s, "constructed": False} for s in confirm.SEARCHES]
        self.assertFalse(confirm.unit_done(unposed))
        self.assertTrue(confirm.unit_done(unposed * 2))

    def test_a_search_that_lost_its_session_is_tried_twice(self):
        lost = [row("t0", "whole"), {"module": "M0", "declaration": "t0", "search": "groups", "constructed": True,
                                     "abandoned": "repl timeout"}]
        self.assertFalse(confirm.unit_done(lost))
        self.assertTrue(confirm.unit_done(lost * 2))

    def test_the_two_searches_share_draws_in_alternating_order(self):
        calls = []

        def run_one(task, search, propose, budget):
            calls.append(search)
            self.assertEqual(budget, confirm.BUDGET)
            first, second = propose(state("A")), propose(state("A"))
            return {"module": task["module"], "declaration": task["declaration"], "search": search,
                    "constructed": True, "result": {"proof": None, "expansions": [], "candidates": [first, second]}}

        def draw(self_, goal):
            return [f"tac{len(self_.log)}"], {"prompt": goal + ":::", "replies": [], "candidates": []}

        with patch.object(confirm.guarded, "run_one", run_one), patch.object(confirm.v8.ReplicateDraws, "draw", draw):
            rows, log = confirm.run_unit({"module": "M", "declaration": "t0", "index": 0})
            self.assertEqual(calls, ["whole", "groups"])
            self.assertEqual(rows[0]["result"]["candidates"], rows[1]["result"]["candidates"])
            self.assertEqual(rows[0]["draws"], {"seeded": 0, "shared": 0, "drawn": 2})
            self.assertEqual(rows[1]["draws"], {"seeded": 0, "shared": 2, "drawn": 0})
            self.assertEqual([(e["index"], e["declaration"], e["occurrence"]) for e in log], [(0, "t0", 0), (0, "t0", 1)])
            calls.clear()
            rows, _ = confirm.run_unit({"module": "M", "declaration": "t1", "index": 1})
            self.assertEqual(calls, ["groups", "whole"])
            self.assertEqual([r["position"] for r in rows], [0, 1])


class ProcessTests(unittest.TestCase):
    """The unit's own process, emulated in this one: what the child writes is what the runner records."""

    def fake_run(self, unit_rows, returncode=0):
        def run(command, **kwargs):
            self.assertEqual(command[2:4], [str(Path(confirm.__file__).resolve()), "--unit"])
            if returncode == 0:
                with patch.object(confirm, "run_unit", lambda task: (unit_rows(task), [{"index": task["index"]}])):
                    confirm.child_main(Path(command[4]), Path(command[5]))
            return SimpleNamespace(returncode=returncode, stdout="", stderr="Traceback ...\nRuntimeError: boom")
        return run

    def test_a_unit_comes_back_whole_from_its_process(self):
        rows = lambda task: [row(task["declaration"], s, proof=True) for s in confirm.SEARCHES]  # noqa: E731
        with patch.object(confirm.subprocess, "run", self.fake_run(rows)), \
                patch.object(confirm.prover, "ENDPOINT", "unset"):
            got, log = confirm.unit_in_child({"module": "M0", "declaration": "t0", "index": 3})
            self.assertEqual(confirm.prover.ENDPOINT, confirm.deep.ENDPOINT)
        self.assertEqual(got, rows({"declaration": "t0"}))
        self.assertEqual(log, [{"index": 3}])

    def test_a_failed_process_raises_with_its_reason(self):
        with patch.object(confirm.subprocess, "run", self.fake_run(None, returncode=1)):
            with self.assertRaisesRegex(RuntimeError, "exited with 1: .*boom"):
                confirm.unit_in_child({"module": "M0", "declaration": "t0", "index": 0})

    def test_a_pass_records_every_unit_once(self):
        tasks = [{"module": f"M{i}", "declaration": f"t{i}", "index": i} for i in range(5)]

        def unit(task):
            return ([row(task["declaration"], s) for s in confirm.SEARCHES],
                    [{"index": task["index"], "declaration": task["declaration"], "prompt": "A:::"}])

        with tempfile.TemporaryDirectory() as tmp, patch.object(confirm, "RESULTS", Path(tmp) / "results.jsonl"), \
                patch.object(confirm, "DRAWS", Path(tmp) / "draws.jsonl.gz"), \
                patch.object(confirm, "unit_in_child", unit), patch.object(confirm.deep, "admit", lambda: None):
            self.assertEqual(confirm.run_pass(tasks, 2), 5)
            self.assertEqual(len(confirm.read_rows()), 10)
            self.assertEqual(confirm.done_tasks(confirm.read_rows()), {t["declaration"] for t in tasks})
            self.assertEqual([e["index"] for e in confirm.read_draws()], [0, 1, 2, 3, 4])
            self.assertEqual(confirm.run_pass(tasks, 2), 0)


class SummaryTests(unittest.TestCase):
    def summarize(self, rows: list[dict], tasks: list[dict]) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            prereg, results = Path(tmp) / "preregistration.json", Path(tmp) / "results.jsonl"
            prereg.write_text("{}", encoding="utf-8")
            results.write_text("", encoding="utf-8")
            with patch.object(confirm, "PREREG", prereg), patch.object(confirm, "RESULTS", results), \
                    patch.object(confirm, "DRAWS", Path(tmp) / "draws.jsonl.gz"):
                return confirm.summarize(rows, [], tasks)

    def test_cells_tests_and_shares(self):
        tasks = [{"module": f"M{i}", "declaration": f"t{i}"} for i in range(6)]
        proofs = {"t0": (True, True), "t1": (True, False), "t2": (True, False), "t3": (False, False),
                  "t4": (False, False)}
        rows = [row(t, s, proof=p) for t, (g, w) in proofs.items() for s, p in (("groups", g), ("whole", w))]
        rows += [{"module": "M5", "declaration": "t5", "search": s, "constructed": False} for s in confirm.SEARCHES]
        s = self.summarize(rows, tasks)
        self.assertEqual(s["stated"], 5)
        self.assertEqual(s["cells"], {"both": 1, "groupsOnly": 2, "wholeOnly": 0, "neither": 2})
        self.assertAlmostEqual(s["difference"], 2 / 5)
        self.assertEqual(s["signTestGroupsMore"], 0.25)
        lower, upper = s["newcombe95"]
        self.assertLess(lower, 2 / 5)
        self.assertGreater(upper, 2 / 5)
        self.assertTrue(s["hypotheses"]["H109"]["holds"])
        self.assertFalse(s["hypotheses"]["H110"]["holds"])
        self.assertAlmostEqual(s["duplicates"]["goalShare"], 1 / 3)
        self.assertFalse(s["hypotheses"]["H111"]["holds"])
        self.assertTrue(s["checks"]["C44"]["holds"])
        self.assertFalse(s["checks"]["C43"]["final"])  # t5 was tried once

    def test_no_discordant_task_is_no_significant_gain(self):
        tasks = [{"module": "M0", "declaration": "t0"}, {"module": "M1", "declaration": "t1"}]
        rows = [row(t, s, proof=t == "t0", expansions=30) for t in ("t0", "t1") for s in confirm.SEARCHES]
        s = self.summarize(rows, tasks)
        self.assertIsNone(s["signTestGroupsMore"])
        self.assertTrue(s["hypotheses"]["H109"]["holds"])
        self.assertEqual(s["difference"], 0)

    def test_newcombe_is_symmetric_without_a_difference(self):
        lower, upper = confirm.newcombe(40, 5, 5, 350)
        self.assertAlmostEqual(lower, -upper)
        self.assertLess(upper, 0.03)


class SampleSizeTests(unittest.TestCase):
    def size(self, cells: dict) -> dict:
        with patch.object(confirm, "pilot_cells", lambda: cells), patch.object(confirm, "SIMULATION_RUNS", 300):
            return confirm.sample_size(826)

    def test_the_smallest_size_that_reaches_the_target(self):
        out = self.size({"both": 120, "groupsOnly": 0, "wholeOnly": 0, "neither": 350})
        self.assertEqual(out["chosen"], confirm.SIZES[0])
        self.assertEqual(out, self.size({"both": 120, "groupsOnly": 0, "wholeOnly": 0, "neither": 350}))

    def test_every_candidate_when_no_size_reaches_it(self):
        out = self.size({"both": 100, "groupsOnly": 40, "wholeOnly": 0, "neither": 330})
        self.assertEqual(out["chosen"], 826)
        self.assertEqual(list(out["simulation"]), [str(s) for s in confirm.SIZES] + ["826"])


if __name__ == "__main__":
    unittest.main()
