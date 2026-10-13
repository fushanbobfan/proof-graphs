#!/usr/bin/env python3
"""search-v0.12's seeding, attempt rule with its candidate bank, units, and summary, without Lean or a model."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_search_goals_holdout as goals
from search_harness import State


def state(goal: str) -> State:
    return State(0, 0, [goal], None, None, 0)


def entry(index: int, goal: str, occurrence: int, candidates: list[str], attempt: int = 1) -> dict:
    return {"index": index, "declaration": f"t{index}", "prompt": goal + goals.prover.SEPARATOR,
            "occurrence": occurrence, "candidates": candidates, "attempt": attempt}


def row(declaration: str, search: str, proof: bool = False, expansions: int = 3, index: int = 0, **extra) -> dict:
    out = {"module": f"M{declaration[-1]}", "declaration": declaration, "search": search, "constructed": True,
           "index": index, "attempt": 1,
           "result": {"proof": ["simp"] if proof else None, "exportAttempts": 10, "exportFailures": 0,
                      "expansions": [{"draw": None} for _ in range(expansions)]}}
    return out | extra


class SeedTests(unittest.TestCase):
    def test_sets_are_grouped_by_task_and_goal_in_occurrence_order(self):
        sets = goals.group_sets([entry(0, "A", 1, ["b"]), entry(0, "A", 0, ["a"]), entry(1, "B", 0, ["c"])], "x")
        self.assertEqual(sets, {0: {"A": [["a"], ["b"]]}, 1: {"B": [["c"]]}})

    def test_a_gap_in_a_goals_occurrences_is_refused(self):
        with self.assertRaises(AssertionError):
            goals.group_sets([entry(0, "A", 0, ["a"]), entry(0, "A", 2, ["c"])], "x")

    def test_an_earlier_attempts_draws_continue_the_recorded_sets(self):
        recorded = {0: {"A": [["a"]]}}
        drawn = [entry(0, "A", 1, ["b"]), entry(0, "C", 0, ["c"]), entry(1, "A", 0, ["z"])]
        self.assertEqual(goals.seeds_for(0, recorded, drawn), {"A": [["a"], ["b"]], "C": [["c"]]})
        self.assertEqual(goals.seeds_for(2, recorded, drawn), {})

    def test_a_draw_that_skips_an_occurrence_is_refused(self):
        with self.assertRaises(AssertionError):
            goals.seeds_for(0, {0: {"A": [["a"]]}}, [entry(0, "A", 2, ["c"])])


class UnitTests(unittest.TestCase):
    def test_the_attempt_rule(self):
        self.assertTrue(goals.unit_done([row("t0", "goals")]))
        self.assertFalse(goals.unit_done([]))
        error = {"module": "M", "declaration": "t0", "search": "goals", "constructed": None, "error": "x"}
        self.assertFalse(goals.unit_done([error]))
        self.assertTrue(goals.unit_done([error] * goals.MAX_ATTEMPTS))
        self.assertTrue(goals.unit_done([error, row("t0", "goals")]))
        lost = row("t0", "goals", abandoned="repl timeout")
        self.assertFalse(goals.unit_done([lost]))
        self.assertTrue(goals.unit_done([lost, lost]))
        unposed = {"module": "M", "declaration": "t0", "search": "goals", "constructed": False}
        self.assertFalse(goals.unit_done([unposed]))
        self.assertTrue(goals.unit_done([unposed, unposed]))

    def test_the_unit_runs_the_goal_search_on_its_seeds_then_draws(self):
        calls = []

        def run_one(task, search, propose, budget):
            calls.append((search, budget, "seeds" in task))
            got = [propose(state("A")), propose(state("A")), propose(state("B"))]
            return {"module": task["module"], "declaration": task["declaration"], "search": search,
                    "constructed": True, "result": {"proof": None, "expansions": [], "got": got}}

        def draw(self_, goal):
            return [f"new{len(self_.log)}"], {"prompt": goal + goals.prover.SEPARATOR, "replies": [], "candidates": []}

        with patch.object(goals.guarded, "run_one", run_one), patch.object(goals.v8.ReplicateDraws, "draw", draw):
            rows, log = goals.run_unit({"module": "M", "declaration": "t0", "index": 7, "attempt": 2,
                                        "seeds": {"A": [["seeded"]]}})
        self.assertEqual(calls, [("goals", goals.BUDGET, False)])
        self.assertEqual(rows[0]["result"]["got"], [["seeded"], ["new0"], ["new1"]])
        self.assertEqual(rows[0]["draws"], {"seeded": 1, "shared": 0, "drawn": 2})
        self.assertEqual((rows[0]["index"], rows[0]["attempt"]), (7, 2))
        self.assertEqual([(e["index"], e["attempt"], e["occurrence"]) for e in log], [(7, 2, 1), (7, 2, 0)])


class PassTests(unittest.TestCase):
    def test_a_repeat_reuses_what_the_earlier_attempt_drew(self):
        tasks = [{"module": "M0", "declaration": "t0", "index": 0}, {"module": "M1", "declaration": "t1", "index": 1}]
        recorded = {0: {"A": [["a"]]}}
        seen = []

        def unit(task):
            seen.append((task["declaration"], task["attempt"], task["seeds"]))
            if task["declaration"] == "t0" and task["attempt"] == 1:
                return [row("t0", "goals", abandoned="repl timeout", attempt=1)], [entry(0, "A", 1, ["b"])]
            return [row(task["declaration"], "goals", index=task["index"], attempt=task["attempt"])], []

        with tempfile.TemporaryDirectory() as tmp, patch.object(goals, "RESULTS", Path(tmp) / "results.jsonl"), \
                patch.object(goals, "DRAWS", Path(tmp) / "draws.jsonl.gz"), \
                patch.object(goals, "unit_in_child", unit), patch.object(goals.deep, "admit", lambda: None):
            self.assertEqual(goals.run_pass(tasks, recorded, 1), 2)
            self.assertEqual(goals.done_tasks(goals.read_rows()), {"t1"})
            self.assertEqual(goals.run_pass(tasks, recorded, 1), 1)
            self.assertEqual(goals.done_tasks(goals.read_rows()), {"t0", "t1"})
            self.assertEqual(goals.run_pass(tasks, recorded, 1), 0)
            self.assertEqual(len(goals.read_draws()), 1)
        self.assertEqual(sorted(seen)[:2], [("t0", 1, {"A": [["a"]]}), ("t0", 2, {"A": [["a"], ["b"]]})])
        self.assertIn(("t1", 1, {}), seen)


class SummaryTests(unittest.TestCase):
    def summarize(self, rows: list[dict], confirm_rows: list[dict], recorded: dict, tasks: list[dict],
                  draws: list[dict] | None = None) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            prereg, results = Path(tmp) / "preregistration.json", Path(tmp) / "results.jsonl"
            prereg.write_text("{}", encoding="utf-8")
            results.write_text("", encoding="utf-8")
            with patch.object(goals, "PREREG", prereg), patch.object(goals, "RESULTS", results), \
                    patch.object(goals, "DRAWS", Path(tmp) / "draws.jsonl.gz"), \
                    patch.object(goals.rc, "read_rows", lambda: confirm_rows), \
                    patch.object(goals, "recorded_sets", lambda: recorded):
                return goals.summarize(rows, draws or [], tasks)

    def test_pairs_tests_and_hypotheses(self):
        tasks = [{"module": f"M{i}", "declaration": f"t{i}", "index": i} for i in range(6)]
        # (groups, whole) from search-v0.11 and goals from this experiment
        proofs = {"t0": (True, True, True), "t1": (True, False, True), "t2": (True, False, False),
                  "t3": (False, False, True), "t4": (False, False, False), "t5": (False, False, False)}
        confirm_rows = [row(t, s, proof=p) for t, (g, w, _) in proofs.items() for s, p in (("groups", g), ("whole", w))]
        seeded = {"draw": {"goal": goals.goal_hash("A"), "n": 0, "source": "seeded"}}
        rows = [row(t, "goals", proof=o, index=int(t[1])) for t, (_, _, o) in proofs.items()]
        rows[0]["result"]["expansions"] = [seeded, {"draw": {"goal": goals.goal_hash("A"), "n": 1, "source": "drawn"}}]
        s = self.summarize(rows, confirm_rows, {0: {"A": [["a"]]}}, tasks)
        self.assertEqual(s["stated"], 6)
        self.assertEqual(s["proved"]["goals"]["48"], 3)
        self.assertEqual(s["pairs"]["groupsOverGoals"]["cells"], {"both": 2, "firstOnly": 1, "secondOnly": 1, "neither": 2})
        self.assertEqual(s["pairs"]["goalsOverWhole"]["cells"], {"both": 1, "firstOnly": 2, "secondOnly": 0, "neither": 3})
        self.assertEqual(s["pairs"]["goalsOverWhole"]["signTestFirstMore"], 0.25)
        self.assertTrue(s["hypotheses"]["H112"]["holds"])
        self.assertFalse(s["hypotheses"]["H113"]["holds"])
        self.assertFalse(s["hypotheses"]["H114"]["holds"])  # six tasks cannot bound the difference below a point
        self.assertEqual(s["checks"]["C47"], {"seeded": 1, "recorded": 1, "holds": True})
        self.assertTrue(s["checks"]["C46"]["holds"])

    def test_a_seeded_set_not_recorded_fails_the_seed_check(self):
        tasks = [{"module": "M0", "declaration": "t0", "index": 0}]
        confirm_rows = [row("t0", s) for s in goals.PAIRED]
        rows = [row("t0", "goals")]
        rows[0]["result"]["expansions"] = [{"draw": {"goal": goals.goal_hash("A"), "n": 1, "source": "seeded"}}]
        s = self.summarize(rows, confirm_rows, {0: {"A": [["a"]]}}, tasks)
        self.assertFalse(s["checks"]["C47"]["holds"])
        # unless an earlier attempt of the unit drew that occurrence
        rows[0]["attempt"] = 2
        s = self.summarize(rows, confirm_rows, {0: {"A": [["a"]]}}, tasks, [entry(0, "A", 1, ["b"], attempt=1)])
        self.assertTrue(s["checks"]["C47"]["holds"])


if __name__ == "__main__":
    unittest.main()
