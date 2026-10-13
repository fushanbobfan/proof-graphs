#!/usr/bin/env python3
"""search-v0.13's units, rotation, attempt rule with its candidate bank, power simulation, and summary, without Lean
or a model."""

from __future__ import annotations

import random
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_search_replicates_holdout as rep
from search_harness import State


def state(goal: str) -> State:
    return State(0, 0, [goal], None, None, 0)


def entry(index: int, replicate: int, goal: str, occurrence: int, candidates: list[str], attempt: int = 1) -> dict:
    return {"index": index, "replicate": replicate, "declaration": f"t{index}", "attempt": attempt,
            "prompt": goal + rep.prover.SEPARATOR, "occurrence": occurrence, "candidates": candidates}


def row(declaration: str, search: str, replicate: int, proof: bool = False, index: int = 0, attempt: int = 1,
        **extra) -> dict:
    out = {"module": f"M{declaration[-1]}", "declaration": declaration, "search": search, "replicate": replicate,
           "index": index, "attempt": attempt, "constructed": True,
           "result": {"proof": ["simp"] if proof else None, "exportAttempts": 10, "exportFailures": 0, "groups":
                      {"single": 1, "several": 0}, "groupsInProof": 0,
                      "expansions": [{"orderDuplicate": False, "goalDuplicate": False, "draw": None}]}}
    return out | extra


class SeedTests(unittest.TestCase):
    def test_a_unit_reuses_only_its_own_earlier_draws(self):
        drawn = [entry(0, 1, "A", 0, ["a"]), entry(0, 1, "A", 1, ["b"]), entry(0, 2, "A", 0, ["z"]),
                 entry(1, 1, "A", 0, ["y"])]
        self.assertEqual(rep.seeds_for(0, 1, drawn), {"A": [["a"], ["b"]]})
        self.assertEqual(rep.seeds_for(0, 2, drawn), {"A": [["z"]]})
        self.assertEqual(rep.seeds_for(2, 1, drawn), {})

    def test_a_gap_is_refused(self):
        with self.assertRaises(AssertionError):
            rep.seeds_for(0, 1, [entry(0, 1, "A", 1, ["b"])])


class UnitTests(unittest.TestCase):
    def test_the_attempt_rule(self):
        clean = [row("t0", s, 1) for s in rep.SEARCHES]
        self.assertTrue(rep.unit_done(clean))
        self.assertFalse(rep.unit_done(clean[:2]))
        lost = clean[:2] + [row("t0", "groups", 1, abandoned="repl timeout")]
        self.assertFalse(rep.unit_done(lost))
        self.assertTrue(rep.unit_done(lost + lost))
        error = [{"module": "M", "declaration": "t0", "search": s, "replicate": 1, "constructed": None, "error": "x"}
                 for s in rep.SEARCHES]
        self.assertFalse(rep.unit_done(error))
        self.assertTrue(rep.unit_done(error * rep.MAX_ATTEMPTS))

    def test_three_searches_share_one_stream_in_a_rotating_order(self):
        calls = []

        def run_one(task, search, propose, budget):
            calls.append(search)
            self.assertNotIn("seeds", task)
            got = [propose(state("A")), propose(state("B"))]
            return {"module": task["module"], "declaration": task["declaration"], "search": search,
                    "constructed": True, "result": {"proof": None, "expansions": [], "got": got}}

        def draw(self_, goal):
            return [f"new{len(self_.log)}"], {"prompt": goal + rep.prover.SEPARATOR, "replies": [], "candidates": []}

        with patch.object(rep.guarded, "run_one", run_one), patch.object(rep.v8.ReplicateDraws, "draw", draw):
            rows, log = rep.run_unit({"module": "M", "declaration": "t0", "index": 0, "replicate": 1, "attempt": 1,
                                      "seeds": {"A": [["kept"]]}})
            self.assertEqual(calls, list(rep.ORDERS[1]))
            self.assertEqual([r["result"]["got"] for r in rows], [[["kept"], ["new0"]]] * 3)
            self.assertEqual([r["draws"] for r in rows], [{"seeded": 1, "shared": 0, "drawn": 1},
                                                          {"seeded": 1, "shared": 1, "drawn": 0},
                                                          {"seeded": 1, "shared": 1, "drawn": 0}])
            self.assertEqual([(e["replicate"], e["attempt"], e["occurrence"]) for e in log], [(1, 1, 0)])
            calls.clear()
            rep.run_unit({"module": "M", "declaration": "t2", "index": 2, "replicate": 2, "attempt": 1, "seeds": {}})
            self.assertEqual(calls, list(rep.ORDERS[(2 + 2) % 3]))


class PassTests(unittest.TestCase):
    def test_set_one_runs_first_and_a_repeat_reuses_its_draws(self):
        tasks = [{"module": "M0", "declaration": "t0", "index": 0}, {"module": "M1", "declaration": "t1", "index": 1}]
        seen = []

        def unit(task):
            seen.append((task["replicate"], task["declaration"], task["attempt"], task["seeds"]))
            r, k, a = task["declaration"], task["replicate"], task["attempt"]
            if (r, k, a) == ("t0", 1, 1):
                return ([row(r, s, k, index=0, attempt=a) for s in ("whole", "goals")]
                        + [row(r, "groups", k, index=0, attempt=a, abandoned="repl timeout")],
                        [entry(0, 1, "A", 0, ["a"])])
            return [row(r, s, k, index=task["index"], attempt=a) for s in rep.SEARCHES], []

        with tempfile.TemporaryDirectory() as tmp, patch.object(rep, "RESULTS", Path(tmp) / "results.jsonl"), \
                patch.object(rep, "DRAWS", Path(tmp) / "draws.jsonl.gz"), \
                patch.object(rep, "unit_in_child", unit), patch.object(rep.deep, "admit", lambda: None):
            self.assertEqual(rep.run_pass(tasks, 1), 4)
            self.assertEqual([s[:2] for s in seen], [(1, "t0"), (1, "t1"), (2, "t0"), (2, "t1")])
            self.assertEqual(rep.done_units(rep.read_rows()), {"1:t1", "2:t0", "2:t1"})
            self.assertEqual(rep.run_pass(tasks, 1), 1)
            self.assertEqual(seen[-1], (1, "t0", 2, {"A": [["a"]]}))
            self.assertEqual(rep.run_pass(tasks, 1), 0)


class PowerTests(unittest.TestCase):
    def test_power_follows_the_pilot_patterns(self):
        always = [((True, False),) * 3] * 5 + [((False, False),) * 3] * 5
        never = [((True, True),) * 3, ((False, False),) * 3]
        with patch.object(rep, "SIMULATION_RUNS", 50):
            self.assertEqual(rep.simulate_power(200, always, random.Random(0))["signTestPower"], 1.0)
            self.assertEqual(rep.simulate_power(200, never, random.Random(0))["signTestPower"], 0.0)


class SummaryTests(unittest.TestCase):
    def summarize(self, rows: list[dict], tasks: list[dict], draws: list[dict] | None = None) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            prereg, results = Path(tmp) / "preregistration.json", Path(tmp) / "results.jsonl"
            prereg.write_text("{}", encoding="utf-8")
            results.write_text("", encoding="utf-8")
            with patch.object(rep, "PREREG", prereg), patch.object(rep, "RESULTS", results), \
                    patch.object(rep, "DRAWS", Path(tmp) / "draws.jsonl.gz"):
                return rep.summarize(rows, draws or [], tasks)

    def test_scores_comparisons_and_hypotheses(self):
        tasks = [{"module": f"M{i}", "declaration": f"t{i}", "index": i} for i in range(4)]
        # per task and set: (whole, goals, groups) proves
        outcome = {("t0", 1): (1, 1, 1), ("t0", 2): (1, 1, 1), ("t1", 1): (0, 1, 1), ("t1", 2): (0, 0, 1),
                   ("t2", 1): (0, 0, 1), ("t2", 2): (0, 0, 0), ("t3", 1): (0, 0, 0), ("t3", 2): (0, 0, 0)}
        rows = [row(t, s, k, proof=bool(p), index=int(t[1])) for (t, k), ps in outcome.items()
                for s, p in zip(rep.SEARCHES, ps)]
        s = self.summarize(rows, tasks)
        self.assertEqual(s["stated"], 4)
        gw = s["pairs"]["groupsOverWhole"]
        self.assertEqual((gw["tasksFirstMore"], gw["tasksSecondMore"]), (2, 0))
        self.assertEqual(gw["signTestFirstMore"], 0.25)
        self.assertAlmostEqual(gw["meanRateDifference"], 3 / 8)
        go = s["pairs"]["groupsOverGoals"]
        self.assertEqual((go["tasksFirstMore"], go["tasksSecondMore"]), (2, 0))
        self.assertEqual(gw["perSet"], {"1": {"firstOnly": 2, "secondOnly": 0}, "2": {"firstOnly": 1, "secondOnly": 0}})
        self.assertFalse(s["hypotheses"]["H115"]["holds"])
        self.assertTrue(s["hypotheses"]["H117"]["holds"])
        self.assertFalse(s["hypotheses"]["H118"]["holds"])
        self.assertTrue(s["checks"]["C50"]["holds"])
        self.assertTrue(s["checks"]["C49"]["holds"])

    def test_a_set_drawn_twice_fails_the_stream_check(self):
        tasks = [{"module": "M0", "declaration": "t0", "index": 0}]
        rows = [row("t0", s, k) for k in rep.REPLICATES for s in rep.SEARCHES]
        s = self.summarize(rows, tasks, [entry(0, 1, "A", 0, ["a"]), entry(0, 1, "A", 0, ["b"], attempt=2)])
        self.assertFalse(s["checks"]["C50"]["holds"])


if __name__ == "__main__":
    unittest.main()
