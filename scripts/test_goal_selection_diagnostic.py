#!/usr/bin/env python3
"""Goal-selection diagnostic tests on synthetic rows (no Lean).

  python -B scripts/test_goal_selection_diagnostic.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_goal_selection_diagnostic as diagnostic  # noqa: E402
import run_search_goal_selection as runner  # noqa: E402


def unit(task: dict, arm: str, proved: bool, coupled: bool | None = None) -> dict:
    proof = ["pick_goal 3", "rfl", "simp"] if proved else None
    probe = None if coupled is None else {
        "closed": True, "steps": [{"position": 3, "chosenCoupled": coupled}, {"position": 1, "chosenCoupled": False}]}
    return {"module": "development", "declaration": task["declaration"], "arm": arm,
            "result": {"proof": proof, "steps": 30, "stepsAtProof": 30 if proved else None,
                       "expansions": [{}] * 3}, "probe": probe}


def outcome(coupled_first: bool = False, free_coupled: bool | None = True,
            independent_first: bool = True) -> list[dict]:
    rows = []
    for task in diagnostic.TASKS:
        for arm in runner.ARMS:
            if task["kind"] == "coupled":
                free = arm in ("any", "anyMultiset")
                rows.append(unit(task, arm, free or coupled_first,
                                 free_coupled if free and arm != "firstText" else None))
            else:
                rows.append(unit(task, arm, arm != "first" or independent_first))
    return rows


class Diagnostic(unittest.TestCase):
    def test_tasks_are_new_and_balanced(self):
        names = [t["declaration"] for t in diagnostic.TASKS]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(sum(t["kind"] == "coupled" for t in diagnostic.TASKS), 10)
        self.assertEqual(sum(t["kind"] == "independent" for t in diagnostic.TASKS), 8)
        used = {c["statement"] for c in runner.CONTROLS}
        self.assertFalse(used & {t["statement"] for t in diagnostic.TASKS})

    def test_expected_outcome_holds_every_prediction(self):
        summary = diagnostic.summarize(outcome())
        self.assertTrue(summary["complete"])
        self.assertEqual(summary["predictions"], {"D1": "holds", "D2": "holds", "D3": "holds", "D4": "holds"})

    def test_each_prediction_can_fail(self):
        self.assertEqual(diagnostic.summarize(outcome(coupled_first=True))["predictions"]["D1"], "fails")
        self.assertEqual(diagnostic.summarize(outcome(free_coupled=False))["predictions"]["D3"], "fails")
        self.assertEqual(diagnostic.summarize(outcome(free_coupled=None))["predictions"]["D3"], "fails")
        self.assertEqual(diagnostic.summarize(outcome(independent_first=False))["predictions"]["D4"], "fails")
        rows = [r for r in outcome() if not (r["declaration"] == "pair_sum" and r["arm"] == "any")]
        rows.append(unit(diagnostic.TASKS[8], "any", False))
        self.assertEqual(diagnostic.summarize(rows)["predictions"]["D2"], "fails")

    def test_no_free_proof_leaves_d3_untested_and_missing_units_are_incomplete(self):
        rows = [unit(t, a, False) for t in diagnostic.TASKS for a in runner.ARMS]
        self.assertEqual(diagnostic.summarize(rows)["predictions"]["D3"], "untested")
        summary = diagnostic.summarize(outcome()[:-1])
        self.assertFalse(summary["complete"])
        self.assertEqual(set(summary["predictions"].values()), {"incomplete"})
        self.assertIn("missing", diagnostic.report(summary))

    def test_latest_row_wins_and_report_lists_proofs(self):
        rows = outcome()
        rows.append({"module": "development", "declaration": "two_facts", "arm": "first", "error": "x"})
        summary = diagnostic.summarize(rows)
        self.assertFalse(summary["complete"])
        text = diagnostic.report(diagnostic.summarize(outcome()))
        self.assertIn("| square_sixteen | coupled |", text)
        self.assertIn("pick_goal 3; rfl; simp", text)
        self.assertIn("| D1 |", text)

    def test_registration_payload(self):
        payload = diagnostic.registration_payload()
        self.assertEqual(payload["tasks"], diagnostic.TASKS)
        self.assertEqual(payload["predictions"], diagnostic.PREDICTIONS)
        self.assertIn("diagnostic", payload["implementationSha256"])
        self.assertIn("runner", payload["implementationSha256"])


if __name__ == "__main__":
    unittest.main()
