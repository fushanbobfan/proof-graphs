#!/usr/bin/env python3
"""Goal-selection search, paired arithmetic, and runner gates without Lean."""

from __future__ import annotations

import json
import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import goal_identity_typed as gi
import run_search_goal_selection as runner
import search_goal_selection as search
import search_harness as harness


def goal(name: str, value: str) -> dict:
    return {"id": name, "hyps": [], "target": {"kind": "string", "value": value}}


class FakeRepl:
    def __init__(self, transitions: dict | None = None, exports: dict | None = None) -> None:
        self.transitions = transitions or {}
        self.exports = exports or {}
        self.restarts = 0
        self.calls = []
        self.export_calls = []

    def tactic(self, state: int, tactic: str):
        self.calls.append((state, tactic))
        return self.transitions.get((state, tactic))

    def export(self, repl, state: int):
        self.export_calls.append(state)
        return self.exports.get(state)


class SearchTests(unittest.TestCase):
    def run_search(self, repl, goals=None, candidates=None, budget=4, identify="text", verifier=None, **kwargs):
        return search.any_goal_search(repl, 0, goals or ["A"], lambda _: candidates or ["a"], budget,
                                      verifier, identify, repl.export, **kwargs)

    def test_pick_is_a_separate_harness_step_and_proof_line(self):
        repl = FakeRepl({(0, "pick_goal 2 -- harness\n"): (["B", "A"], 10),
                         (10, "a"): (["A"], 1), (1, "a"): ([], 2)})
        scripts = []
        result = self.run_search(repl, ["A", "B"], verifier=lambda s: scripts.append(s) or True)
        self.assertEqual(result["proof"], ["pick_goal 2", "a", "a"])
        self.assertEqual(scripts, [["pick_goal 2", "a", "a"]])
        self.assertEqual(repl.calls, [(0, "a"), (0, "pick_goal 2 -- harness\n"), (10, "a"), (1, "a")])
        self.assertEqual(result["steps"], 3)
        self.assertEqual(result["stepsAtProof"], 3)
        self.assertEqual(result["expansions"][0]["positions"], {"1": 0, "2": 1})

    def test_candidates_start_from_the_same_selected_parent(self):
        repl = FakeRepl({(0, "pick_goal 2 -- harness\n"): (["B", "A"], 10)})
        result = self.run_search(repl, ["A", "B"], ["a", "b"], budget=1)
        self.assertEqual(repl.calls, [(0, "a"), (0, "b"), (0, "pick_goal 2 -- harness\n"),
                                      (10, "a"), (10, "b")])
        self.assertEqual(result["steps"], 4)
        self.assertIsNone(result["stepsAtProof"])

    def test_early_proof_counts_only_tried_candidates(self):
        repl = FakeRepl({(0, "b"): ([], 1)})
        result = self.run_search(repl, candidates=["a", "b", "c"])
        self.assertEqual(result["stepsAtProof"], 2)
        self.assertEqual(result["expansions"][0]["candidates"], 3)
        self.assertEqual(result["expansions"][0]["steps"], 2)

    def test_rejected_closure_is_not_a_valid_child(self):
        repl = FakeRepl({(0, "a"): ([], 1), (0, "b"): (["B"], 2)})
        result = self.run_search(repl, candidates=["a", "b"], budget=1, verifier=lambda _: False)
        self.assertIsNone(result["proof"])
        self.assertEqual(result["rejected"], 1)
        self.assertEqual(result["steps"], 2)
        self.assertEqual(result["expansions"][0]["valid"], 1)

    def test_budget_and_breadth_first(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (0, "b"): (["C"], 2), (1, "a"): (["D"], 3)})
        result = self.run_search(repl, candidates=["a", "b"], budget=3)
        self.assertEqual([e["state"] for e in result["expansions"]], [0, 1, 2])
        self.assertEqual([e["depth"] for e in result["expansions"]], [0, 1, 1])
        self.assertEqual(result["steps"], 6)
        self.assertEqual(len(repl.export_calls), 3)

    def test_zero_budget_exports_typed_root_without_steps(self):
        repl = FakeRepl()
        result = self.run_search(repl, budget=0, identify="multiset")
        self.assertEqual(result["expansions"], [])
        self.assertEqual(result["steps"], 0)
        self.assertEqual(repl.export_calls, [0])

    def test_text_mode_drops_text_duplicates(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (0, "b"): (["B"], 2)})
        result = self.run_search(repl, candidates=["a", "b"], budget=1)
        self.assertEqual(result["states"], 2)
        self.assertEqual(result["expansions"][0]["exactDuplicates"], 1)
        self.assertEqual(result["expansions"][0]["multisetDuplicates"], 1)
        self.assertEqual(repl.export_calls, [0])

    def test_multiset_mode_merges_jointly_renamed_reordered_children(self):
        repl = FakeRepl({(0, "a"): (["A", "B"], 1), (0, "b"): (["B", "A"], 2)},
                        {0: [goal("r", "root")], 1: [goal("a", "A"), goal("b", "B")],
                         2: [goal("x", "B"), goal("y", "A")]})
        result = self.run_search(repl, candidates=["a", "b"], budget=1, identify="multiset")
        self.assertEqual(result["states"], 2)
        self.assertEqual(result["expansions"][0]["typedDuplicates"], 1)
        self.assertEqual(result["expansions"][0]["exactDuplicates"], 0)
        self.assertEqual(repl.export_calls, [0, 1, 2])

    def test_multiset_does_not_merge_failed_exports_even_if_text_matches(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (0, "b"): (["B"], 2)})
        result = self.run_search(repl, candidates=["a", "b"], budget=1, identify="multiset")
        self.assertEqual(result["states"], 3)
        self.assertEqual(result["exportFailures"], 3)
        self.assertIsNone(result["expansions"][0]["coupled"])
        self.assertIsNone(result["expansions"][0]["orderDuplicateTyped"])

    def test_none_keys_never_merge(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (0, "b"): (["B"], 2)},
                        {i: [goal(str(i), "B")] for i in range(3)})
        with patch.object(gi, "unordered_state_key", return_value=None):
            result = self.run_search(repl, candidates=["a", "b"], budget=1, identify="multiset")
        self.assertEqual(result["states"], 3)
        self.assertEqual(result["exportFailures"], 0)
        self.assertIsNone(result["expansions"][0]["orderDuplicateTyped"])
        self.assertFalse(result["expansions"][0]["coupled"])

    def test_joint_identity_preserves_sharing(self):
        shared = [goal("a", "A"), goal("b", "B")]
        separate = [goal("x", "A"), goal("y", "B")]
        for g in shared:
            g["target"] = {"kind": "mvar", "id": "w"}
        for i, g in enumerate(separate):
            g["target"] = {"kind": "mvar", "id": f"w{i}"}
        repl = FakeRepl({(0, "a"): (["same", "same"], 1), (0, "b"): (["same", "same"], 2)},
                        {0: [goal("r", "root")], 1: shared, 2: separate})
        result = self.run_search(repl, candidates=["a", "b"], budget=1, identify="multiset")
        self.assertEqual(result["states"], 3)
        self.assertEqual(result["expansions"][0]["typedDuplicates"], 0)
        self.assertEqual(result["expansions"][0]["exactDuplicates"], 1)

    def test_export_cache_and_child_failures(self):
        repl = FakeRepl({(0, "a"): (["B"], 1)})
        result = self.run_search(repl, budget=2, identify="multiset")
        self.assertEqual(repl.export_calls, [0, 1])
        self.assertEqual([e["exportFailures"] for e in result["expansions"]], [2, 0])

    def test_wrong_export_goal_count_is_a_failure(self):
        repl = FakeRepl(exports={0: []})
        result = self.run_search(repl, budget=1)
        self.assertEqual(result["exportFailures"], 1)
        self.assertIsNone(result["expansions"][0]["coupled"])

    def test_multiset_exports_closing_child(self):
        repl = FakeRepl({(0, "a"): ([], 1)}, {0: [goal("r", "R")], 1: []})
        result = self.run_search(repl, identify="multiset")
        self.assertEqual(repl.export_calls, [0, 1])
        self.assertEqual(result["stepsAtProof"], 1)

    def test_multiset_drops_a_typed_return_to_root(self):
        repl = FakeRepl({(0, "a"): (["renamed text"], 1)},
                        {0: [goal("r", "R")], 1: [goal("other", "R")]})
        result = self.run_search(repl, identify="multiset")
        self.assertEqual(result["states"], 1)
        self.assertEqual(result["expansions"][0]["typedDuplicates"], 1)

    def test_first_text_is_the_unchanged_search_without_exports(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (1, "b"): ([], 2)})
        with patch.object(harness, "MENU", ["a", "b", "c"]):
            fresh = runner.search(repl, "firstText", 0, ["A"], None, 3)
            old = harness.whole_state_search(FakeRepl(repl.transitions), 0, ["A"],
                                             harness.menu_proposer, 3)
            self.assertEqual(fresh, old)
            self.assertEqual(runner.result_steps(fresh), 5)
        self.assertEqual(repl.export_calls, [])
        self.assertNotIn("steps", fresh)

    def test_typed_order_duplicate_and_coupling_measure(self):
        measures = search.Measures()
        a = goal("a", "A")
        b = {"id": "b", "hyps": [], "target": {"kind": "mvar", "id": "a"}}
        first = measures.expanded(harness.State(0, 0, ["A", "B"], None, None, 0), [a, b])
        second = measures.expanded(harness.State(1, 1, ["B", "A"], None, None, 0), [b, a])
        third = measures.expanded(harness.State(2, 2, ["B", "A"], None, None, 0), [b, a])
        self.assertTrue(first["coupled"])
        self.assertTrue(second["orderDuplicateTyped"])
        self.assertTrue(second["orderDuplicate"])
        self.assertFalse(third["orderDuplicateTyped"])

    def test_probe_reports_original_position_and_coupled_group(self):
        exported = [goal("a", "A"), {"id": "b", "hyps": [], "target": {"kind": "mvar", "id": "a"}}]
        repl = FakeRepl({(0, "pick_goal 2 -- harness\n"): (["B", "A"], 10), (10, "a"): ([], 1)},
                        {0: exported, 1: []})
        with patch.object(search, "export", side_effect=repl.export):
            probe = search.coupling_probe(repl, 0, ["pick_goal 2", "a"])
        self.assertTrue(probe["closed"])
        self.assertEqual(probe["steps"][0]["groups"], [[1, 2]])
        self.assertTrue(probe["steps"][0]["chosenCoupled"])
        self.assertEqual(probe["steps"][0]["position"], 2)

    def test_definition_failure_uses_plain_export(self):
        class Session(FakeRepl):
            import_timeout = timeout = 1

            def _exchange(self, request, timeout):
                return {"messages": [{"severity": "error", "data": "failed"}]}

        repl = Session()
        self.assertEqual(search.define_exporter(repl, 7), 7)
        with patch.object(gi, "export", return_value=[]) as exporter:
            self.assertEqual(search.export(repl, 0), [])
        exporter.assert_called_once_with(repl, 0, tactic=None)

    def test_named_export_and_restart_abandons_stale_state(self):
        repl = FakeRepl()
        repl.typed_fast_export = True
        with patch.object(gi, "export", return_value=[]) as exporter:
            self.assertEqual(search.export(repl, 0), [])
        exporter.assert_called_once_with(repl, 0, tactic=search.EXPORT_TACTIC)

        def restarted(*args, **kwargs):
            repl.restarts += 1
            return None

        with patch.object(gi, "export", side_effect=restarted):
            with self.assertRaises(search.ReplTimeout):
                search.export(repl, 0)

    def test_unknown_identify_and_negative_budget(self):
        with self.assertRaises(ValueError):
            self.run_search(FakeRepl(), identify="textMultiset")
        with self.assertRaises(ValueError):
            self.run_search(FakeRepl(), budget=-1)

    def test_first_position_has_no_picks_and_26_steps_per_expansion(self):
        repl = FakeRepl({(0, harness.MENU[0]): (["B", "C"], 1)},
                        {0: [goal("r", "R")], 1: [goal("b", "B"), goal("c", "C")]})
        result = self.run_search(repl, candidates=harness.MENU, budget=2, identify="ordered", positions="first")
        self.assertEqual([e["steps"] for e in result["expansions"]], [26, 26])
        self.assertEqual(result["steps"], 52)
        self.assertTrue(all(not tactic.startswith("pick_goal") for _, tactic in repl.calls))
        self.assertEqual(result["expansions"][1]["positions"], {"1": 0})

    def test_ordered_identity_keeps_different_typed_children_with_identical_text(self):
        repl = FakeRepl({(0, "a"): (["B"], 1), (0, "b"): (["B"], 2)},
                        {0: [goal("r", "R")], 1: [goal("b", "B")], 2: [goal("c", "C")]})
        result = self.run_search(repl, candidates=["a", "b"], budget=1, identify="ordered")
        self.assertEqual(result["states"], 3)
        self.assertEqual(result["expansions"][0]["exactDuplicates"], 1)
        self.assertEqual(result["expansions"][0]["typedDuplicates"], 0)
        self.assertEqual(repl.export_calls, [0, 1, 2])

    def test_ordered_identity_merges_joint_renaming_but_preserves_order(self):
        repl = FakeRepl({(0, "a"): (["A", "B"], 1), (0, "b"): (["renamed A", "renamed B"], 2),
                         (0, "c"): (["B", "A"], 3)},
                        {0: [goal("r", "R")], 1: [goal("a", "A"), goal("b", "B")],
                         2: [goal("x", "A"), goal("y", "B")], 3: [goal("z", "B"), goal("w", "A")]})
        result = self.run_search(repl, candidates=["a", "b", "c"], budget=1, identify="ordered")
        self.assertEqual(result["states"], 3)
        self.assertEqual(result["expansions"][0]["typedDuplicates"], 1)

    def test_ordered_failed_exports_and_none_keys_never_merge(self):
        transitions = {(0, "a"): (["B"], 1), (0, "b"): (["B"], 2)}
        repl = FakeRepl(transitions)
        failed = self.run_search(repl, candidates=["a", "b"], budget=1, identify="ordered")
        self.assertEqual(failed["states"], 3)
        self.assertEqual(failed["exportFailures"], 3)
        repl = FakeRepl(transitions, {i: [goal(str(i), "B")] for i in range(3)})
        with patch.object(gi, "ordered_state_key", return_value=None):
            unknown = self.run_search(repl, candidates=["a", "b"], budget=1, identify="ordered")
        self.assertEqual(unknown["states"], 3)
        self.assertEqual(unknown["exportFailures"], 0)

    def test_both_typed_modes_export_verified_closure_and_drop_root_returns(self):
        for identify in ("ordered", "multiset"):
            repl = FakeRepl({(0, "a"): (["renamed"], 1), (0, "b"): ([], 2)},
                            {0: [goal("r", "R")], 1: [goal("s", "R")], 2: []})
            result = self.run_search(repl, candidates=["a", "b"], identify=identify)
            self.assertEqual(repl.export_calls, [0, 1, 2])
            self.assertEqual(result["states"], 2)
            self.assertEqual(result["stepsAtProof"], 2)

    def test_time_stop_before_first_expansion_exports_root(self):
        repl = FakeRepl(exports={0: [goal("r", "R")]})
        ticks = iter([0, 10, 10])
        result = self.run_search(repl, identify="ordered", clock=lambda: next(ticks), time_limit=10)
        self.assertEqual(result["stopped"], "wall-clock")
        self.assertEqual(result["expansions"], [])
        self.assertEqual(result["steps"], 0)
        self.assertEqual(repl.export_calls, [0])

    def test_time_stop_between_positions_records_partial_expansion(self):
        repl = FakeRepl(exports={0: [goal("a", "A"), goal("b", "B")]})
        ticks = iter([0, 0, 0, 10, 10])
        result = self.run_search(repl, goals=["A", "B"], candidates=harness.MENU, identify="ordered",
                                 clock=lambda: next(ticks), time_limit=10)
        self.assertEqual(result["stopped"], "wall-clock")
        self.assertIsNone(result["proof"])
        self.assertIsNone(result["stepsAtProof"])
        self.assertEqual(result["steps"], 26)
        self.assertEqual(result["expansions"][0]["positions"], {"1": 0})
        self.assertTrue(result["expansions"][0]["interrupted"])
        self.assertTrue(all(not t.startswith("pick_goal") for _, t in repl.calls))

    def test_time_stop_before_first_position_records_no_tried_positions(self):
        repl = FakeRepl()
        ticks = iter([0, 0, 10, 10])
        result = self.run_search(repl, clock=lambda: next(ticks), time_limit=10)
        self.assertEqual(result["steps"], 0)
        self.assertEqual(result["expansions"][0]["positions"], {})
        self.assertTrue(result["expansions"][0]["interrupted"])
        self.assertEqual(repl.calls, [])

    def test_time_stop_before_later_expansion_preserves_full_records(self):
        repl = FakeRepl({(0, "a"): (["B"], 1)})
        ticks = iter([0, 0, 0, 10, 10])
        result = self.run_search(repl, clock=lambda: next(ticks), time_limit=10)
        self.assertEqual(result["stopped"], "wall-clock")
        self.assertEqual(len(result["expansions"]), 1)
        self.assertNotIn("interrupted", result["expansions"][0])

    def test_verification_timeout_abandons_stale_states(self):
        repl = FakeRepl({(0, "a"): ([], 1)})
        def verifier(script):
            repl.restarts += 1
            return False
        with self.assertRaises(search.ReplTimeout):
            self.run_search(repl, verifier=verifier)

    def test_invalid_positions_and_time_limit(self):
        with self.assertRaises(ValueError):
            self.run_search(FakeRepl(), positions="last")
        with self.assertRaises(ValueError):
            self.run_search(FakeRepl(), time_limit=-1)


def row(name, arm, proof=None, steps=20, expansions=None):
    return {"module": "M", "declaration": name, "arm": arm, "constructed": True,
            "result": {"proof": proof, "stepsAtProof": steps if proof else None, "steps": steps,
                       "distinctTypedMultisets": 1, "exportFailures": 0,
                       "expansions": expansions or []}}


class SummaryTests(unittest.TestCase):
    def test_module_units_use_only_the_required_session_and_report_setup_time(self):
        task = {"module": "M", "declaration": "a", "line": 1}
        made = SimpleNamespace(proof_state=0, goal="A")
        result = {"seconds": 2, "proof": None, "expansions": []}
        for arm in runner.ARMS:
            with patch.object(search, "ClosingRepl") as repl, patch.object(harness, "ModuleSession") as plain, \
                    patch.object(search, "ExportingSession") as typed, patch.object(runner, "find_lake", return_value="lake"), \
                    patch.object(runner, "search", return_value=result), \
                    patch.object(runner.time, "monotonic", side_effect=[0, 3]):
                repl.return_value.restarts = 0
                for session in (plain, typed):
                    session.return_value.tasks_in_order.return_value = [("a", made)]
                unit = runner.run_unit(task, arm)
                self.assertEqual(unit["setupSeconds"], 3)
                self.assertEqual(unit["result"], result)
                self.assertEqual(plain.call_count, int(arm == "firstText"))
                self.assertEqual(typed.call_count, int(arm != "firstText"))
                repl.return_value.close.assert_called_once()

    def test_first_text_summary_derives_steps_without_inventing_export_support(self):
        expansion = {"state": 0, "depth": 0, "goals": 1, "candidates": 26, "valid": 1,
                     "exactDuplicates": 0, "orderDuplicate": False, "goalDuplicate": False}
        baseline = {"module": "M", "declaration": "a", "arm": "firstText", "constructed": True,
                    "result": {"expansions": [expansion], "proof": ["omega"]}}
        summary = runner.summarize([baseline], [{"module": "M", "declaration": "a"}], ["firstText"])
        arm = summary["arms"]["firstText"]
        self.assertEqual(arm["steps"], 3)
        self.assertEqual(arm["exportFailures"], 0)
        self.assertEqual(arm["typedOrderSupport"], 0)
        self.assertIsNone(arm["distinctTypedMultisets"])
        self.assertIsNone(arm["multisetFraction"])
        self.assertNotIn("steps", baseline["result"])

    def test_baseline_sample_is_deterministic_and_contains_every_proved_task(self):
        tasks = runner.read_json(runner.SOURCE / "tasks.json")
        sample = runner.baseline_sample(tasks)
        keys = {runner.task_key(t) for t in sample}
        proved = {runner.task_key(r) for r in runner.read_rows(runner.SOURCE / "results.jsonl")
                  if r["arm"] == "menu" and r["search"] == "whole" and r.get("result", {}).get("proof")}
        self.assertEqual(len(sample), 200)
        self.assertTrue(proved <= keys)
        self.assertEqual(sample, runner.baseline_sample(list(reversed(tasks))))
        self.assertEqual(sample, sorted(sample, key=runner.task_key))
        self.assertNotEqual(sample, runner.baseline_sample(tasks, runner.SAMPLE_SEED + 1))

    def test_wall_clock_stops_remain_paired_and_abandonments_are_excluded(self):
        tasks = [{"module": "M", "declaration": n} for n in ("a", "b")]
        stopped = row("a", "first")
        stopped["result"]["stopped"] = "wall-clock"
        abandoned = {"module": "M", "declaration": "b", "arm": "first",
                     "constructed": True, "abandoned": "repl timeout", "abandonments": 2}
        summary = runner.summarize([stopped, row("a", "any", ["x"]), abandoned, row("b", "any", ["x"])],
                                   tasks, ["first", "any"])
        self.assertEqual(summary["pairs"]["first:any"]["pairedCompleted"], 1)
        self.assertEqual(summary["pairs"]["first:any"]["equalExpansions"]["bOnly"], 1)
        self.assertEqual(summary["arms"]["first"]["wallClockStops"], 1)
        self.assertEqual(summary["arms"]["first"]["finalAbandoned"], 1)

    def test_equal_steps_caps_every_arm_and_only_registered_pairs_exist(self):
        tasks = [{"module": "M", "declaration": "a"}]
        rows = [row("a", arm, ["x"], 625 if arm in ("firstText", "first") else 624) for arm in runner.ARMS]
        summary = runner.summarize(rows, tasks, list(runner.ARMS))
        self.assertEqual(set(summary["pairs"]), {f"{a}:{b}" for a, b in runner.PAIRS})
        self.assertEqual(summary["pairs"]["first:any"]["equalSteps"]["bOnly"], 1)
        self.assertEqual(summary["pairs"]["firstText:first"]["equalSteps"]["aOnly"], 0)
        self.assertEqual(summary["freeChoiceOnlyProofs"], [])

    def test_second_abandonment_is_final_across_compaction_and_later_runs(self):
        task = {"module": "M", "declaration": "a"}
        timeout = task | {"arm": "first", "abandoned": "repl timeout", "constructed": True}
        with tempfile.TemporaryDirectory() as directory:
            sink = Path(directory) / "results.jsonl"
            sink.write_text(json.dumps(timeout) + "\n", encoding="utf-8")
            with patch.object(runner, "RESULTS", sink), patch.object(runner, "run_unit", return_value=timeout) as unit, \
                    contextlib.redirect_stdout(io.StringIO()):
                rows = runner.run_all([task], ["first"], 1)
                self.assertEqual(unit.call_count, 1)
                self.assertEqual(rows[0]["abandonments"], 2)
                sink.write_text(json.dumps(rows[0]) + "\n", encoding="utf-8")
                resumed = runner.run_all([task], ["first"], 1)
                self.assertEqual(unit.call_count, 1)
                self.assertEqual(resumed[0]["abandonments"], 2)

    def test_abandonment_count_survives_an_error_then_success(self):
        task = {"module": "M", "declaration": "a", "arm": "first"}
        rows = [task | {"abandoned": "repl timeout"}, task | {"error": "failure"}]
        compact = runner.latest_rows(rows)
        self.assertEqual(compact[0]["abandonments"], 1)
        final = runner.latest_rows(compact + [task | {"abandoned": "repl timeout"}])
        self.assertEqual(final[0]["abandonments"], 2)

    def test_run_all_limits_first_text_to_sample_and_typed_arms_to_all_tasks(self):
        tasks = [{"module": "M", "declaration": n} for n in ("a", "b")]
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(runner, "RESULTS", Path(directory) / "rows.jsonl"), \
                    patch.object(runner, "run_unit", side_effect=lambda t, a: row(t["declaration"], a)) as unit, \
                    contextlib.redirect_stdout(io.StringIO()):
                runner.run_all(tasks, list(runner.ARMS), 1, sample=tasks[:1])
        self.assertEqual(unit.call_count, 7)
        self.assertNotIn(("b", "firstText"), [(c.args[0]["declaration"], c.args[1]) for c in unit.call_args_list])

    def test_holdout_selection_and_all_four_arms_use_module_units(self):
        tasks = runner.holdout_tasks()
        self.assertEqual(len(tasks), 44)
        self.assertEqual(tasks, sorted(tasks, key=runner.task_key))
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(runner, "run_unit", side_effect=lambda t, a: row(t["declaration"], a)) as unit, \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.develop_holdout(Path(directory), 2), 0)
                self.assertEqual(unit.call_count, 8)
                self.assertEqual([c.args for c in unit.call_args_list], [(t, a) for t in tasks[:2] for a in runner.ARMS])

    def test_typed_arm_dispatch(self):
        for arm, positions, identify in (("first", "first", "ordered"), ("any", "all", "ordered"),
                                         ("anyMultiset", "all", "multiset")):
            with patch.object(search, "any_goal_search", return_value={}) as engine:
                runner.search(None, arm, 0, ["A"], None)
            self.assertEqual(engine.call_args.kwargs, {"positions": positions, "identify": identify,
                                                       "time_limit": 7200})

    def test_discordances_steps_and_missing_are_separate(self):
        tasks = [{"module": "M", "declaration": n} for n in ("a", "b", "c", "d")]
        rows = [row("a", "first"), row("a", "any", ["x"], 625),
                row("b", "first", ["x"]), row("b", "any"),
                row("c", "first"), row("c", "any", ["x"], 624), row("d", "any", ["x"])]
        summary = runner.summarize(rows, tasks, ["first", "any"])
        pair = summary["pairs"]["first:any"]
        self.assertEqual(pair["pairedCompleted"], 3)
        self.assertEqual(pair["equalExpansions"]["aOnly"], 1)
        self.assertEqual(pair["equalExpansions"]["bOnly"], 2)
        self.assertEqual(pair["equalExpansions"]["pBGreater"], .5)
        self.assertEqual(pair["equalSteps"]["aOnly"], 1)
        self.assertEqual(pair["equalSteps"]["bOnly"], 1)
        self.assertEqual(pair["equalSteps"]["pBGreater"], .75)
        self.assertEqual(len(summary["freeChoiceOnlyProofs"]), 2)
        self.assertEqual(summary["arms"]["first"]["missing"], 1)

    def test_fractions_use_explicit_support(self):
        expansions = [{"goals": 2, "valid": 4, "exactDuplicates": 1, "multisetDuplicates": 2,
                       "orderDuplicate": True, "orderDuplicateTyped": True, "coupled": True},
                      {"goals": 2, "valid": 2, "exactDuplicates": 0, "multisetDuplicates": 1,
                       "orderDuplicate": False, "orderDuplicateTyped": None, "coupled": None}]
        summary = runner.summarize([row("a", "any", expansions=expansions)],
                                   [{"module": "M", "declaration": "a"}], ["any"])
        arm = summary["arms"]["any"]
        self.assertEqual(arm["orderFraction"], .5)
        self.assertEqual(arm["typedOrderFraction"], 1)
        self.assertEqual(arm["exactFraction"], 1 / 6)
        self.assertEqual(arm["multisetFraction"], .5)
        self.assertEqual(arm["coupledFraction"], 1)

    def test_exact_sign_tail(self):
        self.assertIsNone(runner.sign_test(0, 0))
        self.assertEqual(runner.sign_test(3, 0), .125)
        self.assertEqual(runner.sign_test(0, 3), 1)
        self.assertEqual(runner.sign_test(2, 1), .5)

    def test_latest_retry_replaces_old_success(self):
        tasks = [{"module": "M", "declaration": "a"}]
        summary = runner.summarize([row("a", "first", ["x"]), row("a", "first")], tasks, ["first"])
        self.assertEqual(summary["arms"]["first"]["proved"], 0)

    def test_resume_skips_completed_and_retries_errors_and_timeouts(self):
        tasks = [{"module": "M", "declaration": n} for n in ("a", "b", "c")]
        old = [row("a", "first"), {"module": "M", "declaration": "b", "arm": "first", "error": "failure"},
               {"module": "M", "declaration": "c", "arm": "first", "abandoned": "repl timeout"}]
        with tempfile.TemporaryDirectory() as directory:
            sink = Path(directory) / "results.jsonl"
            sink.write_bytes("".join(json.dumps(r) + "\n" for r in old).encode("utf-8"))
            with patch.object(runner, "RESULTS", sink), \
                    patch.object(runner, "run_unit", side_effect=lambda t, a: row(t["declaration"], a)) as unit, \
                    contextlib.redirect_stdout(io.StringIO()):
                resumed = runner.run_all(tasks, ["first"], 1)
                self.assertEqual([call.args[0]["declaration"] for call in unit.call_args_list], ["b", "c"])
                self.assertEqual(len(resumed), 3)
                self.assertEqual(len(runner.read_rows(sink)), 5)
                self.assertNotIn(b"\r", sink.read_bytes())

    def test_unposed_baseline_is_replicated_and_timeout_is_not(self):
        baseline = {"module": "M", "declaration": "a", "arm": "menu", "search": "whole", "constructed": False}
        fresh = {"module": "M", "declaration": "a", "arm": "firstText", "constructed": False}
        with patch.object(runner, "read_rows", return_value=[baseline]):
            self.assertEqual(runner.replication([fresh])["matched"], 1)
            self.assertEqual(runner.replication([fresh | {"abandoned": "timeout"}])["matched"], 0)

    def test_replication_requires_the_registered_sample_membership(self):
        baseline = {"module": "M", "declaration": "a", "arm": "menu", "search": "whole", "constructed": False}
        fresh = baseline | {"arm": "firstText"}
        with patch.object(runner, "read_rows", return_value=[baseline]):
            self.assertTrue(runner.replication([fresh], [baseline])["sampleMatches"])
            wrong = runner.replication([fresh], [baseline | {"declaration": "b"}])
            self.assertEqual(wrong["matched"], 1)
            self.assertFalse(wrong["sampleMatches"])

    def test_registration_placeholders_and_source_population(self):
        tasks = runner.read_json(runner.SOURCE / "tasks.json")
        payload = runner.registration_payload(tasks)
        self.assertEqual(len(tasks), 1347)
        self.assertEqual(payload["proposer"], harness.MENU)
        self.assertEqual(payload["budget"], {"expansions": 24, "secondarySteps": 624, "typedSearchSeconds": 7200})
        self.assertTrue(all(v == "TO BE WRITTEN" for v in payload["hypotheses"].values()))

    def test_development_theorems_exclude_the_entire_slice(self):
        names = runner.development_names(10)
        slice_names = {r["declaration"] for r in runner.read_rows(
            runner.ROOT / "experiments" / "linearizations-mathlib-v0.1" / "results.jsonl")}
        self.assertTrue(names)
        self.assertLessEqual(len(names), 10)
        self.assertFalse(slice_names.intersection(names))

    def test_replication_requires_full_expansion_records_and_found_status(self):
        result = {"proof": ["a"], "expansions": [{k: 0 for k in runner.deep.WHOLE_KEYS}]}
        baseline = {"module": "M", "declaration": "a", "arm": "menu", "search": "whole",
                    "constructed": True, "result": result}
        fresh = {"module": "M", "declaration": "a", "arm": "firstText", "constructed": True,
                 "result": {"proof": ["different valid proof"], "expansions": result["expansions"]}}
        with patch.object(runner, "read_rows", return_value=[baseline]):
            self.assertEqual(runner.replication([fresh])["matched"], 1)
            fresh["result"]["expansions"] = []
            self.assertEqual(runner.replication([fresh])["matched"], 0)

    def test_output_directory_must_be_external(self):
        with self.assertRaises(SystemExit):
            runner.outside_output(runner.ROOT / "smoke")
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(runner.outside_output(Path(directory)), Path(directory).resolve())

    def test_report_contains_proof_and_secondary_comparison(self):
        tasks = [{"module": "M", "declaration": "a"}]
        summary = runner.summarize([row("a", "first"), row("a", "any", ["pick_goal 2", "a"])],
                                   tasks, ["first", "any"])
        text = runner.report(summary)
        self.assertIn("pick_goal 2\na", text)
        self.assertIn("equalSteps", text)


if __name__ == "__main__":
    unittest.main()
