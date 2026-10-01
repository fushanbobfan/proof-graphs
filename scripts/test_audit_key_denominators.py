#!/usr/bin/env python3
"""Denominator audit tests on synthetic committed-log shapes (no Lean).

  python -B scripts/test_audit_key_denominators.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from audit_key_denominators import (  # noqa: E402
    expansions_of, false_drops, false_merges, matched_duplicates, source_hash_checks,
)


def state(expression: list[str] | None, coarse: list[str], default: list[str] | None = None,
          joint: str | None = None) -> dict:
    return {"faithful": expression, "coarse": coarse, "default": default if default is not None else coarse,
            "state": joint if joint is not None else (None if expression is None else "|".join(expression))}


class Denominators(unittest.TestCase):
    def test_source_hash_mismatch_is_reported(self) -> None:
        import gzip
        import hashlib
        data = {"logs.jsonl.gz": gzip.compress(b"logs"), "results.jsonl": b"results"}
        old = {"logsSha256": "stale", "resultsSha256": hashlib.sha256(b"results").hexdigest()}
        checks = source_hash_checks(data, old)
        self.assertFalse(checks["logs.jsonl.gz"]["matches"])
        self.assertEqual(checks["logs.jsonl.gz"]["expected"], "stale")
        self.assertEqual(checks["logs.jsonl.gz"]["actual"], hashlib.sha256(b"logs").hexdigest())
        self.assertTrue(checks["results.jsonl"]["matches"])

    def test_gzip_hash_is_of_the_content_like_the_repository(self) -> None:
        import gzip
        import hashlib
        content = b"line\r\nline\n"
        data = {"logs.jsonl.gz": gzip.compress(content, mtime=1), "results.jsonl": b"results"}
        old = {"logsSha256": hashlib.sha256(b"line\nline\n").hexdigest(), "resultsSha256": "x"}
        self.assertTrue(source_hash_checks(data, old)["logs.jsonl.gz"]["matches"])

    def test_matched_support_excludes_missing_from_both_histories(self) -> None:
        log = {"events": [["x", i] for i in range(4)], "expansions": [{} for _ in range(4)],
               "states": {"0": state(None, ["coarse"]), "1": state(["expr"], ["coarse"]),
                          "2": state(["expr"], ["other"]), "3": state(["new"], ["coarse"])}}
        self.assertEqual(matched_duplicates(log), {"total": 4, "evaluable": 3, "missing": 1,
                                                   "expressionDuplicates": 1, "coarseDuplicates": 1})

    def test_histories_restart_for_each_unit(self) -> None:
        log = {"events": [["x", 0]], "expansions": [{}], "states": {"0": state(["expr"], ["coarse"])}}
        self.assertEqual(matched_duplicates(log)["expressionDuplicates"], 0)
        self.assertEqual(matched_duplicates(log)["expressionDuplicates"], 0)

    def test_first_goal_only(self) -> None:
        log = {"events": [["x", 0], ["x", 1]], "expansions": [{}, {}],
               "states": {"0": state(["a", "b"], ["x", "y"]), "1": state(["b"], ["y"])}}
        self.assertEqual(matched_duplicates(log)["expressionDuplicates"], 0)
        self.assertEqual(matched_duplicates(log)["coarseDuplicates"], 0)

    def test_drop_denominators_missing_either_endpoint(self) -> None:
        log = {"events": [["x", 0]] + [["t", 0, i] for i in range(1, 7)],
               "expansions": [{"exactDuplicates": 3}],
               "states": {"0": state(["a"], ["same"]), "1": state(["b"], ["same"]),
                          "2": state(None, ["same"]), "3": state(None, ["other"]),
                          "4": state(["c"], ["other"]), "5": state(["d"], ["fresh"]),
                          "6": state([], [])}}
        self.assertEqual(false_drops(log, "default"), {"total": 3, "evaluable": 1, "missing": 2, "false": 1})

    def test_coarse_drops_use_joint_state_key(self) -> None:
        log = {"events": [["x", 0], ["t", 0, 1]], "expansions": [{"renamedDuplicates": 1}],
               "states": {"0": state(["a", "b"], ["x", "y"], ["p", "q"], "shared"),
                          "1": state(["a", "b"], ["x", "y"], ["r", "s"], "split")}}
        self.assertEqual(false_drops(log, "coarse"), {"total": 1, "evaluable": 1, "missing": 0, "false": 1})

    def test_merges_keep_missing_representatives_and_skip_entanglement(self) -> None:
        log = {"events": [["x", 0]] + [["t", 0, i] for i in range(1, 5)], "expansions": [{}],
               "states": {"0": state(["a", "tail"], ["root", "tail"]),
                          "1": state(["b", "tail"], ["root", "tail"]),
                          "2": state(None, ["fresh", "tail"]),
                          "3": state(["c", "tail"], ["fresh", "tail"]),
                          "4": state(["d", "changed"], ["root", "changed"])}}
        self.assertEqual(false_merges(log), {"total": 2, "evaluable": 1, "missing": 1, "false": 1})

    def test_pick_is_not_a_candidate(self) -> None:
        log = {"events": [["x", 0], ["t", 0, 1], ["t", 0, 2, "p"], ["x", 2], ["t", 2, 3]],
               "expansions": [{}, {}]}
        self.assertEqual(expansions_of(log), [(0, [1]), (2, [3])])

    def test_reconstruction_fails_instead_of_approximating(self) -> None:
        with self.assertRaises(ValueError):
            expansions_of({"events": [["x", 0]], "expansions": []})
        with self.assertRaises(ValueError):
            false_drops({"events": [["x", 0]], "expansions": [{"exactDuplicates": 1}],
                         "states": {"0": state(["a"], ["root"])}}, "default")
        with self.assertRaises(ValueError):
            matched_duplicates({"events": [["x", 0]], "expansions": [{}],
                                "states": {"0": state(["a", "b"], ["root"])}})

    def test_empty_logs(self) -> None:
        log = {"events": [], "expansions": [], "states": {}}
        self.assertEqual(false_drops(log, "default")["total"], 0)
        self.assertEqual(false_merges(log)["total"], 0)
        self.assertEqual(matched_duplicates(log)["total"], 0)


if __name__ == "__main__":
    unittest.main()
