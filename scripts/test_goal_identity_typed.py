#!/usr/bin/env python3
"""Typed goal identity tests on synthetic exports (no Lean).

  python -B scripts/test_goal_identity_typed.py
"""

from __future__ import annotations

import copy
import itertools
import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import goal_identity_typed as gi  # noqa: E402
from lean_repl import ReplTimeout  # noqa: E402


def const(name: str, levels: list[dict] | None = None) -> dict:
    return {"kind": "const", "name": name, "levels": levels or []}


def mvar(name: str) -> dict:
    return {"kind": "mvar", "id": name}


def lmvar(name: str) -> dict:
    return {"kind": "lmvar", "id": name}


def app(function: dict, argument: dict) -> dict:
    return {"kind": "app", "function": function, "argument": argument}


def goal(name: str, target: dict, hyps: list[dict] | None = None) -> dict:
    return {"id": name, "hyps": hyps or [], "target": target}


def hyp(type_: dict, value: dict | None = None, implementation_detail: bool = False,
        binder_info: str = "explicit") -> dict:
    return {"type": type_, "value": value, "implementation_detail": implementation_detail,
            "binder_info": binder_info}


class TypedIdentity(unittest.TestCase):
    def test_literals_are_opaque(self) -> None:
        for text in ('?[foo]', '?1', '?u.1', 'λ "quoted" \\ \n?[escaped.变量]'):
            literal = {"kind": "string", "value": text}
            g = goal("root", app(const("Eq"), literal))
            self.assertEqual(gi._renumber([g])[0]["target"]["argument"], literal)
        def equation(left: str, right: str) -> dict:
            return app(app(const("Eq"), {"kind": "string", "value": left}),
                       {"kind": "string", "value": right})
        self.assertNotEqual(gi.goal_key(goal("a", equation("?[foo]", "?1"))),
                            gi.goal_key(goal("b", equation("?1", "?1"))))
        self.assertNotEqual(gi.goal_key(goal("a", equation("?u.1", "?u.1"))),
                            gi.goal_key(goal("b", equation("?u.2", "?u.2"))))

    def test_names_are_opaque(self) -> None:
        a = goal("a", const("?[foo].«?u.1.λ»"))
        b = goal("b", const("?[bar].«?u.2.λ»"))
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))
        self.assertEqual(gi._renumber([a])[0]["target"], a["target"])
        self.assertEqual(gi.groups([a, b]), [[0], [1]])

    def test_joint_sharing_not_individual_multiset(self) -> None:
        shared = [goal("a", app(const("P"), mvar("x"))), goal("b", app(const("Q"), mvar("x")))]
        split = [goal("c", app(const("Q"), mvar("y"))), goal("d", app(const("P"), mvar("z")))]
        renamed = [goal("c", app(const("Q"), mvar("y"))), goal("d", app(const("P"), mvar("y")))]
        self.assertEqual(sorted(map(gi.goal_key, shared)), sorted(map(gi.goal_key, split)))
        self.assertNotEqual(gi.unordered_state_key(shared), gi.unordered_state_key(split))
        self.assertEqual(gi.unordered_state_key(shared), gi.unordered_state_key(renamed))
        self.assertNotEqual(gi.ordered_state_key(shared), gi.ordered_state_key(renamed))
        self.assertEqual(gi.group_key(shared), gi.ordered_state_key(shared))

    def test_goal_owners_are_numbered_first(self) -> None:
        goals = [goal("a", app(mvar("third"), mvar("b"))), goal("b", mvar("a"))]
        normalized = gi._renumber(goals)
        self.assertEqual(normalized[0]["target"]["function"]["id"], 2)
        self.assertEqual(normalized[0]["target"]["argument"]["id"], 1)
        self.assertEqual(normalized[1]["target"]["id"], 0)
        renamed = [goal("α", app(mvar("χ"), mvar("β"))), goal("β", mvar("α"))]
        self.assertEqual(gi.ordered_state_key(goals), gi.ordered_state_key(renamed))
        unrelated = [goal("a", app(mvar("third"), mvar("other"))), goal("b", mvar("a"))]
        self.assertNotEqual(gi.unordered_state_key(goals), gi.unordered_state_key(unrelated))

    def test_repeated_goal_ids_preserve_aliases(self) -> None:
        repeated = [goal("a", const("True")), goal("a", const("True"))]
        distinct = [goal("a", const("True")), goal("b", const("True"))]
        self.assertNotEqual(gi.ordered_state_key(repeated), gi.ordered_state_key(distinct))
        self.assertEqual(gi.groups(repeated), [[0, 1]])

    def test_local_and_bound_names_are_absent(self) -> None:
        # Both exports use positions/indices, whether source names are x/h or «λ.变量»/«h?1».
        target = {"kind": "pi", "binder_info": "explicit", "type": const("Nat"),
                  "body": app(app(const("Eq"), {"kind": "bvar", "index": 0}),
                              {"kind": "fvar", "position": 0})}
        a = goal("first", target, [hyp(const("Nat"))])
        b = goal("renamed", copy.deepcopy(target), [hyp(const("Nat"))])
        self.assertEqual(gi.goal_key(a), gi.goal_key(b))
        for binder in gi.BINDERS - {"explicit"}:
            b["target"]["binder_info"] = binder
            self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))
        b = copy.deepcopy(a)
        b["hyps"][0]["binder_info"] = "implicit"
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))

    def test_implementation_detail_locals_are_kept(self) -> None:
        a = goal("a", const("True"), [hyp(const("Nat"), implementation_detail=True)])
        b = goal("b", const("True"), [hyp(const("Int"), implementation_detail=True)])
        c = goal("c", const("True"), [hyp(const("Nat"))])
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(c))
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(goal("d", const("True"))))

    def test_external_free_variables_retain_distinct_ids(self) -> None:
        a = goal("a", {"kind": "external_fvar", "id": "?[x].变量"})
        b = goal("b", {"kind": "external_fvar", "id": "?[y].变量"})
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))
        self.assertEqual(gi._renumber([a])[0]["target"], a["target"])
        self.assertEqual(gi.groups([a, b]), [[0], [1]])

    def test_universe_sharing_and_joint_renaming(self) -> None:
        a = [goal("a", const("P", [lmvar("u")])), goal("b", {"kind": "sort", "level": lmvar("u")})]
        b = [goal("c", {"kind": "sort", "level": lmvar("v")}), goal("d", const("P", [lmvar("v")]))]
        c = [goal("c", {"kind": "sort", "level": lmvar("v")}), goal("d", const("P", [lmvar("w")]))]
        self.assertEqual(gi.unordered_state_key(a), gi.unordered_state_key(b))
        self.assertNotEqual(gi.unordered_state_key(a), gi.unordered_state_key(c))
        self.assertEqual(gi.groups(a), [[0, 1]])
        self.assertEqual(gi.groups(c), [[0], [1]])

    def test_metavariable_namespaces_are_separate(self) -> None:
        a = [goal("u", app(mvar("x"), const("P", [lmvar("x")]))), goal("b", mvar("u"))]
        b = [goal("a", app(mvar("t"), const("P", [lmvar("v")]))), goal("c", mvar("a"))]
        self.assertEqual(gi.ordered_state_key(a), gi.ordered_state_key(b))
        self.assertEqual(gi.groups([goal("a", mvar("x")), goal("b", const("P", [lmvar("x")]))]),
                         [[0], [1]])

    def test_universe_constructors(self) -> None:
        universe = {"kind": "imax", "left": {"kind": "succ", "of": {"kind": "zero"}},
                    "right": {"kind": "max", "left": {"kind": "param", "name": "?u.1"},
                              "right": lmvar("u")}}
        a = goal("a", {"kind": "sort", "level": universe})
        b = copy.deepcopy(a)
        b["target"]["level"]["right"]["right"]["id"] = "v"
        self.assertEqual(gi.goal_key(a), gi.goal_key(b))
        b["target"]["level"]["right"]["left"]["name"] = "?u.2"
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))

    def test_permutation_canonicalization(self) -> None:
        goals = [goal(str(i), app(const(chr(65 + i)), mvar("shared"))) for i in range(7)]
        for size in range(1, 5):
            key = gi.unordered_state_key(goals[:size])
            for permutation in itertools.permutations(goals[:size]):
                self.assertEqual(gi.unordered_state_key(list(permutation)), key)
        for size in (5, 6, 7):
            self.assertEqual(gi.unordered_state_key(goals[:size]), gi.unordered_state_key(goals[:size][::-1]))
        self.assertIsNone(gi.unordered_state_key(goals + [goal("8", const("H"))]))
        self.assertIsNone(gi.unordered_state_key(goals, max_goals=6))
        self.assertEqual(gi.unordered_state_key([]), gi.ordered_state_key([]))

    def test_transitive_coupling_in_contexts_and_targets(self) -> None:
        goals = [goal("a", mvar("b")), goal("b", const("True"), [hyp(mvar("third"))]),
                 goal("c", mvar("third"), [hyp(const("Type", [lmvar("universe")]))]),
                 goal("d", const("Type", [lmvar("universe")])), goal("e", const("True"))]
        self.assertEqual(gi.groups(goals), [[0, 1, 2, 3], [4]])
        self.assertEqual(gi.groups([]), [])
        self.assertEqual(gi.groups([goal("a", const("True")), goal("b", const("True"))]), [[0], [1]])

    def test_local_definitions_lambda_let_and_projection(self) -> None:
        n = {"kind": "nat", "value": "12345678901234567890"}
        target = {"kind": "lambda", "binder_info": "explicit", "type": const("Nat"),
                  "body": {"kind": "let", "type": const("Nat"), "value": {"kind": "bvar", "index": 0},
                           "body": {"kind": "projection", "name": "Pair", "index": 0,
                                    "expression": {"kind": "fvar", "position": 0}}}}
        a = goal("a", target, [hyp(const("Nat"), n)])
        b = copy.deepcopy(a)
        self.assertEqual(gi.goal_key(a), gi.goal_key(b))
        b["hyps"][0]["value"]["value"] = "12345678901234567891"
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))
        b = copy.deepcopy(a)
        b["target"]["body"]["body"]["index"] = 1
        self.assertNotEqual(gi.goal_key(a), gi.goal_key(b))

    def test_keys_do_not_mutate_input_and_canonicalize_json_fields(self) -> None:
        goals = [goal("a", app(const("P"), mvar("x")))]
        before = copy.deepcopy(goals)
        self.assertEqual(gi.ordered_state_key(goals), gi.ordered_state_key(json.loads(json.dumps(goals, sort_keys=True))))
        gi.unordered_state_key(goals)
        gi.groups(goals)
        self.assertEqual(goals, before)

    def test_export_and_defined_tactic_with_fake_transport(self) -> None:
        goals = [goal("a", const("True"))]
        repl = SimpleNamespace(timeout=1, _exchange=Mock(return_value={"messages": [
            {"severity": "info", "data": json.dumps(goals)}]}))
        self.assertEqual(gi.export(repl, 3), goals)
        self.assertIn(gi.KEY_TACTIC, repl._exchange.call_args.args[0]["tactic"])
        self.assertEqual(gi.export(repl, 3, tactic="typed_export"), goals)
        self.assertEqual(repl._exchange.call_args.args[0], {
            "tactic": f"set_option maxHeartbeats {gi.HEARTBEATS} in\ntyped_export", "proofState": 3})

    def test_failed_exports_return_none(self) -> None:
        malformed = [None, {}, [None], [goal("a", {"kind": "unsupported"})],
                     [goal("a", {"kind": "fvar", "position": 0})]]
        responses = [{"messages": []}, {"messages": [{"severity": "error", "data": "bad"}]},
                     {"messages": [{"severity": "info", "data": "invalid json"}]}]
        responses += [{"messages": [{"severity": "info", "data": json.dumps(value)}]} for value in malformed]
        for response in responses:
            repl = SimpleNamespace(timeout=1, _exchange=Mock(return_value=response))
            self.assertIsNone(gi.export(repl, 0))
        repl = SimpleNamespace(timeout=1, _exchange=Mock(side_effect=ReplTimeout("timeout")))
        self.assertIsNone(gi.export(repl, 0))


if __name__ == "__main__":
    unittest.main()
