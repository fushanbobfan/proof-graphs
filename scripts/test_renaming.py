#!/usr/bin/env python3
"""Tests of the renaming step on goals as the REPL prints them (no Lean needed).

  python scripts/test_renaming.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from renaming import agrees, hidden, hypotheses, masked, renaming_step  # noqa: E402

CONTEXT = "R : Type u_1\ninst✝¹ : CommRing R\ninst✝ : IsDomain R\nW : WeierstrassCurve R\nhW : IsMinimal R W\n"


class Renaming(unittest.TestCase):
    def test_hypotheses_in_order(self) -> None:
        goal = "case h\nx y v✝ : α × β\np✝ : Walk v✝ y\nh : x ≠ y\n  ∧ True\n⊢ G.Walk x.1 y.1"
        self.assertEqual(hypotheses(goal), ["x", "y", "v✝", "p✝", "h"])
        self.assertEqual(hidden(goal), [2, 3])

    def test_accessible_names(self) -> None:
        goal = CONTEXT + "x : β\ny : β × γ\n⊢ y ∈ u ↔ y.1 ∈ s ∧ x = y.1"
        target = CONTEXT + "b : β\nc : β × γ\n⊢ c ∈ u ↔ c.1 ∈ s ∧ b = c.1"
        self.assertEqual(renaming_step(goal, target), ["rename' x => b, y => c"])

    def test_swap(self) -> None:
        self.assertEqual(renaming_step("a b : ℕ\n⊢ a < b", "b a : ℕ\n⊢ b < a"), ["rename' a => b, b => a"])

    def test_inaccessible_to_accessible(self) -> None:
        goal = CONTEXT + "a✝ : HasGoodReduction R W\n⊢ (reduction R W).IsElliptic"
        target = CONTEXT + "h : HasGoodReduction R W\n⊢ (reduction R W).IsElliptic"
        self.assertEqual(renaming_step(goal, target), ["rename_i h"])

    def test_skipped_inaccessible(self) -> None:
        goal = "a✝¹ : P\na✝ : Q\n⊢ R"
        self.assertEqual(renaming_step(goal, "h : P\na✝ : Q\n⊢ R"), ["rename_i h _"])
        self.assertEqual(renaming_step(goal, "a✝¹ : P\nh : Q\n⊢ R"), ["rename_i h"])

    def test_both_tactics(self) -> None:
        self.assertEqual(renaming_step("h : P\na✝ : Q\n⊢ R", "k : P\nh : Q\n⊢ R"), ["rename' h => k", "rename_i h"])

    def test_shadowing_created_by_rename(self) -> None:
        # after `rename' b => a` the first `a` is shadowed, so `rename_i` counts it and skips it
        self.assertEqual(renaming_step("c✝ : S\na : P\nb : Q\n⊢ R", "h : S\nx✝ : P\na : Q\n⊢ R"),
                         ["rename' b => a", "rename_i h _"])

    def test_target_inaccessible_is_left(self) -> None:
        goal, target = "k : ℕ\n⊢ k + 0 = k", "x✝ : ℕ\n⊢ x✝ + 0 = x✝"
        self.assertEqual(renaming_step(goal, target), [])
        self.assertTrue(agrees(goal, target))
        self.assertFalse(agrees(target, goal))

    def test_no_correspondence(self) -> None:
        self.assertIsNone(renaming_step("a : ℕ\n⊢ a = a", "a : ℤ\n⊢ a = a"))
        self.assertIsNone(renaming_step("a b : ℕ\n⊢ a = b", "a : ℕ\n⊢ a = a"))

    def test_agrees_needs_the_mentionable_names(self) -> None:
        self.assertTrue(agrees("n : ℕ\n⊢ n = n", "n : ℕ\n⊢ n = n"))
        self.assertFalse(agrees("m : ℕ\n⊢ m = m", "n : ℕ\n⊢ n = n"))
        self.assertEqual(masked("inst✝ : Foo α\nx✝ : ℕ\n⊢ x✝ = x✝", [1]), "inst✝ : Foo α\n◊1 : ℕ\n⊢ ◊1 = ◊1")

    def test_names_inside_longer_identifiers_are_kept(self) -> None:
        goal = "h : a ≤ b\nh' : b ≤ c\n⊢ h.trans h' = Nat.h"
        target = "k : a ≤ b\nh' : b ≤ c\n⊢ k.trans h' = Nat.h"
        self.assertEqual(renaming_step(goal, target), ["rename' h => k"])
        self.assertEqual(masked(goal, [0]), "◊0 : a ≤ b\nh' : b ≤ c\n⊢ ◊0.trans h' = Nat.h")


if __name__ == "__main__":
    unittest.main()
