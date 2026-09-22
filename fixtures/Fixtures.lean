/-! Hand-checkable tactic proofs for the extractor. -/

theorem chain (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  apply hqr
  apply hpq
  exact hp

theorem star (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩
  · exact hp
  · exact hq
  · exact hr

theorem mixed (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
  constructor
  · constructor
    · exact hp
    · exact hq
  · constructor
    · exact hq
    · exact hp

theorem arithmetic (n : Nat) (h : 2 ≤ n) : 4 ≤ n + n := by
  omega
