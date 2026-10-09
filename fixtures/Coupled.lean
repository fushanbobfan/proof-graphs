/-! A proof whose goals share a metavariable. Its goal-origin graph is a forest with one goal per step, so the
sample rule of orderings-replay-v0.1 admits it, and of its two orderings only the original replays. -/

theorem coupled_witness : ∃ n : Nat, n + 1 = 5 := by
  refine ⟨?_, ?_⟩
  exact 4
  decide
