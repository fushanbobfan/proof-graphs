import Mathlib

/-
Adversarial checkpoints for scripts/goal_identity_typed.py. scripts/check_identity_v2_repl.py replays
each example up to its `skip -- ID` checkpoint, exports the goal list there, and checks the relations
below: goal_key for single checkpoints, unordered_state_key for the multi-goal checkpoints.
Expected equalities refer to syntax after instantiation, not to definitional equality.
-/

namespace IdentityV2Fixture

-- S1 and S2: different keys; literal metavariable markers must remain opaque.
example (h : "?[foo]" = "?1") : "?[foo]" = "?1" := by
  skip -- S1
  exact h

example (h : "?1" = "?1") : "?1" = "?1" := by
  skip -- S2
  exact h

-- S3 and S4: different keys; universe-looking text is still literal text.
example (h : "?u.1" = "\"λ\\变量\"") : "?u.1" = "\"λ\\变量\"" := by
  skip -- S3
  exact h

example (h : "?u.2" = "\"λ\\变量\"") : "?u.2" = "\"λ\\变量\"" := by
  skip -- S4
  exact h

-- N1 and N2: equal keys despite escaped and Unicode hypothesis names.
example («x.?[foo]» : Nat) («证据.λ» : «x.?[foo]» = 0) : «x.?[foo]» = 0 := by
  skip -- N1
  exact «证据.λ»

example (n : Nat) (h : n = 0) : n = 0 := by
  skip -- N2
  exact h

-- B1 and B2: equal; B3: different (implicit pi binder).
example : ∀ x : Nat, x = x := by
  skip -- B1
  intro x
  rfl

example : ∀ «变量.λ» : Nat, «变量.λ» = «变量.λ» := by
  skip -- B2
  intro x
  rfl

example : ∀ {x : Nat}, x = x := by
  skip -- B3
  intro x
  rfl

-- L1 and L2: equal lambda trees with different bound names.
example : (fun x : Nat => x) = (fun y : Nat => y) := by
  skip -- L1
  rfl

example : (fun «λ» : Nat => «λ») = (fun «变量» : Nat => «变量») := by
  skip -- L2
  rfl

-- D1 and D2: equal local definitions; D3: different value, even with the same target True.
example : True := by
  let «局部.值» : Nat := 1
  skip -- D1
  trivial

example : True := by
  let n : Nat := 1
  skip -- D2
  trivial

example : True := by
  let n : Nat := 2
  skip -- D3
  trivial

-- W1 and W2: equal unordered keys with a shared existential witness, different ordered keys.
-- W3: different unordered key (the two propositions have independent witnesses).
example (P Q : Nat → Prop) (h : P 0) (k : Q 0) : ∃ n, P n ∧ Q n := by
  refine ⟨?_, ?_⟩
  rotate_left
  constructor
  skip -- W1: [P ?w, Q ?w, Nat witness goal]
  all_goals first | exact h | exact k | exact 0

example (P Q : Nat → Prop) (h : P 0) (k : Q 0) : ∃ n, P n ∧ Q n := by
  refine ⟨?_, ?_⟩
  rotate_left
  constructor
  swap
  skip -- W2: [Q ?w, P ?w, Nat witness goal]
  all_goals first | exact h | exact k | exact 0

example (P Q : Nat → Prop) (h : P 0) (k : Q 0) : (∃ n, P n) ∧ (∃ n, Q n) := by
  constructor
  all_goals refine ⟨?_, ?_⟩
  skip -- W3: independent witnesses; never merge with W1/W2
  all_goals first | exact h | exact k | exact 0

-- U1 and U2: equal after joint level renaming; U3: different level-sharing pattern.
-- Fresh MetaM levels ensure the checkpoints retain unassigned universe metavariables.
example : True := by
  run_tac do
    let original ← Lean.Elab.Tactic.getMainGoal
    original.assign (Lean.mkConst ``True.intro)
    let u ← Lean.Meta.mkFreshLevelMVar
    let a ← Lean.Meta.mkFreshExprMVar (Lean.mkSort u)
    let b ← Lean.Meta.mkFreshExprMVar (Lean.mkSort u)
    Lean.Elab.Tactic.setGoals [a.mvarId!, b.mvarId!]
  skip -- U1: two goals with one shared level metavariable; groups = [[0, 1]]
  all_goals exact Prop

example : True := by
  run_tac do
    let original ← Lean.Elab.Tactic.getMainGoal
    original.assign (Lean.mkConst ``True.intro)
    let v ← Lean.Meta.mkFreshLevelMVar
    let b ← Lean.Meta.mkFreshExprMVar (Lean.mkSort v)
    let a ← Lean.Meta.mkFreshExprMVar (Lean.mkSort v)
    Lean.Elab.Tactic.setGoals [a.mvarId!, b.mvarId!]
  skip -- U2: same sharing, fresh ids; unordered key equals U1
  all_goals exact Prop

example : True := by
  run_tac do
    let original ← Lean.Elab.Tactic.getMainGoal
    original.assign (Lean.mkConst ``True.intro)
    let u ← Lean.Meta.mkFreshLevelMVar
    let v ← Lean.Meta.mkFreshLevelMVar
    let a ← Lean.Meta.mkFreshExprMVar (Lean.mkSort u)
    let b ← Lean.Meta.mkFreshExprMVar (Lean.mkSort v)
    Lean.Elab.Tactic.setGoals [a.mvarId!, b.mvarId!]
  skip -- U3: independent levels; groups = [[0], [1]], unordered key differs from U1
  all_goals exact Prop

end IdentityV2Fixture
