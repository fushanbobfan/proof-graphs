/-!
# First-goal completeness

The combinatorial core of the first-goal argument (Proposition 4 of the paper): a run that may act on any open goal
and reorder the goals arbitrarily, and that ends with no goals, can be reordered into a run that always acts on the
first goal, using the same applications.

The model makes goal-locality structural. A goal is a value, and `step g gs` says that some tactic application turns
the goal `g` into the new goals `gs`; whether it applies, and what it creates, depend on `g` alone, and it changes no
other goal. Goals therefore cannot share metavariables here, and identity up to the names of fresh metavariables is
equality of values. A first-goal run puts the new goals in front of the remaining ones, as Lean's `replaceMainGoal`
does, so it is the depth-first order of the run's goals. An any-goal run may act on any goal and leave the goals in
any order, which covers `pick_goal`, `swap`, and `rotate_left` followed by a tactic on the main goal.
-/

namespace ProofGraphs.FirstGoal

variable {G : Type}

/-- An application as a run records it: the goal acted on and the goals created, in order. -/
abbrev App (G : Type) := G × List G

/-- A run from a state to the empty state that always acts on the first goal, with its applications in order. -/
inductive FirstRun (step : G → List G → Prop) : List G → List (App G) → Prop
  | done : FirstRun step [] []
  | cons {g : G} {gs rest : List G} {t : List (App G)} :
      step g gs → FirstRun step (gs ++ rest) t → FirstRun step (g :: rest) ((g, gs) :: t)

/-- A run from a state to the empty state that may act on any goal: from a permutation of `g :: rest`, an
application to `g` reaches any permutation of `gs ++ rest`. -/
inductive AnyRun (step : G → List G → Prop) : List G → List (App G) → Prop
  | done : AnyRun step [] []
  | apply {s s' : List G} {g : G} {gs rest : List G} {t : List (App G)} :
      step g gs → s.Perm (g :: rest) → s'.Perm (gs ++ rest) → AnyRun step s' t → AnyRun step s ((g, gs) :: t)

variable {step : G → List G → Prop}

/-- Solving `a` first and then `b` solves `a ++ b`. -/
theorem FirstRun.append {a b : List G} {ta tb : List (App G)} (ha : FirstRun step a ta)
    (hb : FirstRun step b tb) : FirstRun step (a ++ b) (ta ++ tb) := by
  induction ha with
  | done => simpa using hb
  | @cons g gs rest t hstep _ ih =>
    have : FirstRun step (gs ++ (rest ++ b)) (t ++ tb) := by simpa [List.append_assoc] using ih
    simpa using FirstRun.cons hstep this

/-- A first-goal run on `a ++ b` solves every goal of `a`, and their descendants, before it touches `b`. -/
theorem FirstRun.split {s : List G} {t : List (App G)} (h : FirstRun step s t) :
    ∀ a b : List G, s = a ++ b → ∃ ta tb, t = ta ++ tb ∧ FirstRun step a ta ∧ FirstRun step b tb := by
  induction h with
  | done =>
    intro a b hab
    have hab' := hab.symm
    simp only [List.append_eq_nil_iff] at hab'
    obtain ⟨rfl, rfl⟩ := hab'
    exact ⟨[], [], rfl, FirstRun.done, FirstRun.done⟩
  | @cons g gs rest t hstep hrun ih =>
    intro a b hab
    cases a with
    | nil =>
      simp only [List.nil_append] at hab
      subst hab
      exact ⟨[], _, rfl, FirstRun.done, FirstRun.cons hstep hrun⟩
    | cons a₀ a' =>
      simp only [List.cons_append, List.cons.injEq] at hab
      obtain ⟨hg, hrest⟩ := hab
      subst hg hrest
      obtain ⟨ta, tb, rfl, hta, htb⟩ := ih (gs ++ a') b (by simp [List.append_assoc])
      exact ⟨(g, gs) :: ta, tb, rfl, FirstRun.cons hstep hta, htb⟩

/-- First-goal solvability does not depend on the order of the goals; only the order of the applications changes. -/
theorem FirstRun.perm {s s' : List G} (p : s.Perm s') :
    ∀ {t : List (App G)}, FirstRun step s t → ∃ t', FirstRun step s' t' ∧ t'.Perm t := by
  induction p with
  | nil => exact fun h => ⟨_, h, List.Perm.refl _⟩
  | cons x _ ih =>
    intro t h
    obtain ⟨tx, tl, rfl, hx, hl⟩ := h.split [x] _ rfl
    obtain ⟨tl', hl', ptl⟩ := ih hl
    exact ⟨tx ++ tl', hx.append hl', ptl.append_left tx⟩
  | swap x y l =>
    intro t h
    obtain ⟨ty, txl, rfl, hy, hxl⟩ := h.split [y] (x :: l) rfl
    obtain ⟨tx, tl, rfl, hx, hl⟩ := hxl.split [x] l rfl
    refine ⟨tx ++ (ty ++ tl), hx.append (hy.append hl), ?_⟩
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := tx) (l₂ := ty)).append_right tl
  | trans _ _ ih₁ ih₂ =>
    intro t h
    obtain ⟨t₁, h₁, p₁⟩ := ih₁ h
    obtain ⟨t₂, h₂, p₂⟩ := ih₂ h₁
    exact ⟨t₂, h₂, p₂.trans p₁⟩

/-- **First-goal completeness.** A run that may act on any goal and ends with no goals can be reordered into a
first-goal run with the same applications. -/
theorem AnyRun.toFirstRun {s : List G} {t : List (App G)} (h : AnyRun step s t) :
    ∃ t', FirstRun step s t' ∧ t'.Perm t := by
  induction h with
  | done => exact ⟨[], FirstRun.done, List.Perm.refl _⟩
  | @apply s s' g gs rest t hstep hs hs' _ ih =>
    obtain ⟨t₁, h₁, p₁⟩ := ih
    obtain ⟨t₂, h₂, p₂⟩ := FirstRun.perm hs' h₁
    obtain ⟨t₃, h₃, p₃⟩ := FirstRun.perm hs.symm (FirstRun.cons hstep h₂)
    exact ⟨t₃, h₃, p₃.trans (((p₂.trans p₁)).cons (g, gs))⟩

/-- Every first-goal run is a run of the more permissive kind. -/
theorem FirstRun.toAnyRun {s : List G} {t : List (App G)} (h : FirstRun step s t) : AnyRun step s t := by
  induction h with
  | done => exact AnyRun.done
  | cons hstep _ ih => exact AnyRun.apply hstep (List.Perm.refl _) (List.Perm.refl _) ih

/-- The two kinds of search reach the empty state from the same states, and a first-goal run needs no more
applications than any run. -/
theorem firstRun_iff_anyRun (s : List G) :
    (∃ t, FirstRun step s t) ↔ ∃ t, AnyRun step s t :=
  ⟨fun ⟨t, h⟩ => ⟨t, h.toAnyRun⟩, fun ⟨_, h⟩ => (h.toFirstRun).elim fun t' ht' => ⟨t', ht'.1⟩⟩

theorem AnyRun.toFirstRun_length {s : List G} {t : List (App G)} (h : AnyRun step s t) :
    ∃ t', FirstRun step s t' ∧ t'.length = t.length :=
  h.toFirstRun.elim fun t' ht' => ⟨t', ht'.1, ht'.2.length_eq⟩

end ProofGraphs.FirstGoal
