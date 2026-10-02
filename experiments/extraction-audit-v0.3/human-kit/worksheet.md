# Worksheet

## 1. `Nat.leRec_succ'`

Source: `.lake/packages/mathlib/Mathlib/Data/Nat/Init.lean`, from line 174.

```lean
  172  
  173  lemma leRec_succ' {n} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le) :
  174      (leRec (motive := motive) refl le_succ_of_le (le_succ _)) = le_succ_of_le _ refl := by
  175    rw [leRec_succ, leRec_self]
  176  
```

Steps (line, tactic):

Edges [i, j]:

## 2. `Nat.decreasingInduction_succ_left`

Source: `.lake/packages/mathlib/Mathlib/Data/Nat/Init.lean`, from line 312.

```lean
  310      (smn : m + 1 ≤ n) (mn : m ≤ n) :
  311      decreasingInduction (motive := motive) of_succ self mn =
  312        of_succ m smn (decreasingInduction of_succ self smn) := by
  313    rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn),
  314      decreasingInduction_trans (n := m + 1) (Nat.le_succ m),
  315      decreasingInduction_succ']
  316  
```

Steps (line, tactic):

Edges [i, j]:

## 3. `Submodule.mapQ_pow`

Source: `.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`, from line 210.

```lean
  208  theorem mapQ_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
  209      (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
  210      p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k := by
  211    induction k with
  212    | zero => simp [Module.End.one_eq_id]
  213    | succ k ih =>
  214      simp only [Module.End.iterate_succ]
  215      rw [mapQ_comp, ih]
  216      exact p.le_comap_pow_of_le_comap h k
  217  
```

Steps (line, tactic):

Edges [i, j]:

## 4. `Submodule.Quotient.equiv_trans`

Source: `.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean`, from line 351.

```lean
  349      (hef : P.map (e.trans f : M →ₗ[R] O) = S) :
  350      Quotient.equiv P S (e.trans f) hef =
  351        (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) := by
  352    ext
  353    -- `simp` can deal with `hef` depending on `e` and `f`
  354    simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  355    -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  356    rw [mapQ_comp, LinearMap.comp_apply]
  357  
```

Steps (line, tactic):

Edges [i, j]:

## 5. `TensorPower.gradedMonoid_eq_of_cast`

Source: `.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Basic.lean`, from line 125.

```lean
  123  @[ext (iff := false)]
  124  theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
  125      (h2 : cast R M h a.snd = b.snd) : a = b := by
  126    refine gradedMonoid_eq_of_reindex_cast h ?_
  127    rw [cast] at h2
  128    rw [← finCongr_eq_equivCast, ← h2]
  129  
```

Steps (line, tactic):

Edges [i, j]:

## 6. `ZMod.fieldRange_castHom_eq_bot`

Source: `.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Basic.lean`, from line 584.

```lean
  582  
  583  theorem fieldRange_castHom_eq_bot (p : ℕ) [Fact p.Prime] [DivisionRing K] [CharP K p] :
  584      (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K) := by
  585    rw [RingHom.fieldRange_eq_map, ← Subfield.map_bot (K := ZMod p), Subsingleton.elim ⊥]
  586  
```

Steps (line, tactic):

Edges [i, j]:

## 7. `ProbabilityTheory.Kernel.partialTraj_eq_prod`

Source: `.lake/packages/mathlib/Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.lean`, from line 211.

```lean
  209      partialTraj κ a b =
  210      (Kernel.id ×ₖ (partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map
  211      (IicProdIoc a b) := by
  212    obtain hba | hab := le_total b a
  213    · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
  214        fst_prod, id_map]
  215      all_goals fun_prop
  216    induction b, hab using Nat.le_induction with
  217    | base =>
  218      ext1 x
  219      rw [partialTraj_self, id_map, map_apply, prod_apply, IicProdIoc_self, ← Measure.fst,
  220      Measure.fst_prod]
  221      all_goals fun_prop
  222    | succ k h hk =>
  223      have : (IicProdIoc (X := X) k (k + 1)) ∘ (Prod.map (IicProdIoc a k) id) =
  224          (IicProdIoc (h.trans k.le_succ) ∘ (Prod.map id (IocProdIoc a k (k + 1)))) ∘
  225          prodAssoc := by
  226        ext x i
  227        simp only [IicProdIoc_def, MeasurableEquiv.IicProdIoc, MeasurableEquiv.coe_mk,
  228          Equiv.coe_fn_mk, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
  229          Nat.succ_eq_add_one, IocProdIoc]
  230        split_ifs <;> try rfl
  231        lia
  232      nth_rw 1 [← partialTraj_comp_partialTraj h k.le_succ, hk, partialTraj_succ_self, comp_map,
  233        comap_map_comm, comap_prod, id_comap, ← id_map, map_prod_eq, ← map_comp_right, this,
  234        map_comp_right, id_prod_eq, prodAssoc_prod, map_comp_right, ← map_prod_map, map_id,
  235        ← map_comp, map_apply_eq_iff_map_symm_apply_eq, fst_prod_comp_id_prod, ← map_comp_right,
  236        ← coe_IicProdIoc (h.trans k.le_succ), symm_comp_self, map_id,
  237        deterministic_congr IicProdIoc_comp_restrict₂.symm, ← deterministic_comp_deterministic,
  238        comp_deterministic_eq_comap, ← comap_prod, ← map_comp, ← comp_map, ← hk,
  239        ← partialTraj_comp_partialTraj h k.le_succ, partialTraj_succ_self, map_comp, map_comp,
  240        ← map_comp_right, ← id_map, map_prod_eq, ← map_comp_right]
  241      · rfl
  242      all_goals fun_prop
  243  
```

Steps (line, tactic):

Edges [i, j]:

## 8. `ProofNetIR.SequentialFigure7.UnifyPayloadStep.payloadMemWaitingMiddle`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyPayloadInvariant.lean`, from line 1863.

```lean
 1861      (step : UnifyPayloadStep certificate before after)
 1862      {vertex : Vertex} (membership : vertex ∈ step.payload) :
 1863      vertex ∈ step.prepared.after.stack.waitingVertices := by
 1864    unfold SequentialStackState.waitingVertices
 1865    apply List.mem_flatMap.mpr
 1866    refine ⟨.initialized step.payload, ?_, ?_⟩
 1867    · apply List.mem_of_getElem?
 1868      change step.prepared.stackResult.after.waiting.toList[_]? =
 1869        some (WaitingCell.initialized step.payload)
 1870      rw [Array.getElem?_toList]
 1871      exact step.waiting_payload
 1872    · simpa [WaitingCell.vertices] using membership
 1873  
```

Steps (line, tactic):

Edges [i, j]:

## 9. `ProofNetIR.UnificationState.markReadyRaw?_abstractable`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerBridge.lean`, from line 188.

```lean
  186      (rawAgeBound : rawAge < before.parents.size)
  187      (equation : before.markReadyRaw? vertex rawAge = .ok after) :
  188      after.Abstractable certificate := by
  189    rcases markReadyRaw?_ok_iff.mp equation with ⟨step⟩
  190    have vertexBound : vertex < before.marks.size :=
  191      (Array.getElem?_eq_some_iff.mp step.unmarked).1
  192    rw [step.after_eq]
  193    refine {
  194      markArraySize := by
  195        simpa using abstractable.markArraySize
  196      markedVertexBound := ?_
  197      markedTokenBound := ?_
  198      representativeBound := abstractable.representativeBound
  199      representativeIdempotent :=
  200        abstractable.representativeIdempotent }
  201    · intro candidate token marked
  202      by_cases same : vertex = candidate
  203      · simpa [same, abstractable.markArraySize] using
  204          (show vertex < certificate.formulas.size by
  205            rw [← abstractable.markArraySize]
  206            exact vertexBound)
  207      · apply abstractable.markedVertexBound
  208        unfold assignedToken? at marked ⊢
  209        simpa [Array.getElem?_setIfInBounds, same] using marked
  210    · intro candidate token marked
  211      by_cases same : vertex = candidate
  212      · subst candidate
  213        unfold assignedToken? at marked
  214        simp [vertexBound] at marked
  215        subst token
  216        exact rawAgeBound
  217      · apply abstractable.markedTokenBound
  218        unfold assignedToken? at marked ⊢
  219        simpa [Array.getElem?_setIfInBounds, same] using marked
  220  
```

Steps (line, tactic):

Edges [i, j]:

## 10. `ProofNetIR.UnificationState.markReadyRaw?_componentsFormulaConsistent`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerBridge.lean`, from line 229.

```lean
  227      (consistent : before.ComponentsFormulaConsistent certificate)
  228      (equation : before.markReadyRaw? vertex rawAge = .ok after) :
  229      after.ComponentsFormulaConsistent certificate := by
  230    have componentsEquation := (markReadyRaw?_carriers equation).2
  231    intro index component lookup
  232    apply consistent
  233    rw [componentsEquation] at lookup
  234    exact lookup
  235  
```

Steps (line, tactic):

Edges [i, j]:

## 11. `ProofNetIR.Certificate.reserveAxiomAt?_abstractable`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerBridge.lean`, from line 395.

```lean
  393      (equation :
  394        certificate.reserveAxiomAt? before linkIndex = some after) :
  395      after.Abstractable certificate := by
  396    rcases certificate.reserveAxiomAt?_exact equation with
  397      ⟨left, right, component, exactLink, ready, componentLookup,
  398        frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  399    have afterOrdered :
  400        after.OrderedParents :=
  401      certificate.reserveAxiomAt?_orderedParents ordered equation
  402    apply afterOrdered.abstractable
  403    · simpa [marksEq] using abstractable.markArraySize
  404    · intro vertex token marked
  405      apply abstractable.markedVertexBound
  406      unfold UnificationState.assignedToken? at marked ⊢
  407      rw [marksEq] at marked
  408      exact marked
  409    · intro vertex token marked
  410      have beforeMarked :
  411          before.assignedToken? vertex = some token := by
  412        unfold UnificationState.assignedToken? at marked ⊢
  413        rw [marksEq] at marked
  414        exact marked
  415      have oldBound := abstractable.markedTokenBound beforeMarked
  416      rw [parentsEq]
  417      simpa using Nat.lt_succ_of_lt oldBound
  418  
```

Steps (line, tactic):

Edges [i, j]:

## 12. `ProofNetIR.Certificate.reserveAxiomAt?_componentsFormulaConsistent`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerBridge.lean`, from line 427.

```lean
  425      (equation :
  426        certificate.reserveAxiomAt? before linkIndex = some after) :
  427      after.ComponentsFormulaConsistent certificate := by
  428    rcases certificate.reserveAxiomAt?_exact equation with
  429      ⟨left, right, component, exactLink, ready, componentLookup,
  430        frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  431    have componentConsistent :
  432        component.FormulaConsistent certificate :=
  433      UnificationComponent.axiom?_formulaConsistent
  434        ((certificate.linkLocallyWellFormed_iff _).mp ready.1)
  435        componentLookup
  436    have pushed :
  437        ({ before with
  438          components :=
  439            before.components.push (some component) } :
  440          UnificationState).ComponentsFormulaConsistent certificate :=
  441      consistent.push componentConsistent
  442    unfold UnificationState.ComponentsFormulaConsistent at pushed ⊢
  443    intro index candidate lookup
  444    apply pushed
  445    rw [componentsEq] at lookup
  446    exact lookup
  447  
```

Steps (line, tactic):

Edges [i, j]:

## 13. `ProofNetIR.SequentialFigure7.UnifyOneStep.waitingConclusion_mem_waiting_middle`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerInvariant.lean`, from line 6546.

```lean
 6544      (step : UnifyOneStep certificate before after) :
 6545      step.waitingConclusion ∈
 6546        step.prepared.after.stack.waitingVertices := by
 6547    unfold SequentialStackState.waitingVertices
 6548    apply List.mem_flatMap.mpr
 6549    refine ⟨.initialized [step.waitingConclusion], ?_, by simp
 6550      [WaitingCell.vertices]⟩
 6551    apply List.mem_of_getElem?
 6552    change step.prepared.stackResult.after.waiting.toList[_]? =
 6553      some (WaitingCell.initialized [step.waitingConclusion])
 6554    rw [Array.getElem?_toList]
 6555    exact step.waiting_one
 6556  
```

Steps (line, tactic):

Edges [i, j]:

## 14. `ProofNetIR.UnificationState.ObservationEquivalent.abstractable`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 718.

```lean
  716      (equivalent : first.ObservationEquivalent second)
  717      (abstractable : first.Abstractable certificate) :
  718      second.Abstractable certificate := by
  719    refine {
  720      markArraySize := by
  721        rw [← equivalent.marks]
  722        exact abstractable.markArraySize
  723      markedVertexBound := ?_
  724      markedTokenBound := ?_
  725      representativeBound := ?_
  726      representativeIdempotent := ?_
  727    }
  728    · intro vertex token marked
  729      apply abstractable.markedVertexBound
  730      unfold assignedToken? at marked ⊢
  731      rw [equivalent.marks]
  732      exact marked
  733    · intro vertex token marked
  734      have oldMarked : first.assignedToken? vertex = some token := by
  735        unfold assignedToken? at marked ⊢
  736        rw [equivalent.marks]
  737        exact marked
  738      rw [← equivalent.parents]
  739      exact abstractable.markedTokenBound oldMarked
  740    · intro token bound
  741      have oldBound : token < first.parents.size := by
  742        simpa [equivalent.parents] using bound
  743      simpa [representative, equivalent.parents] using
  744        abstractable.representativeBound oldBound
  745    · intro token bound
  746      have oldBound : token < first.parents.size := by
  747        simpa [equivalent.parents] using bound
  748      simpa [representative, equivalent.parents] using
  749        abstractable.representativeIdempotent oldBound
```

Steps (line, tactic):

Edges [i, j]:

## 15. `mem_generatePiSystem_iUnion_elim`

Source: `.lake/packages/mathlib/Mathlib/MeasureTheory/PiSystem.lean`, from line 285.

```lean
  283  theorem mem_generatePiSystem_iUnion_elim {α β} {g : β → Set (Set α)} (h_pi : ∀ b, IsPiSystem (g b))
  284      (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b, g b)) :
  285      ∃ (T : Finset β) (f : β → Set α), (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b := by
  286    classical
  287    induction h_t with
  288    | @base s h_s =>
  289      rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩
  290      refine ⟨{b}, fun _ => s, ?_⟩
  291      simpa using h_s_in_t'
  292    | inter h_gen_s h_gen_t' h_nonempty h_s h_t' =>
  293      rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩
  294      rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩⟩⟩
  295      use T_s ∪ T_t', fun b : β =>
  296        if b ∈ T_s then if b ∈ T_t' then f_s b ∩ f_t' b else f_s b
  297        else if b ∈ T_t' then f_t' b else (∅ : Set α)
  298      constructor
  299      · ext a
  300        simp_rw [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
  301        grind
  302      intro b h_b
  303      split_ifs with hbs hbt hbt
  304      · refine h_pi b (f_s b) (h_s b hbs) (f_t' b) (h_t' b hbt) (Set.Nonempty.mono ?_ h_nonempty)
  305        exact Set.inter_subset_inter (Set.biInter_subset_of_mem hbs) (Set.biInter_subset_of_mem hbt)
  306      · exact h_s b hbs
  307      · exact h_t' b hbt
  308      · rw [Finset.mem_union] at h_b
  309        apply False.elim (h_b.elim hbs hbt)
  310  
```

Steps (line, tactic):

Edges [i, j]:

## 16. `ProofNetIR.Certificate.firePar?_success_conclusion_frontier`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 4856.

```lean
 4854        next.tokenAt? conclusion = some outputToken ∧
 4855          next.componentAt? outputToken = some nextComponent ∧
 4856            conclusion ∈ nextComponent.frontier := by
 4857    rcases firePar?_success_observation equation with
 4858      ⟨outputToken, forwardEquation, observation⟩
 4859    have guards := state.forwardToken?_success forwardEquation
 4860    have outputRoot : state.representative outputToken = outputToken :=
 4861      abstractable.tokenAt?_root guards.2.1
 4862    have conclusionToken :
 4863        next.tokenAt? conclusion = some outputToken :=
 4864      firePar?_success_conclusion_tokenAt?
 4865        abstractable forwardEquation equation
 4866    unfold firePar? at equation
 4867    rw [forwardEquation] at equation
 4868    cases componentLookup :
 4869        state.componentAt? outputToken with
 4870    | none =>
 4871        simp [componentLookup] at equation
 4872    | some component =>
 4873        simp only [componentLookup] at equation
 4874        cases leftPick : pickVertex? component.frontier left with
 4875        | none =>
 4876            simp [leftPick] at equation
 4877        | some leftResult =>
 4878            rcases leftResult with ⟨leftIndex, afterLeft⟩
 4879            simp only [leftPick] at equation
 4880            cases rightPick : pickVertex? afterLeft right with
 4881            | none =>
 4882                simp [rightPick] at equation
 4883            | some rightResult =>
 4884                rcases rightResult with ⟨rightIndex, context⟩
 4885                simp only [rightPick] at equation
 4886                injection equation with nextEquation
 4887                have nextOutputRoot :
 4888                    next.representative outputToken = outputToken := by
 4889                  rw [observation.representative_eq outputToken]
 4890                  simpa [UnificationState.representative,
 4891                    UnificationState.markConclusion] using outputRoot
 4892                have componentRaw :
 4893                    state.components[outputToken]? =
 4894                      some (some component) := by
 4895                  have rawAtRepresentative :=
 4896                    UnificationState.componentAt?_some_raw
 4897                      componentLookup
 4898                  simpa [outputRoot] using rawAtRepresentative
 4899                have outputBound :
 4900                    outputToken < state.components.size :=
 4901                  (Array.getElem?_eq_some_iff.mp componentRaw).1
 4902                subst next
 4903                let replacement : UnificationComponent :=
 4904                  { tree := .par leftIndex rightIndex component.tree
 4905                    frontier := context ++ [conclusion] }
 4906                refine
 4907                  ⟨outputToken, replacement, conclusionToken, ?_, ?_⟩
 4908                · unfold UnificationState.componentAt?
 4909                  rw [nextOutputRoot]
 4910                  simp [replacement, outputBound]
 4911                · simp [replacement]
 4912  
```

Steps (line, tactic):

Edges [i, j]:

## 17. `FiniteField.sum_pow_units`

Source: `.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Basic.lean`, from line 295.

```lean
  293  is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
  294  theorem sum_pow_units [DecidableEq K] (i : ℕ) :
  295      (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  296    let φ : Kˣ →* K :=
  297      { toFun := fun x => x ^ i
  298        map_one' := by simp
  299        map_mul' := by simp [mul_pow] }
  300    have : Decidable (φ = 1) := by classical infer_instance
  301    calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
  302        _ = if q - 1 ∣ i then -1 else 0 := by
  303          suffices q - 1 ∣ i ↔ φ = 1 by
  304            simp only [this]
  305            split_ifs; swap
  306            · exact Nat.cast_zero
  307            · rw [Fintype.card_units, Nat.cast_sub,
  308                cast_card_eq_zero, Nat.cast_one, zero_sub]
  309              show 1 ≤ q; exact Fintype.card_pos_iff.mpr ⟨0⟩
  310          rw [← forall_pow_eq_one_iff, DFunLike.ext_iff]
  311          apply forall_congr'; intro x; simp [φ, Units.ext_iff]
  312  
```

Steps (line, tactic):

Edges [i, j]:

## 18. `ProofNetIR.SequentialFigure7.UnifyOneStep.producedPremisesMarked`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerInvariant.lean`, from line 7432.

```lean
 7430      (step : UnifyOneStep certificate before after)
 7431      (invariant : SchedulerInvariant certificate before) :
 7432      ProducedPremisesMarked certificate after := by
 7433    have middleInvariant := step.prepared.schedulerInvariant invariant
 7434    intro link linkMembership
 7435    cases link with
 7436    | «axiom» left right => trivial
 7437    | «par» left right conclusion
 7438    | tensor left right conclusion =>
 7439        intro producedAfter
 7440        rcases step.produced_after_cases invariant producedAfter with
 7441          waitingEq | tensorEq | producedMiddle
 7442        · subst conclusion
 7443          have currentMembership :
 7444              (.par step.activationStep.producer.storedLeft
 7445                step.activationStep.producer.storedRight
 7446                step.waitingConclusion : Link) ∈ certificate.links :=
 7447            List.mem_of_getElem? step.submitted_waiting_par
 7448          have producerEq :=
 7449            UnificationState.StructurallyWellFormed.producerLink_unique
 7450              invariant.structural
 7451              (conclusion := step.waitingConclusion)
 7452              linkMembership (by simp [Link.produces])
 7453              currentMembership (by simp [Link.produces])
 7454          cases producerEq <;>
 7455            exact step.waitingPremisesMarkedAfter
 7456        · subst conclusion
 7457          have currentMembership :
 7458              (.tensor step.consumer.storedLeft step.consumer.storedRight
 7459                step.consumer.conclusion : Link) ∈ certificate.links :=
 7460            List.mem_of_getElem? step.submitted_tensor
 7461          have producerEq :=
 7462            UnificationState.StructurallyWellFormed.producerLink_unique
 7463              invariant.structural
 7464              (conclusion := step.consumer.conclusion)
 7465              linkMembership (by simp [Link.produces])
 7466              currentMembership (by simp [Link.produces])
 7467          cases producerEq <;>
 7468            exact step.tensorPremisesMarkedAfter
 7469        · rcases middleInvariant.produced_premises_marked
 7470              linkMembership producedMiddle with
 7471            ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
 7472          refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
 7473          · rw [step.core_marks_eq]
 7474            exact leftMarked
 7475          · rw [step.core_marks_eq]
 7476            exact rightMarked
 7477  
```

Steps (line, tactic):

Edges [i, j]:

## 19. `ProofNetIR.SequentialFigure7.CanonicalTagHistory.sameRepresentative_conclusionTouch_decomposition`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7EqualBoundaryCommitmentTargetAvoidance.lean`, from line 247.

```lean
  245          event.search.result.trace =
  246            beforeTrace ++ guard.tensor.conclusion ::
  247              guard.head.vertex :: afterTrace := by
  248    have mateUntouched : ¬ event.Touched guard.tensor.mate := by
  249      intro mateTouched
  250      apply tagHistory.not_event_touch_of_sameRepresentative correct invariant guard
  251        membership sameRepresentative mateTouched
  252      exact .visited (.refl guard.tensor.mate)
  253    have conclusionInTrace :
  254        guard.tensor.conclusion ∈ event.search.result.trace := by
  255      rcases touched with inTrace | leftEq | rightEq
  256      · exact inTrace
  257      · exfalso
  258        exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
  259          (List.mem_of_getElem? event.search.result.exactLink) (Or.inl rfl)
  260          (List.mem_of_getElem? guard.tensor_valid.2.1)
  261          (by simpa [Link.produces] using leftEq)
  262      · exfalso
  263        exact invariant.structural.axiomEndpoint_ne_connectiveConclusion
  264          (List.mem_of_getElem? event.search.result.exactLink) (Or.inr rfl)
  265          (List.mem_of_getElem? guard.tensor_valid.2.1)
  266          (by simpa [Link.produces] using rightEq)
  267    have sideLeft : guard.tensor.side = .storedLeft := by
  268      cases sideEquation : guard.tensor.side with
  269      | storedLeft => exact rfl
  270      | storedRight =>
  271          exfalso
  272          apply mateUntouched
  273          have conclusionReach :
  274              SourceLeftReachable certificate event.start
  275                guard.tensor.conclusion := by
  276            have region := event.touched_sourceLeftRegion touched
  277            cases region with
  278            | visited reachable => exact reachable
  279            | terminalPartner reachable exactAxiom =>
  280                rcases exactAxiom with axiomEq | axiomEq
  281                · exact False.elim
  282                    (invariant.structural.axiomEndpoint_ne_connectiveConclusion
  283                      (List.mem_of_getElem? axiomEq) (Or.inr rfl)
  284                      (List.mem_of_getElem? guard.tensor_valid.2.1)
  285                      (by simp [Link.produces]))
  286                · exact False.elim
  287                    (invariant.structural.axiomEndpoint_ne_connectiveConclusion
  288                      (List.mem_of_getElem? axiomEq) (Or.inl rfl)
  289                      (List.mem_of_getElem? guard.tensor_valid.2.1)
  290                      (by simp [Link.produces]))
  291          have storedLeftReach :
  292              SourceLeftReachable certificate event.start guard.tensor.storedLeft :=
  293            sourceLeftReachable_trans conclusionReach
  294              (.step (.tensor guard.tensor_valid.2.1)
  295                (.refl guard.tensor.storedLeft))
  296          have storedLeftTouched : event.Touched guard.tensor.storedLeft :=
  297            event.sourceLeftRegion_touched invariant.structural
  298              (.visited storedLeftReach)
  299          simpa [TensorBelow.mate, TensorPremiseSide.mate, sideEquation] using
  300            storedLeftTouched
  301    have headIsStoredLeft :
  302        guard.head.vertex = guard.tensor.storedLeft := by
  303      simpa [TensorBelow.premise, TensorPremiseSide.premise, sideLeft] using
  304        guard.tensor_valid.2.2.2
  305    have reachedEndpoint :
  306        event.search.reached = event.search.result.left ∨
  307          event.search.reached = event.search.result.right := by
  308      rcases event.search.route.storedEndpoints with endpoints | endpoints
  309      · exact Or.inl endpoints.1
  310      · exact Or.inr endpoints.1
  311    rcases SourceLeftChain.decompose_at_step invariant.structural
  312        event.search.route.chain event.search.route.traceLast
  313        event.search.result.exactLink reachedEndpoint conclusionInTrace
  314        (.tensor guard.tensor_valid.2.1) with
  315      ⟨beforeTrace, afterTrace, decomposition⟩
  316    refine ⟨sideLeft, beforeTrace, afterTrace, ?_⟩
  317    simpa [headIsStoredLeft] using decomposition
  318  
```

Steps (line, tactic):

Edges [i, j]:

## 20. `ProofNetIR.SequentialFigure7.FreshSourceLeftRoute.source_is_axiom_of_axiom_endpoint`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7NewRegion.lean`, from line 213.

```lean
  211      ∃ sourceLeft sourceRight,
  212        source.link = .axiom sourceLeft sourceRight ∧
  213          (endpoint = sourceLeft ∨ endpoint = sourceRight) := by
  214    have expectedWellFormed :=
  215      structural.2.2.2.2.1 _ expectedMembership
  216    rcases expectedWellFormed.axiom_endpointFormula expectedEndpoint with
  217      ⟨name, positive, expectedFormula⟩
  218    have sourceWellFormed :=
  219      structural.2.2.2.2.1 _ sourceMembership
  220    cases sourceLinkEquation : source.link with
  221    | «axiom» sourceLeft sourceRight =>
  222        refine ⟨sourceLeft, sourceRight, rfl, ?_⟩
  223        rcases sourceOrigin with sourceAxiom | sourceProduces
  224        · have reversed :
  225              sourceLeft = endpoint ∨ sourceRight = endpoint := by
  226            simpa [sourceLinkEquation, Link.containsAxiomEndpoint] using sourceAxiom
  227          exact reversed.imp Eq.symm Eq.symm
  228        · simp [sourceLinkEquation, Link.produces] at sourceProduces
  229    | tensor sourceLeft sourceRight sourceConclusion =>
  230        have sourceWellFormed' :
  231            certificate.LinkWellFormed
  232              (.tensor sourceLeft sourceRight sourceConclusion) := by
  233          simpa [sourceLinkEquation] using sourceWellFormed
  234        rcases sourceOrigin with sourceAxiom | sourceProduces
  235        · simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
  236        · simp [sourceLinkEquation, Link.produces] at sourceProduces
  237          subst sourceConclusion
  238          rcases sourceWellFormed'.tensor_conclusionFormula with
  239            ⟨leftFormula, rightFormula, sourceFormula⟩
  240          have impossible := Option.some.inj
  241            (expectedFormula.symm.trans sourceFormula)
  242          cases impossible
  243    | «par» sourceLeft sourceRight sourceConclusion =>
  244        have sourceWellFormed' :
  245            certificate.LinkWellFormed
  246              (.par sourceLeft sourceRight sourceConclusion) := by
  247          simpa [sourceLinkEquation] using sourceWellFormed
  248        rcases sourceOrigin with sourceAxiom | sourceProduces
  249        · simp [sourceLinkEquation, Link.containsAxiomEndpoint] at sourceAxiom
  250        · simp [sourceLinkEquation, Link.produces] at sourceProduces
  251          subst sourceConclusion
  252          rcases sourceWellFormed'.par_conclusionFormula with
  253            ⟨leftFormula, rightFormula, sourceFormula⟩
  254          have impossible := Option.some.inj
  255            (expectedFormula.symm.trans sourceFormula)
  256          cases impossible
  257  
```

Steps (line, tactic):

Edges [i, j]:

## 21. `ProofNetIR.Certificate.processWorklistLink_core_componentsFormulaConsistent`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 12088.

```lean
12086      (consistent : state.core.ComponentsFormulaConsistent certificate) :
12087      (processWorklistLink certificate consumers index state).core
12088        |>.ComponentsFormulaConsistent certificate := by
12089    intro componentIndex component componentLookup
12090    cases linkLookup : certificate.links[index]? with
12091    | none =>
12092        apply consistent
12093        simpa [processWorklistLink, linkLookup] using componentLookup
12094    | some link =>
12095        have linkMembership : link ∈ certificate.links :=
12096          List.mem_of_getElem? linkLookup
12097        have wellFormed : certificate.LinkWellFormed link :=
12098          structural.2.2.2.2.1 link linkMembership
12099        cases link with
12100        | «axiom» left right =>
12101            apply consistent
12102            simpa [processWorklistLink, linkLookup] using componentLookup
12103        | «par» left right conclusion =>
12104            cases leftLookup : state.core.tokenAt? left with
12105            | none =>
12106                apply consistent
12107                simpa [processWorklistLink, linkLookup, leftLookup] using
12108                  componentLookup
12109            | some leftToken =>
12110                cases rightLookup : state.core.tokenAt? right with
12111                | none =>
12112                    apply consistent
12113                    simpa [processWorklistLink, linkLookup, leftLookup,
12114                      rightLookup] using componentLookup
12115                | some rightToken =>
12116                    by_cases same : leftToken = rightToken
12117                    · subst rightToken
12118                      cases firing :
12119                          firePar? state.core left right conclusion with
12120                      | none =>
12121                          apply consistent
12122                          simpa [processWorklistLink, linkLookup, leftLookup,
12123                            rightLookup, firing] using componentLookup
12124                      | some nextCore =>
12125                          have nextConsistent :
12126                              nextCore.ComponentsFormulaConsistent certificate :=
12127                            firePar?_success_componentsFormulaConsistent
12128                              consistent wellFormed firing
12129                          apply nextConsistent
12130                          simpa [processWorklistLink, linkLookup, leftLookup,
12131                            rightLookup, firing] using componentLookup
12132                    · apply consistent
12133                      simpa [processWorklistLink, linkLookup, leftLookup,
12134                        rightLookup, same] using componentLookup
12135        | «tensor» left right conclusion =>
12136            cases leftLookup : state.core.tokenAt? left with
12137            | none =>
12138                apply consistent
12139                simpa [processWorklistLink, linkLookup, leftLookup] using
12140                  componentLookup
12141            | some leftToken =>
12142                cases rightLookup : state.core.tokenAt? right with
12143                | none =>
12144                    apply consistent
12145                    simpa [processWorklistLink, linkLookup, leftLookup,
12146                      rightLookup] using componentLookup
12147                | some rightToken =>
12148                    by_cases same : leftToken = rightToken
12149                    · subst rightToken
12150                      apply consistent
12151                      simpa [processWorklistLink, linkLookup, leftLookup,
12152                        rightLookup] using componentLookup
12153                    · cases firing :
12154                          fireTensor? state.core left right conclusion with
12155                      | none =>
12156                          apply consistent
12157                          simpa [processWorklistLink, linkLookup, leftLookup,
12158                            rightLookup, same, firing] using componentLookup
12159                      | some nextCore =>
12160                          have nextConsistent :
12161                              nextCore.ComponentsFormulaConsistent certificate :=
12162                            fireTensor?_success_componentsFormulaConsistent
12163                              consistent wellFormed firing
12164                          apply nextConsistent
12165                          simpa [processWorklistLink, linkLookup, leftLookup,
12166                            rightLookup, same, firing] using componentLookup
```

Steps (line, tactic):

Edges [i, j]:

## 22. `ProofNetIR.SequentialFigure7.UnifyPayloadStep.createdConclusionFutureWorkAt`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7ContinuationCredit.lean`, from line 303.

```lean
  301      (step : UnifyPayloadStep certificate before after) :
  302      FutureWorkAt after step.previousBoundary
  303        step.consumer.conclusion := by
  304    have afterStack : after.stack = step.stackAfter :=
  305      congrArg ReservationState.stack step.output_eq
  306    have afterSigma :
  307        after.stack.sigma = step.mergeStep.sigmaPrefix ++
  308          [step.previousBoundary] := by
  309      rw [afterStack]
  310      exact step.exact.1
  311    have afterReady :
  312        after.stack.ready = step.mergeStep.readyPrefix ++
  313          [step.consumer.conclusion ::
  314            (step.payload ++ step.mergeStep.previousReady ++
  315              step.mergeStep.activeReady)] := by
  316      rw [afterStack]
  317      exact step.exact.2.1
  318    have prefixLengths :
  319        step.mergeStep.sigmaPrefix.length =
  320          step.mergeStep.readyPrefix.length := by
  321      have middleInvariant :
  322          ReservationInvariant certificate step.prepared.after :=
  323        step.prepared.reservationInvariant step.before_invariant
  324      have aligned := middleInvariant.stack_wellShaped.ready_aligned
  325      change
  326        step.prepared.stackResult.after.ready.length =
  327          step.prepared.stackResult.after.sigma.length at aligned
  328      rw [step.mergeStep.ready_eq, step.mergeStep.sigma_eq] at aligned
  329      simp at aligned
  330      omega
  331    apply FutureWorkAt.ready
  332      (position := step.mergeStep.sigmaPrefix.length)
  333      (bucket := step.consumer.conclusion ::
  334        (step.payload ++ step.mergeStep.previousReady ++
  335          step.mergeStep.activeReady))
  336    · rw [afterSigma]
  337      simp
  338    · rw [afterReady, prefixLengths]
  339      simp
  340    · simp
  341  
```

Steps (line, tactic):

Edges [i, j]:

## 23. `ProofNetIR.SequentialFigure7.RegionClosure.class_of_empty_active`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Figure7/Closure.lean`, from line 2276.

```lean
 2274      (seedBound : seed < certificate.formulas.size)
 2275      {vertex : Vertex} (bound : vertex < certificate.formulas.size) :
 2276      markClass? state.stack vertex = some age := by
 2277    by_cases inside : markClass? state.stack vertex = some age
 2278    · exact inside
 2279    exfalso
 2280    have structural := correct.1
 2281    have bucketEq : bucketAt? state.stack age = some [] :=
 2282      bucketAt?_last invariant.stack_wellShaped.sigma_partition.strictIncreasing
 2283        invariant.stack_wellShaped.ready_aligned sigmaLast readyLast
 2284    have seedInside : activeInside state.stack age [] seed = true :=
 2285      activeInside_iff.mpr (Or.inl seedClass)
 2286    have vertexOutside : activeInside state.stack age [] vertex = false := by
 2287      rw [Bool.eq_false_iff, Ne, activeInside_iff]
 2288      rintro (marked | member)
 2289      · exact inside marked
 2290      · simp at member
 2291    obtain ⟨u, v, uIn, vOut, adjacent⟩ :=
 2292      boundary_edge_of_correct correct (activeInside state.stack age []) seedBound bound
 2293        seedInside vertexOutside
 2294    have uIn' : markClass? state.stack u = some age := by
 2295      rcases activeInside_iff.mp uIn with marked | member
 2296      · exact marked
 2297      · simp at member
 2298    have vOut' : ¬ markClass? state.stack v = some age := by
 2299      intro h
 2300      have := (activeInside_iff (bucket := [])).mpr (Or.inl h)
 2301      rw [vOut] at this
 2302      exact Bool.false_ne_true this
 2303    have ofRegion : ∀ {w : Vertex}, InRegion state.stack age w → markClass? state.stack w = some age := by
 2304      rintro w (marked | ⟨bucket, lookup, member⟩)
 2305      · exact marked
 2306      · rw [bucketEq] at lookup
 2307        cases lookup
 2308        simp at member
 2309    obtain ⟨edge, edgeMember, orientation⟩ := adjacent
 2310    rcases List.mem_append.mp edgeMember with fixed | selected
 2311    · rcases mem_fixedEdges fixed with ⟨l, r, member, rfl⟩ | ⟨l, r, c, member, edgeEq⟩
 2312      · have linked : AxiomLinked certificate u v := by
 2313          rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2314          · exact Or.inl member
 2315          · exact Or.inr member
 2316        exact vOut' (ofRegion (closure.pairsMarked linked uIn'))
 2317      · have premiseCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
 2318            u = premise → v = c → False := by
 2319          intro premise mate linked uEq vEq
 2320          subst uEq; subst vEq
 2321          have mateMarked := closure.tensorTop linked sigmaLast uIn'
 2322          exact vOut' (ofRegion (closure.tensorFired linked uIn' mateMarked).2)
 2323        have conclusionCase : ∀ {premise mate : Vertex}, TensorLinked certificate premise mate c →
 2324            u = c → v = premise → False := by
 2325          intro premise mate linked uEq vEq
 2326          subst uEq; subst vEq
 2327          exact vOut' (closure.down (Or.inl linked) (Or.inl uIn')).1
 2328        rcases edgeEq with rfl | rfl
 2329        · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2330          · exact premiseCase (Or.inl member) rfl rfl
 2331          · exact conclusionCase (Or.inl member) rfl rfl
 2332        · rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2333          · exact premiseCase (Or.inr member) rfl rfl
 2334          · exact conclusionCase (Or.inr member) rfl rfl
 2335    · obtain ⟨l, r, c, member, edgeEq⟩ := mem_cutSelection selected
 2336      have conclusionCase : ∀ {premise mate : Vertex}, ParLinked certificate premise mate c →
 2337          u = c → v = premise → False := by
 2338        intro premise mate linked uEq vEq
 2339        subst uEq; subst vEq
 2340        exact vOut' (closure.down (Or.inr linked) (Or.inl uIn')).1
 2341      unfold cutChoice at edgeEq
 2342      simp only at edgeEq
 2343      split at edgeEq
 2344      · rename_i cond
 2345        rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
 2346        subst edgeEq
 2347        rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2348        · rw [uIn] at cond
 2349          exact Bool.false_ne_true cond.2.symm
 2350        · exact conclusionCase (Or.inr member) rfl rfl
 2351      · split at edgeEq
 2352        · rename_i cond
 2353          rw [Bool.and_eq_true, Bool.not_eq_true'] at cond
 2354          subst edgeEq
 2355          rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2356          · rw [uIn] at cond
 2357            exact Bool.false_ne_true cond.2.symm
 2358          · exact conclusionCase (Or.inl member) rfl rfl
 2359        · rename_i notFirst _
 2360          subst edgeEq
 2361          rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
 2362          · have rIn : activeInside state.stack age [] r = true := by
 2363              cases rIn : activeInside state.stack age [] r
 2364              · exact absurd (by rw [uIn, rIn]; rfl) notFirst
 2365              · rfl
 2366            have rClass : markClass? state.stack r = some age := by
 2367              rcases activeInside_iff.mp rIn with marked | member
 2368              · exact marked
 2369              · simp at member
 2370            exact vOut' (ofRegion (closure.parFired (Or.inl member) uIn' rClass))
 2371          · exact conclusionCase (Or.inl member) rfl rfl
 2372  
```

Steps (line, tactic):

Edges [i, j]:

## 24. `ProofNetIR.Certificate.canonicalWorklistRun_waitingPar_has_dependency`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 20443.

```lean
20441          ∃ target,
20442            QuiescentWaitingParDependency
20443              certificate final source target := by
20444    let final :=
20445      (runUnificationWorklist certificate
20446        certificate.worklistConsumers
20447        (worklistFuel certificate.links.length)
20448        (initializeWorklist certificate started)).state
20449    change
20450      ∀ {source : Vertex},
20451        QuiescentWaitingParAt certificate final source →
20452          ∃ target,
20453            QuiescentWaitingParDependency
20454              certificate final source target
20455    intro source waiting
20456    rcases waiting with
20457      ⟨sourceUnassigned, index, left, right, leftToken, rightToken,
20458        linkLookup, leftMarked, rightMarked, different, registered⟩
20459    have linkMembership :
20460        Link.par left right source ∈ certificate.links :=
20461      List.mem_of_getElem? linkLookup
20462    rcases
20463        correct.parPremises_referencePath_avoids_conclusion linkMembership with
20464      ⟨path, pathStarts, pathFinishes, sourceAvoided⟩
20465    have coreInvariant :
20466        WorklistCoreInvariant certificate final := by
20467      simpa [final] using
20468        canonicalWorklistRun_coreInvariant correct.1 startEquation
20469    let marking :=
20470      final.core.toMarking certificate coreInvariant.1
20471    rcases final.core.tokenAt?_some_witness leftMarked with
20472      ⟨leftRaw, leftRawMarked, leftRepresentative⟩
20473    rcases final.core.tokenAt?_some_witness rightMarked with
20474      ⟨rightRaw, rightRawMarked, rightRepresentative⟩
20475    have abstractLeftMarked :
20476        marking.mark left = some leftRaw := by
20477      simpa [marking] using leftRawMarked
20478    have abstractRightMarked :
20479        marking.mark right = some rightRaw := by
20480      simpa [marking] using rightRawMarked
20481    have exactComponents :
20482        marking.ThreadComponentsExact :=
20483      canonicalWorklistRun_threadComponentsExact
20484        correct.1 startEquation
20485    have notSynchronized :
20486        ¬marking.sameThread leftRaw rightRaw := by
20487      simp only [marking, UnificationState.toMarking_sameThread]
20488      intro representativesEqual
20489      apply different
20490      rw [← leftRepresentative, ← rightRepresentative]
20491      exact representativesEqual
20492    have noActiveWalk :
20493        ¬marking.activeReferenceGraph.Walk left right := by
20494      intro walk
20495      exact notSynchronized
20496        ((exactComponents.walk_iff_sameThread
20497          marking abstractLeftMarked abstractRightMarked).mp walk)
20498    have noActivePath :
20499        ¬marking.activeReferenceGraph.Walk path.start path.finish := by
20500      intro walk
20501      apply noActiveWalk
20502      simpa [pathStarts, pathFinishes] using walk
20503    have pathStartMarked :
20504        (marking.mark path.start).isSome = true := by
20505      simp [pathStarts, abstractLeftMarked]
20506    rcases marking.referencePath_has_first_marked_to_unmarked_boundary
20507        path pathStartMarked noActivePath with
20508      ⟨before, boundary, after, traversalEquation,
20509        prefixAccepted, boundarySourceMarked,
20510        boundaryTargetUnmarked, activePrefix⟩
20511    have boundaryMembership : boundary ∈ path.traversed := by
20512      rw [traversalEquation]
20513      simp
20514    have prefixAssigned :
20515        ∀ candidate ∈ before,
20516          final.core.assignedToken? candidate.source ≠ none ∧
20517            final.core.assignedToken? candidate.target ≠ none := by
20518      intro candidate membership
20519      rcases prefixAccepted candidate membership with
20520        ⟨sourceMarked, targetMarked⟩
20521      constructor
20522      · change
20523          (final.core.assignedToken? candidate.source).isSome = true
20524            at sourceMarked
20525        intro sourceNone
20526        rw [sourceNone] at sourceMarked
20527        contradiction
20528      · change
20529          (final.core.assignedToken? candidate.target).isSome = true
20530            at targetMarked
20531        intro targetNone
20532        rw [targetNone] at targetMarked
20533        contradiction
20534    have firstBoundary :
20535        QuiescentWaitingParFirstBoundary
20536          certificate final path boundary :=
20537      ⟨before, after, traversalEquation, prefixAssigned⟩
20538    have activeFromLeft :
20539        marking.activeReferenceGraph.Walk left boundary.source := by
20540      simpa [pathStarts] using activePrefix
20541    have boundarySourceAssigned :
20542        final.core.assignedToken? boundary.source ≠ none := by
20543      change
20544        (final.core.assignedToken? boundary.source).isSome = true
20545          at boundarySourceMarked
20546      intro sourceNone
20547      rw [sourceNone] at boundarySourceMarked
20548      contradiction
20549    have boundaryTargetUnassigned :
20550        final.core.assignedToken? boundary.target = none := by
20551      change
20552        (final.core.assignedToken? boundary.target).isSome = false
20553          at boundaryTargetUnmarked
20554      cases assigned :
20555          final.core.assignedToken? boundary.target with
20556      | none =>
20557          rfl
20558      | some token =>
20559          simp [assigned] at boundaryTargetUnmarked
20560    rcases final.core.tokenAt?_exists_of_assigned
20561        boundarySourceAssigned with
20562      ⟨boundarySourceToken, boundarySourceLookup⟩
20563    rcases final.core.tokenAt?_some_witness boundarySourceLookup with
20564      ⟨boundarySourceRaw, boundarySourceRawMarked,
20565        boundarySourceRepresentative⟩
20566    have abstractBoundarySourceMarked :
20567        marking.mark boundary.source = some boundarySourceRaw := by
20568      simpa [marking] using boundarySourceRawMarked
20569    have sameThread :
20570        marking.sameThread leftRaw boundarySourceRaw :=
20571      (exactComponents.walk_iff_sameThread
20572        marking abstractLeftMarked abstractBoundarySourceMarked).mp
20573          activeFromLeft
20574    have boundarySourceTokenEquation :
20575        boundarySourceToken = leftToken := by
20576      simp only [marking, UnificationState.toMarking_sameThread]
20577        at sameThread
20578      rw [leftRepresentative, boundarySourceRepresentative] at sameThread
20579      exact sameThread.symm
20580    have boundarySourceTokenLookup :
20581        final.core.tokenAt? boundary.source = some leftToken := by
20582      rw [boundarySourceLookup, boundarySourceTokenEquation]
20583    have boundaryTargetMembership :
20584        boundary.target ∈ path.vertices :=
20585      (path.directed_endpoints_mem_vertices boundaryMembership).2
20586    have boundaryTargetNeSource :
20587        boundary.target ≠ source := by
20588      intro same
20589      exact sourceAvoided (same ▸ boundaryTargetMembership)
20590    have causal :
20591        marking.MarkingCausallyClosed :=
20592      (canonicalWorklistRun_causallyThreaded
20593        correct.1 startEquation).1
20594    have axiomsMarked :
20595        ∀ {axiomIndex axiomLeft axiomRight : Nat},
20596          certificate.links[axiomIndex]? =
20597              some (Link.axiom axiomLeft axiomRight) →
20598            (marking.mark axiomLeft).isSome = true ∧
20599              (marking.mark axiomRight).isSome = true := by
20600      intro axiomIndex axiomLeft axiomRight axiomLookup
20601      have axiomMembership :
20602          Link.axiom axiomLeft axiomRight ∈ certificate.links :=
20603        List.mem_of_getElem? axiomLookup
20604      have assigned :=
20605        canonicalWorklistRun_axiom_endpoints_assigned
20606          correct.1 startEquation axiomMembership
20607      constructor
20608      · change
20609          (final.core.assignedToken? axiomLeft).isSome = true
20610        cases equation :
20611            final.core.assignedToken? axiomLeft with
20612        | none =>
20613            exact False.elim (assigned.1 equation)
20614        | some token =>
20615            rfl
20616      · change
20617          (final.core.assignedToken? axiomRight).isSome = true
20618        cases equation :
20619            final.core.assignedToken? axiomRight with
20620        | none =>
20621            exact False.elim (assigned.2 equation)
20622        | some token =>
20623            rfl
20624    have boundaryExactOrigin :
20625        ExactForwardReferenceConnectiveOccurrence certificate boundary := by
20626      have origin :=
20627        marking.marked_to_unmarked_referenceEdge_exact_connective_origin
20628          causal axiomsMarked boundary boundarySourceMarked
20629          boundaryTargetUnmarked
20630      simpa [ExactForwardReferenceConnectiveOccurrence] using origin
20631    have boundaryOrigin :
20632        ForwardReferenceConnectiveOccurrence certificate boundary :=
20633      boundaryExactOrigin.toForward
20634    have boundaryStatus :
20635        PathFrontierSchedulerObstruction certificate final boundary :=
20636      canonicalWorklistRun_forwardFrontier_status
20637        correct startEquation boundarySourceAssigned
20638        boundaryTargetUnassigned boundaryOrigin
20639    rcases canonicalWorklistRun_pathFrontier_reaches_waitingPar_with_path
20640        correct startEquation boundaryTargetUnassigned boundaryStatus with
20641      ⟨target, targetWaiting, formulaPath⟩
20642    have targetRank :
20643        certificate.formulaComplexityAt target ≤
20644          certificate.formulaComplexityAt boundary.target :=
20645      formulaPath.toFormulaPremiseReachable.complexity_le
20646    exact
20647      ⟨target, index, left, right, leftToken, rightToken, path, boundary,
```

Steps (line, tactic):

Edges [i, j]:

## 25. `ProofNetIR.SequentialSchedulerBridge.InitialReservationStep.readyBucketFrontierExact`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerInvariant.lean`, from line 678.

```lean
  676      {start : Vertex}
  677      (step : InitialReservationStep certificate after start) :
  678      ReadyBucketFrontierExact after := by
  679    have route := step.route
  680    rcases certificate.reserveAxiomAt?_exact step.core_eq with
  681      ⟨left, right, component, exactLink, ready, componentLookup,
  682        frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  683    have submitted :
  684        Link.axiom left right =
  685          .axiom step.result.left step.result.right :=
  686      Option.some.inj (exactLink.symm.trans step.result.exactLink)
  687    injection submitted with leftEq rightEq
  688    subst left
  689    subst right
  690    have stackExact :=
  691      SequentialStackState.initEnqueue?_exact step.stack_eq
  692    rw [step.output_eq]
  693    unfold ReadyBucketFrontierExact
  694    intro position boundary bucket sigmaLookup readyLookup
  695    rw [stackExact.2.2.1] at sigmaLookup
  696    rw [stackExact.2.2.2.1] at readyLookup
  697    have positionBound : position < 1 := by
  698      simpa using (List.getElem?_eq_some_iff.mp sigmaLookup).1
  699    have positionZero : position = 0 := by omega
  700    subst position
  701    simp at sigmaLookup readyLookup
  702    subst boundary
  703    subst bucket
  704    refine ⟨component, ?_, ?_⟩
  705    · change step.coreAfter.components[0]? = some (some component)
  706      rw [componentsEq]
  707      simp [ReservationState.empty,
  708        Certificate.initialUnificationState]
  709    · intro vertex
  710      have endpoints :
  711          (step.reached = step.result.left ∧
  712            step.partner = step.result.right) ∨
  713          (step.reached = step.result.right ∧
  714            step.partner = step.result.left) :=
  715        route.storedEndpoints
  716      rcases endpoints with
  717        ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
  718      · rw [reachedEq, partnerEq, frontier]
  719        constructor
  720        · intro membership
  721          have submittedMembership :
  722              vertex = step.result.left ∨
  723                vertex = step.result.right := by
  724            simpa using membership
  725          have markReady :
  726              step.coreAfter.marks[vertex]? = some none := by
  727            rw [marksEq]
  728            rcases submittedMembership with rfl | rfl
  729            · exact step.result.leftReady
  730            · exact step.result.rightReady
  731          exact ⟨membership, markReady⟩
  732        · exact fun result => result.1
  733      · rw [reachedEq, partnerEq, frontier]
  734        constructor
  735        · intro membership
  736          have submittedMembership :
  737              vertex = step.result.left ∨
  738                vertex = step.result.right := by
  739            simpa [or_comm] using membership
  740          have markReady :
  741              step.coreAfter.marks[vertex]? = some none := by
  742            rw [marksEq]
  743            rcases submittedMembership with rfl | rfl
  744            · exact step.result.leftReady
  745            · exact step.result.rightReady
  746          exact ⟨by simpa [or_comm] using membership, markReady⟩
  747        · intro result
  748          simpa [or_comm] using result.1
  749  
```

Steps (line, tactic):

Edges [i, j]:

## 26. `ProofNetIR.SequentialFigure7.unifyOne?_some_iff`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyOne.lean`, from line 745.

```lean
  743      (invariant : ReservationInvariant certificate before) :
  744      unifyOne? certificate before invariant = some after ↔
  745        Nonempty (UnifyOneStep certificate before after) := by
  746    constructor
  747    · intro equation
  748      unfold unifyOne? at equation
  749      cases prepareEquation : prepare? before with
  750      | none => simp [prepareEquation] at equation
  751      | some prepared =>
  752          cases consumerEquation :
  753              certificate.tensorBelow? prepared.stackResult.vertex with
  754          | none => simp [prepareEquation, consumerEquation] at equation
  755          | some consumer =>
  756              cases mateEquation :
  757                    prepared.coreMarked.marks[consumer.mate]? with
  758                | none =>
  759                    simp [prepareEquation, consumerEquation,
  760                      mateEquation] at equation
  761                | some mark =>
  762                    cases mark with
  763                    | none =>
  764                        simp [prepareEquation, consumerEquation,
  765                          mateEquation] at equation
  766                    | some mateRawAge =>
  767                        cases previousEquation :
  768                            prepared.stackResult.after.sigma.dropLast.getLast? with
  769                        | none =>
  770                            simp [prepareEquation, consumerEquation,
  771                              mateEquation,
  772                              previousEquation] at equation
  773                        | some previousBoundary =>
  774                            by_cases lowerEquation :
  775                                previousBoundary ≤ mateRawAge
  776                            · by_cases upperEquation :
  777                                  mateRawAge < prepared.stackResult.rawAge
  778                              · cases waitingEquation :
  779                                    prepared.stackResult.after.waiting[
  780                                      previousBoundary]? with
  781                                | none =>
  782                                    simp [prepareEquation, consumerEquation,
  783                                      mateEquation,
  784                                      previousEquation, lowerEquation,
  785                                      upperEquation, waitingEquation] at equation
  786                                | some cell =>
  787                                    cases cell with
  788                                    | undefined =>
  789                                        simp [prepareEquation, consumerEquation,
  790                                          mateEquation,
  791                                          previousEquation, lowerEquation,
  792                                          upperEquation, waitingEquation]
  793                                          at equation
  794                                    | initialized payload =>
  795                                        cases payload with
  796                                        | nil =>
  797                                            simp [prepareEquation,
  798                                              consumerEquation,
  799                                              mateEquation, previousEquation,
  800                                              lowerEquation, upperEquation,
  801                                              waitingEquation] at equation
  802                                        | cons waitingConclusion tail =>
  803                                            cases tail with
  804                                            | cons second rest =>
  805                                                simp [prepareEquation,
  806                                                  consumerEquation,
  807                                                  mateEquation,
  808                                                  previousEquation,
  809                                                  lowerEquation, upperEquation,
  810                                                  waitingEquation] at equation
  811                                            | nil =>
  812                                                cases tensorQueueEquation :
  813                                                    Certificate.queueTensor?
  814                                                      prepared.coreMarked
  815                                                      consumer.storedLeft
  816                                                      consumer.storedRight
  817                                                      consumer.conclusion with
  818                                                | none =>
  819                                                    simp [prepareEquation,
  820                                                      consumerEquation,
  821                                                      mateEquation,
  822                                                      previousEquation,
  823                                                      lowerEquation,
  824                                                      upperEquation,
  825                                                      waitingEquation,
  826                                                      tensorQueueEquation]
  827                                                      at equation
  828                                                | some coreTensor =>
  829                                                    cases activationEquation :
  830                                                        activateWaitingPar?
  831                                                          certificate coreTensor
  832                                                          waitingConclusion with
  833                                                    | none =>
  834                                                        simp [prepareEquation,
  835                                                          consumerEquation,
  836                                                          mateEquation,
  837                                                          previousEquation,
  838                                                          lowerEquation,
  839                                                          upperEquation,
  840                                                          waitingEquation,
  841                                                          tensorQueueEquation,
  842                                                          activationEquation]
  843                                                          at equation
  844                                                    | some coreAfter =>
  845                                                        cases stackEquation :
  846                                                            prepared.stackResult.after
  847                                                              |>.mergeTopReadyWaiting?
  848                                                                previousBoundary
  849                                                                consumer.conclusion with
  850                                                        | none =>
  851                                                            simp [prepareEquation,
  852                                                              consumerEquation,
  853                                                              mateEquation,
  854                                                              previousEquation,
  855                                                              lowerEquation,
  856                                                              upperEquation,
  857                                                              waitingEquation,
  858                                                              tensorQueueEquation,
  859                                                              activationEquation,
  860                                                              stackEquation]
  861                                                              at equation
  862                                                        | some stackAfter =>
  863                                                            cases mergedEquation :
  864                                                                stackAfter.ready.getLast? with
  865                                                            | none =>
  866                                                                simp [prepareEquation,
  867                                                                  consumerEquation,
  868                                                                  mateEquation,
  869                                                                  previousEquation,
  870                                                                  lowerEquation,
  871                                                                  upperEquation,
  872                                                                  waitingEquation,
  873                                                                  tensorQueueEquation,
  874                                                                  activationEquation,
  875                                                                  stackEquation,
  876                                                                  mergedEquation]
  877                                                                  at equation
  878                                                            | some merged =>
  879                                                                by_cases readyNodupEquation :
  880                                                                    merged.Nodup
  881                                                                · simp [prepareEquation,
  882                                                                      consumerEquation,
  883                                                                      mateEquation,
  884                                                                      previousEquation,
  885                                                                      lowerEquation,
  886                                                                      upperEquation,
  887                                                                      waitingEquation,
  888                                                                      tensorQueueEquation,
  889                                                                      activationEquation,
  890                                                                      stackEquation,
  891                                                                      mergedEquation,
  892                                                                      readyNodupEquation]
  893                                                                      at equation
  894                                                                  subst after
  895                                                                  rcases
  896                                                                      Certificate.queueTensor?_some_iff.mp
  897                                                                        tensorQueueEquation with
  898                                                                    ⟨tensorStep⟩
  899                                                                  rcases
  900                                                                      activateWaitingPar?_some_iff.mp
  901                                                                        activationEquation with
  902                                                                    ⟨activationStep⟩
  903                                                                  rcases
  904                                                                      SequentialStackState.mergeTopReadyWaiting?_some_iff.mp
  905                                                                        stackEquation with
  906                                                                    ⟨mergeStep⟩
  907                                                                  have activeBoundaryEquation :
  908                                                                      mergeStep.activeBoundary =
  909                                                                        prepared.stackResult.rawAge := by
  910                                                                    have mergeTop :
  911                                                                        prepared.stackResult.after.sigma.getLast? =
  912                                                                          some mergeStep.activeBoundary := by
  913                                                                      rw [mergeStep.sigma_eq]
  914                                                                      simp
  915                                                                    have preparedTop :
  916                                                                        prepared.stackResult.after.sigma.getLast? =
  917                                                                          some prepared.stackResult.rawAge := by
  918                                                                      rcases
  919                                                                          SequentialStackState.popReadyMark?_exact
  920                                                                            prepared.stack_eq with
  921                                                                        ⟨_, sigmaTop, _, _, _, sigmaAfter,
  922                                                                          _, _, _⟩
  923                                                                      rw [sigmaAfter]
  924                                                                      exact sigmaTop
  925                                                                    exact Option.some.inj
  926                                                                      (mergeTop.symm.trans preparedTop)
  927                                                                  have exactSigma :
  928                                                                      prepared.stackResult.after.sigma =
  929                                                                        mergeStep.sigmaPrefix ++
  930                                                                          [previousBoundary,
  931                                                                            prepared.stackResult.rawAge] := by
  932                                                                    simpa [activeBoundaryEquation] using
  933                                                                      mergeStep.sigma_eq
  934                                                                  have tokenOrientation :=
  935                                                                    unifyOne_tensor_tokens_eq_adjacent
  936                                                                      invariant prepared consumer
  937                                                                      consumerEquation
  938                                                                      mateRawAge previousBoundary
  939                                                                      mergeStep.sigmaPrefix exactSigma
  940                                                                      mateEquation lowerEquation
  941                                                                      upperEquation tensorStep
  942                                                                  exact ⟨{
  943                                                                    before_invariant := invariant
  944                                                                    prepared
  945                                                                    consumer
  946                                                                    mateRawAge
  947                                                                    previousBoundary
  948                                                                    waitingConclusion
  949                                                                    coreTensor
  950                                                                    coreAfter
  951                                                                    stackAfter
  952                                                                    merged
  953                                                                    tensorStep
  954                                                                    activationStep
  955                                                                    mergeStep
  956                                                                    prepare_eq := prepareEquation
  957                                                                    consumer_eq := consumerEquation
  958                                                                    mate_marked := mateEquation
  959                                                                    lower := lowerEquation
  960                                                                    upper := upperEquation
  961                                                                    waiting_one := waitingEquation
  962                                                                    tensor_queue_eq := tensorQueueEquation
  963                                                                    activation_eq := activationEquation
  964                                                                    stack_merge_eq := stackEquation
  965                                                                    merged_eq := mergedEquation
  966                                                                    ready_nodup := readyNodupEquation
  967                                                                    tokens_eq_adjacent := tokenOrientation
  968                                                                    output_eq := rfl }⟩
  969                                                                · simp [prepareEquation,
  970                                                                    consumerEquation,
  971                                                                    mateEquation,
  972                                                                    previousEquation,
  973                                                                    lowerEquation,
  974                                                                    upperEquation,
  975                                                                    waitingEquation,
  976                                                                    tensorQueueEquation,
  977                                                                    activationEquation,
  978                                                                    stackEquation,
  979                                                                    mergedEquation,
  980                                                                    readyNodupEquation]
  981                                                                    at equation
  982                              · simp [prepareEquation, consumerEquation,
  983                                  mateEquation,
  984                                  previousEquation, lowerEquation,
  985                                  upperEquation] at equation
  986                            · simp [prepareEquation, consumerEquation,
  987                                mateEquation,
  988                                previousEquation, lowerEquation] at equation
  989    · rintro ⟨step⟩
  990      rcases step with
  991        ⟨stepInvariant, prepared, consumer, mateRawAge,
  992          previousBoundary, waitingConclusion, coreTensor, coreAfter,
  993          stackAfter, merged, tensorStep, activationStep, mergeStep,
  994          prepareEquation, consumerEquation,
  995          mateEquation, lowerEquation, upperEquation, waitingEquation,
  996          tensorQueueEquation, activationEquation, stackEquation,
  997          mergedEquation, readyNodupEquation, tokenOrientation,
  998          outputEquation⟩
  999      subst after
 1000      have previousEquation :
 1001          prepared.stackResult.after.sigma.dropLast.getLast? =
 1002            some previousBoundary := by
 1003        rw [mergeStep.sigma_eq]
 1004        simp
 1005      simp [unifyOne?, prepareEquation, consumerEquation,
 1006        mateEquation, previousEquation,
```

Steps (line, tactic):

Edges [i, j]:

## 27. `ProofNetIR.Certificate.sameThread_tensorDeadlock_false`

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 13737.

```lean
13735      (leftLookup : state.tokenAt? left = some token)
13736      (rightLookup : state.tokenAt? right = some token) :
13737      False := by
13738    have wellFormed :
13739        certificate.LinkWellFormed
13740          (.tensor left right conclusion) :=
13741      correct.1.2.2.2.2.1 _ membership
13742    rcases state.tokenAt?_some_witness leftLookup with
13743      ⟨leftRaw, leftMarked, leftRepresentative⟩
13744    rcases state.tokenAt?_some_witness rightLookup with
13745      ⟨rightRaw, rightMarked, rightRepresentative⟩
13746    have sameThread :
13747        (state.toMarking certificate abstractable).sameThread
13748          leftRaw rightRaw := by
13749      simp only [UnificationState.toMarking_sameThread]
13750      exact leftRepresentative.trans rightRepresentative.symm
13751    have abstractLeftMarked :
13752        (state.toMarking certificate abstractable).mark left =
13753          some leftRaw := by
13754      simpa only [UnificationState.toMarking_mark] using leftMarked
13755    have abstractRightMarked :
13756        (state.toMarking certificate abstractable).mark right =
13757          some rightRaw := by
13758      simpa only [UnificationState.toMarking_mark] using rightMarked
13759    have activeWalk :
13760        (state.toMarking certificate abstractable).activeReferenceGraph.Walk
13761          left right :=
13762      connected abstractLeftMarked abstractRightMarked sameThread
13763    rcases activeWalk.toSimple with ⟨steps, visited, simple⟩
13764    rcases simple.liftToEdgeSimplePathWithEdges
13765        ((state.toMarking certificate abstractable)
13766          |>.activeReferenceEdges_subset_referenceSwitchingGraph) with
13767      ⟨threadPath, threadStarts, threadFinishes, _threadVertices,
13768        threadEdgesActive⟩
13769    have threadStartFinishDifferent :
13770        threadPath.start ≠ threadPath.finish := by
13771      rw [threadStarts, threadFinishes]
13772      exact wellFormed.1
13773    have threadNonempty : threadPath.traversed ≠ [] := by
13774      intro empty
13775      have finishMembership :=
13776        threadPath.walk.finish_mem_visitedVertices
13777      have sameEndpoints : threadPath.finish = threadPath.start := by
13778        simpa [Graph.EdgeWalk.visitedVertices, empty] using finishMembership
13779      exact threadStartFinishDifferent sameEndpoints.symm
13780    have abstractConclusionUnmarked :
13781        (state.toMarking certificate abstractable).mark conclusion = none := by
13782      simpa only [UnificationState.toMarking_mark] using conclusionUnmarked
13783    have noActiveIncident :
13784        ∀ edge,
13785          edge ∈
13786              (state.toMarking certificate abstractable).activeReferenceEdges →
13787            (edge.first = conclusion ∨ edge.second = conclusion) →
13788              False := by
13789      intro edge edgeActive incident
13790      have endpoints := (List.mem_filter.mp edgeActive).2
13791      simp only [Bool.and_eq_true] at endpoints
13792      rcases incident with firstConclusion | secondConclusion
13793      · have markedConclusion :
13794            Option.isSome
13795              ((state.toMarking certificate abstractable).mark conclusion) =
13796                true := by
13797          simpa [firstConclusion] using endpoints.1
13798        rw [abstractConclusionUnmarked] at markedConclusion
13799        simp at markedConclusion
13800      · have markedConclusion :
13801            Option.isSome
13802              ((state.toMarking certificate abstractable).mark conclusion) =
13803                true := by
13804          simpa [secondConclusion] using endpoints.2
13805        rw [abstractConclusionUnmarked] at markedConclusion
13806        simp at markedConclusion
13807    have conclusionNotInThreadPath :
13808        conclusion ∉ threadPath.vertices := by
13809      intro conclusionMembership
13810      change conclusion ∈
13811        Graph.EdgeWalk.visitedVertices threadPath.start
13812          threadPath.traversed at conclusionMembership
13813      simp only [Graph.EdgeWalk.visitedVertices, List.mem_cons] at conclusionMembership
13814      rcases conclusionMembership with startConclusion | targetMembership
13815      · apply wellFormed.2.1
13816        rw [← threadStarts]
13817        exact startConclusion.symm
13818      · rcases List.mem_map.mp targetMembership with
13819          ⟨directed, directedMembership, targetConclusion⟩
13820        have edgeActive := threadEdgesActive directed directedMembership
13821        apply noActiveIncident directed.edge edgeActive
13822        cases forward : directed.forward with
13823        | false =>
13824            exact Or.inl (by
13825              simpa [Graph.DirectedEdge.target, forward] using
13826                targetConclusion)
13827        | true =>
13828            exact Or.inr (by
13829              simpa [Graph.DirectedEdge.target, forward] using
13830                targetConclusion)
13831    have referenceTensorEdges :=
13832      UnificationMarking.referenceSwitchingGraph_tensorEdges
13833        certificate membership
13834    let leftEdge : Edge := { first := left, second := conclusion }
13835    let rightEdge : Edge := { first := right, second := conclusion }
13836    have leftEdgeMembership :
13837        leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
13838      simpa [leftEdge] using referenceTensorEdges.1
13839    have rightEdgeMembership :
13840        rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
13841      simpa [rightEdge] using referenceTensorEdges.2
13842    rcases List.getElem?_of_mem leftEdgeMembership with
13843      ⟨leftIndex, leftEdgeLookup⟩
13844    rcases List.getElem?_of_mem rightEdgeMembership with
13845      ⟨rightIndex, rightEdgeLookup⟩
13846    let rightDirected :
13847        certificate.referenceSwitchingGraph.DirectedEdge := {
13848      index := rightIndex
13849      edge := rightEdge
13850      lookup := rightEdgeLookup
13851      forward := true }
13852    let leftDirected :
13853        certificate.referenceSwitchingGraph.DirectedEdge := {
13854      index := leftIndex
13855      edge := leftEdge
13856      lookup := leftEdgeLookup
13857      forward := false }
13858    have tensorIndicesDifferent : rightIndex ≠ leftIndex := by
13859      intro sameIndex
13860      have sameEdges : rightEdge = leftEdge := by
13861        apply Option.some.inj
13862        rw [← rightEdgeLookup, ← leftEdgeLookup, sameIndex]
13863      apply wellFormed.1
13864      have sameFirst := congrArg Edge.first sameEdges
13865      simpa [rightEdge, leftEdge] using sameFirst.symm
13866    let returnPath : certificate.referenceSwitchingGraph.EdgeSimplePath := {
13867      start := right
13868      finish := left
13869      traversed := [rightDirected, leftDirected]
13870      walk := by
13871        simpa [rightDirected, leftDirected, rightEdge, leftEdge,
13872          Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
13873          Graph.EdgeWalk.step
13874            (Graph.EdgeWalk.step
13875              (Graph.EdgeWalk.refl
13876                (graph := certificate.referenceSwitchingGraph) right)
13877              rightDirected rfl rfl)
13878            leftDirected rfl rfl
13879      verticesNodup := by
13880        simp [Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
13881          rightEdge, leftEdge, Graph.DirectedEdge.target,
13882          wellFormed.2.2.1]
13883        exact
13884          ⟨fun same => wellFormed.1 same.symm,
13885            fun same => wellFormed.2.1 same.symm⟩ }
13886    have returnNonempty : returnPath.traversed ≠ [] := by
13887      simp [returnPath]
13888    have meeting : threadPath.finish = returnPath.start := by
13889      simpa [returnPath] using threadFinishes
13890    have closing : returnPath.finish = threadPath.start := by
13891      simpa [returnPath] using threadStarts.symm
13892    have vertexDisjoint :
13893        ∀ vertex,
13894          vertex ∈ threadPath.vertices →
13895            vertex ∈ returnPath.vertices.tail.dropLast →
13896              False := by
13897      intro vertex threadMembership returnMembership
13898      have vertexConclusion : vertex = conclusion := by
13899        simpa [returnPath, Graph.EdgeSimplePath.vertices,
13900          Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
13901          rightEdge, leftEdge, Graph.DirectedEdge.target] using
13902            returnMembership
13903      subst vertex
13904      exact conclusionNotInThreadPath threadMembership
13905    have leftEdgeNotActive :
13906        leftEdge ∉
13907          (state.toMarking certificate abstractable).activeReferenceEdges := by
13908      intro active
13909      exact noActiveIncident leftEdge active (by
13910        exact Or.inr rfl)
13911    have rightEdgeNotActive :
13912        rightEdge ∉
13913          (state.toMarking certificate abstractable).activeReferenceEdges := by
13914      intro active
13915      exact noActiveIncident rightEdge active (by
13916        exact Or.inr rfl)
13917    have edgeDisjoint :
13918        ∀ index,
13919          index ∈ threadPath.traversed.map Graph.DirectedEdge.index →
13920            index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
13921              False := by
13922      intro index threadIndex returnIndex
13923      rcases List.mem_map.mp threadIndex with
13924        ⟨directed, directedMembership, directedIndex⟩
13925      have edgeActive := threadEdgesActive directed directedMembership
13926      change directed.edge ∈
13927        (state.toMarking certificate abstractable).activeReferenceEdges
13928          at edgeActive
13929      have returnCases : index = rightIndex ∨ index = leftIndex := by
13930        simpa [returnPath, rightDirected, leftDirected] using returnIndex
13931      rcases returnCases with rightCase | leftCase
13932      · have sameIndex : directed.index = rightIndex :=
13933          directedIndex.trans rightCase
13934        have sameEdge : directed.edge = rightEdge := by
13935          apply Option.some.inj
13936          rw [← directed.lookup, ← rightEdgeLookup, sameIndex]
13937        rw [sameEdge] at edgeActive
13938        exact rightEdgeNotActive edgeActive
13939      · have sameIndex : directed.index = leftIndex :=
13940          directedIndex.trans leftCase
13941        have sameEdge : directed.edge = leftEdge := by
13942          apply Option.some.inj
13943          rw [← directed.lookup, ← leftEdgeLookup, sameIndex]
13944        rw [sameEdge] at edgeActive
13945        exact leftEdgeNotActive edgeActive
13946    let cycle : certificate.referenceSwitchingGraph.EdgeSimpleCycle :=
13947      Graph.EdgeSimpleCycle.ofTwoPaths
13948        threadPath returnPath threadNonempty returnNonempty
13949        meeting closing vertexDisjoint edgeDisjoint
13950    have compact :=
13951      certificate.declarativelyCorrect_iff_structural_cuspAcyclic_referenceConnected
13952        |>.mp correct
13953    have referenceAcyclic :
13954        certificate.referenceSwitchingGraph.Acyclic := by
13955      simpa [Certificate.referenceSwitchingGraph] using
13956        compact.2.1.occurrenceSwitching_acyclic
13957          compact.1 certificate.referenceFullSwitchingSelection
13958    exact referenceAcyclic cycle
13959  
```

Steps (line, tactic):

Edges [i, j]:

## 28. `ProofNetIR.SequentialFigure7.referenceAcyclic_no_tensorBypass`

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7TerminalPartnerGeometry.lean`, from line 380.

```lean
  378      (pathFinishes : path.finish = right)
  379      (conclusionNotInPath : conclusion ∉ path.vertices) :
  380      False := by
  381    have wellFormed :
  382        certificate.LinkWellFormed (.tensor left right conclusion) :=
  383      structural.2.2.2.2.1 _ membership
  384    have pathNonempty : path.traversed ≠ [] := by
  385      intro empty
  386      have finishMembership := path.walk.finish_mem_visitedVertices
  387      have sameEndpoints : path.finish = path.start := by
  388        simpa [Graph.EdgeWalk.visitedVertices, empty] using finishMembership
  389      rw [pathStarts, pathFinishes] at sameEndpoints
  390      exact wellFormed.1 sameEndpoints.symm
  391    have referenceTensorEdges :=
  392      UnificationMarking.referenceSwitchingGraph_tensorEdges
  393        certificate membership
  394    let leftEdge : Edge := { first := left, second := conclusion }
  395    let rightEdge : Edge := { first := right, second := conclusion }
  396    have leftEdgeMembership :
  397        leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
  398      simpa [leftEdge] using referenceTensorEdges.1
  399    have rightEdgeMembership :
  400        rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
  401      simpa [rightEdge] using referenceTensorEdges.2
  402    rcases List.getElem?_of_mem leftEdgeMembership with
  403      ⟨leftIndex, leftEdgeLookup⟩
  404    rcases List.getElem?_of_mem rightEdgeMembership with
  405      ⟨rightIndex, rightEdgeLookup⟩
  406    let rightDirected :
  407        certificate.referenceSwitchingGraph.DirectedEdge := {
  408      index := rightIndex
  409      edge := rightEdge
  410      lookup := rightEdgeLookup
  411      forward := true }
  412    let leftDirected :
  413        certificate.referenceSwitchingGraph.DirectedEdge := {
  414      index := leftIndex
  415      edge := leftEdge
  416      lookup := leftEdgeLookup
  417      forward := false }
  418    have tensorIndicesDifferent : rightIndex ≠ leftIndex := by
  419      intro sameIndex
  420      have sameEdges : rightEdge = leftEdge := by
  421        apply Option.some.inj
  422        rw [← rightEdgeLookup, ← leftEdgeLookup, sameIndex]
  423      apply wellFormed.1
  424      have sameFirst := congrArg Edge.first sameEdges
  425      simpa [rightEdge, leftEdge] using sameFirst.symm
  426    let returnPath : certificate.referenceSwitchingGraph.EdgeSimplePath := {
  427      start := right
  428      finish := left
  429      traversed := [rightDirected, leftDirected]
  430      walk := by
  431        simpa [rightDirected, leftDirected, rightEdge, leftEdge,
  432          Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
  433          Graph.EdgeWalk.step
  434            (Graph.EdgeWalk.step
  435              (Graph.EdgeWalk.refl
  436                (graph := certificate.referenceSwitchingGraph) right)
  437              rightDirected rfl rfl)
  438            leftDirected rfl rfl
  439      verticesNodup := by
  440        simp [Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
  441          rightEdge, leftEdge, Graph.DirectedEdge.target,
  442          wellFormed.2.2.1]
  443        exact
  444          ⟨fun same => wellFormed.1 same.symm,
  445            fun same => wellFormed.2.1 same.symm⟩ }
  446    have returnNonempty : returnPath.traversed ≠ [] := by
  447      simp [returnPath]
  448    have meeting : path.finish = returnPath.start := by
  449      simpa [returnPath] using pathFinishes
  450    have closing : returnPath.finish = path.start := by
  451      simpa [returnPath] using pathStarts.symm
  452    have vertexDisjoint :
  453        ∀ vertex,
  454          vertex ∈ path.vertices →
  455            vertex ∈ returnPath.vertices.tail.dropLast → False := by
  456      intro vertex pathMembership returnMembership
  457      have vertexConclusion : vertex = conclusion := by
  458        simpa [returnPath, Graph.EdgeSimplePath.vertices,
  459          Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
  460          rightEdge, leftEdge, Graph.DirectedEdge.target] using
  461            returnMembership
  462      subst vertex
  463      exact conclusionNotInPath pathMembership
  464    have edgeDisjoint :
  465        ∀ index,
  466          index ∈ path.traversed.map Graph.DirectedEdge.index →
  467            index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
  468              False := by
  469      intro index pathIndex returnIndex
  470      rcases List.mem_map.mp pathIndex with
  471        ⟨directed, directedMembership, directedIndex⟩
  472      have endpoints :=
  473        path.directed_endpoints_mem_vertices directedMembership
  474      have returnCases : index = rightIndex ∨ index = leftIndex := by
  475        simpa [returnPath, rightDirected, leftDirected] using returnIndex
  476      rcases returnCases with rightCase | leftCase
  477      · have sameIndex : directed.index = rightIndex :=
  478          directedIndex.trans rightCase
  479        have sameEdge : directed.edge = rightEdge := by
  480          apply Option.some.inj
  481          rw [← directed.lookup, ← rightEdgeLookup, sameIndex]
  482        cases forward : directed.forward with
  483        | false =>
  484            have sourceConclusion :
  485                directed.source = conclusion := by
  486              simp [Graph.DirectedEdge.source, forward, sameEdge, rightEdge]
  487            rw [sourceConclusion] at endpoints
  488            exact conclusionNotInPath endpoints.1
  489        | true =>
  490            have targetConclusion :
  491                directed.target = conclusion := by
  492              simp [Graph.DirectedEdge.target, forward, sameEdge, rightEdge]
  493            rw [targetConclusion] at endpoints
  494            exact conclusionNotInPath endpoints.2
  495      · have sameIndex : directed.index = leftIndex :=
  496          directedIndex.trans leftCase
  497        have sameEdge : directed.edge = leftEdge := by
  498          apply Option.some.inj
  499          rw [← directed.lookup, ← leftEdgeLookup, sameIndex]
  500        cases forward : directed.forward with
  501        | false =>
  502            have sourceConclusion :
  503                directed.source = conclusion := by
  504              simp [Graph.DirectedEdge.source, forward, sameEdge, leftEdge]
  505            rw [sourceConclusion] at endpoints
  506            exact conclusionNotInPath endpoints.1
  507        | true =>
  508            have targetConclusion :
  509                directed.target = conclusion := by
  510              simp [Graph.DirectedEdge.target, forward, sameEdge, leftEdge]
  511            rw [targetConclusion] at endpoints
  512            exact conclusionNotInPath endpoints.2
  513    let cycle : certificate.referenceSwitchingGraph.EdgeSimpleCycle :=
  514      Graph.EdgeSimpleCycle.ofTwoPaths
  515        path returnPath pathNonempty returnNonempty
  516        meeting closing vertexDisjoint edgeDisjoint
  517    exact acyclic cycle
  518  
```

Steps (line, tactic):

Edges [i, j]:

