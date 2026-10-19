# Worksheet / 题目清单

P01 to P12: reconstruct the whole proof. W1 to W3: reconstruct the window's lines; earlier lines are
printed for context. Line numbers are those of the file.

P01 至 P12：重建整个证明。W1 至 W3：只重建窗口所含的行；前面的行印出来供参考。行号即文件中的行号。

## P01. `ProofNetIR.Certificate.SchedulerTaggedProvenance.strictInteriorEndpointWitness`

- Module / 模块: `ProofNetIR.Unification`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`
- Reconstruct / 重建: the whole proof, from line 35822 / 整个证明，从第 35822 行开始

```lean
35820      (interior : occurrence.offset ≠ 0) :
35821      SchedulerStrictInteriorEndpointWitness
35822        certificate chainAt count segments tagged occurrence := by
35823    rcases provenance occurrence membership with
35824      ⟨segment, stepBound, segmentLookup, offsetLookup, classified⟩
35825    rcases
35826        classified.1.strictOffset_endpoint
35827          offsetLookup interior with
35828      ⟨head, suffix, segmentShape, occurrenceInSuffix,
35829        headSource, headBackward, headOmitted,
35830        suffixKept, suffixWalk⟩
35831    have headLookup : segment[0]? = some head := by
35832      rw [segmentShape]
35833      simp
35834    have headInFamily :
35835        ({ step := occurrence.step
35836           offset := 0
35837           value := head } :
35838            SchedulerOccurrence
35839              certificate.fullGraph.DirectedEdge) ∈
35840          tagSchedulerFamily segments :=
35841      tagSchedulerFamily_mem_of_getElem? segmentLookup headLookup
35842    have headMissing :
35843        ({ step := occurrence.step
35844           offset := 0
35845           value := head } :
35846            SchedulerOccurrence
35847              certificate.fullGraph.DirectedEdge) ∉ tagged := by
35848      intro headMembership
35849      exact headFree _ headMembership rfl
35850    have targetLeftAvoidance :
35851        ∃ targetBefore targetAfter targetLeft targetRight,
35852          certificate.links =
35853              targetBefore ++
35854                .par targetLeft targetRight
35855                  (chainAt (occurrence.step + 1)) :: targetAfter ∧
35856            ∀ directed ∈ head :: suffix,
35857              directed.index ≠
35858                (linkFullEdges targetBefore).length := by
35859      rcases classified.2 with
35860        ⟨targetBefore, targetAfter, targetLeft, targetRight,
35861          targetLinksEquation, avoidsTargetLeft⟩
35862      exact
35863        ⟨targetBefore, targetAfter, targetLeft, targetRight,
35864          targetLinksEquation, by
35865            intro directed directedMembership
35866            apply avoidsTargetLeft directed
35867            rw [segmentShape]
35868            exact directedMembership⟩
35869    exact
35870      ⟨membership, interior, stepBound, head, suffix,
35871        by simpa [segmentShape] using segmentLookup,
35872        occurrenceInSuffix, headSource, headBackward, headOmitted,
```

## P02. `ProofNetIR.Certificate.runUnificationWorklist_attempts_eq_fuel_of_queue_ne_nil`

- Module / 模块: `ProofNetIR.Unification`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`
- Reconstruct / 重建: the whole proof, from line 13022 / 整个证明，从第 13022 行开始

```lean
13020          state).state.queue ≠ []) :
13021      (runUnificationWorklist certificate consumers fuel
13022        state).linkAttempts = fuel := by
13023    induction fuel generalizing state with
13024    | zero =>
13025        simp [runUnificationWorklist]
13026    | succ fuel induction =>
13027        cases popEquation : popWorklist? state with
13028        | none =>
13029            have queueEmpty : state.queue = [] := by
13030              cases queueEquation : state.queue with
13031              | nil =>
13032                  rfl
13033              | cons head rest =>
13034                  simp [popWorklist?, queueEquation] at popEquation
13035            simp [runUnificationWorklist, popEquation,
13036              queueEmpty] at nonempty
13037        | some result =>
13038            rcases result with ⟨index, popped⟩
13039            let processed :=
13040              processWorklistLink certificate consumers index popped
13041            have tailNonempty :
13042                (runUnificationWorklist certificate consumers fuel
13043                  processed).state.queue ≠ [] := by
13044              simpa [runUnificationWorklist, popEquation,
13045                processed] using nonempty
13046            have tailExact :=
13047              induction (state := processed) tailNonempty
13048            simp [runUnificationWorklist, popEquation,
13049              processed, tailExact]
```

## P03. `Polynomial.eq_mul_mul_of_roots_quadratic_eq_pair`

- Module / 模块: `Mathlib.RingTheory.Polynomial.SmallDegreeVieta`
- File / 文件: `.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/SmallDegreeVieta.lean`
- Reconstruct / 重建: the whole proof, from line 44 / 整个证明，从第 44 行开始

```lean
   42  lemma eq_mul_mul_of_roots_quadratic_eq_pair [CommRing R] [IsDomain R] {a b c x1 x2 : R}
   43      (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
   44      c = a * x1 * x2 := by
   45    let p : R[X] := C a * X ^ 2 + C b * X + C c
   46    have hp_natDegree : p.natDegree = 2 := le_antisymm natDegree_quadratic_le
   47      (by convert! p.card_roots'; rw [hroots, Multiset.card_pair])
   48    have hp_roots_card : p.roots.card = p.natDegree := by
   49      rw [hp_natDegree, hroots, Multiset.card_pair]
   50    simpa [leadingCoeff, hp_natDegree, p, hroots, mul_assoc, add_comm x1] using
   51      coeff_eq_esymm_roots_of_card hp_roots_card (k := 0) (by simp [hp_natDegree])
   52  
```

## P04. `List.sum_fixedLengthDigits_sum`

- Module / 模块: `Mathlib.Data.Nat.Digits.Lemmas`
- File / 文件: `.lake/packages/mathlib/Mathlib/Data/Nat/Digits/Lemmas.lean`
- Reconstruct / 重建: the whole proof, from line 515 / 整个证明，从第 515 行开始

```lean
  513  
  514  theorem sum_fixedLengthDigits_sum {b : ℕ} (hb : 1 < b) (l : ℕ) :
  515      ∑ L ∈ fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2 := by
  516    induction l with
  517    | zero => simp
  518    | succ l hr =>
  519        by_cases hl : l = 0
  520        · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
  521        rw [fixedLengthDigits_succ_eq_disjiUnion, Finset.sum_disjiUnion]
  522        simp only [consFixedLengthDigits, cons.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq,
  523          Finset.sum_image, sum_cons]
  524        rw [Finset.sum_comm]
  525        simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_nsmul, Finset.sum_range_id, hr,
  526          nsmul_eq_mul, Finset.card_range, add_tsub_cancel_right, cast_id, card_fixedLengthDigits,
  527          choose_two_right]
  528        rw [show b ^ l = b * b ^ (l - 1) by rw [← Nat.pow_succ', Nat.sub_one, Nat.succ_pred hl]]
  529        ring
  530  
```

## P05. `Polynomial.leadingCoeff_monic_mul`

- Module / 模块: `Mathlib.Algebra.Polynomial.Degree.Operations`
- File / 文件: `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/Operations.lean`
- Reconstruct / 重建: the whole proof, from line 366 / 整个证明，从第 366 行开始

```lean
  364  
  365  theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
  366      leadingCoeff (p * q) = leadingCoeff q := by
  367    rcases eq_or_ne q 0 with (rfl | H)
  368    · simp
  369    · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
  370      rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]
  371  
```

## P06. `ProofNetIR.Certificate.TerminalPar.parChoice_incident_agreement`

- Module / 模块: `ProofNetIR.Sequentialization`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Sequentialization.lean`
- Reconstruct / 重建: the whole proof, from line 15385 / 整个证明，从第 15385 行开始

```lean
15383      (terminal : certificate.TerminalPar left right conclusion)
15384      {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
15385      choice.1.incident conclusion = choice.2.incident conclusion := by
15386    simp only [parChoices, List.mem_filterMap] at membership
15387    rcases membership with ⟨link, linkMembership, emitted⟩
15388    cases link with
15389    | «axiom» first second => simp at emitted
15390    | tensor first second result => simp at emitted
15391    | par first second result =>
15392        simp at emitted
15393        subst choice
15394        have firstNotConclusion : first ≠ conclusion := by
15395          intro same
15396          subst first
15397          exact TerminalPar.no_parentUse structural terminal linkMembership
15398            (by simp [Link.usesAsPremise, Link.premises])
15399        have secondNotConclusion : second ≠ conclusion := by
15400          intro same
15401          subst second
15402          exact TerminalPar.no_parentUse structural terminal linkMembership
15403            (by simp [Link.usesAsPremise, Link.premises])
15404        have firstBoolean : (first == conclusion) = false :=
15405          beq_eq_false_iff_ne.mpr firstNotConclusion
15406        have secondBoolean : (second == conclusion) = false :=
15407          beq_eq_false_iff_ne.mpr secondNotConclusion
15408        simp [Edge.incident, firstBoolean, secondBoolean]
15409  
```

## P07. `ProofNetIR.SequentialFigure7.UnifyPayloadInput.ready_two_levels`

- Module / 模块: `ProofNetIR.SequentialFigure7UnifyPayloadEnabled`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyPayloadEnabled.lean`
- Reconstruct / 重建: the whole proof, from line 226 / 整个证明，从第 226 行开始

```lean
  224        before.stack.ready =
  225          readyPrefix ++
  226            [previousReady, enabled.vertex :: enabled.readyTail] := by
  227    rcases List.getLast?_eq_some_iff.mp enabled.top_ready with
  228      ⟨activePrefix, readyEquation⟩
  229    have lengthEquation :
  230        activePrefix.length + 1 = enabled.sigmaPrefix.length + 2 := by
  231      calc
  232        activePrefix.length + 1 = before.stack.ready.length := by
  233          rw [readyEquation]
  234          simp
  235        _ = before.stack.sigma.length :=
  236          invariant.stack_wellShaped.ready_aligned
  237        _ = enabled.sigmaPrefix.length + 2 := by
  238          rw [enabled.sigma_two_levels]
  239          simp
  240    have activePrefixNonempty : activePrefix ≠ [] := by
  241      intro empty
  242      rw [empty] at lengthEquation
  243      simp at lengthEquation
  244    cases previousLookup : activePrefix.getLast? with
  245    | none =>
  246        have : activePrefix = [] :=
  247          List.getLast?_eq_none_iff.mp previousLookup
  248        exact False.elim (activePrefixNonempty this)
  249    | some previousReady =>
  250        rcases List.getLast?_eq_some_iff.mp previousLookup with
  251          ⟨readyPrefix, activePrefixEquation⟩
  252        refine ⟨readyPrefix, previousReady, ?_⟩
  253        rw [readyEquation, activePrefixEquation]
  254        simp [List.append_assoc]
  255  
```

## P08. `ProofNetIR.SequentialSchedulerBridge.new_reserve_carrier_realizesSigma`

- Module / 模块: `ProofNetIR.SequentialSchedulerBridge`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerBridge.lean`
- Reconstruct / 重建: the whole proof, from line 1475 / 整个证明，从第 1475 行开始

```lean
 1473      (coreEquation :
 1474        certificate.reserveAxiomAt? coreBefore linkIndex = some coreAfter) :
 1475      RealizesSigma stackAfter coreAfter := by
 1476    rcases
 1477        SequentialStackState.operationalNewEnqueue?_exact stackEquation with
 1478      ⟨active, activeEquation, activeLt, stackMarksEq, stackNextAgeEq,
 1479        stackSigmaEq, stackReadyEq, stackWaitingEq, activeInitialized,
 1480        freshUndefined⟩
 1481    rcases certificate.reserveAxiomAt?_exact coreEquation with
 1482      ⟨left, right, component, exactLink, ready, componentLookup,
 1483        frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
 1484    refine {
 1485      marks_eq := ?_
 1486      horizon_eq := ?_
 1487      representative_eq_boundary := ?_ }
 1488    · calc
 1489        coreAfter.marks = coreBefore.marks := marksEq
 1490        _ = stackBefore.marks := realizes.marks_eq
 1491        _ = stackAfter.marks := stackMarksEq.symm
 1492    · calc
 1493        coreAfter.parents.size =
 1494            (coreBefore.parents.push coreBefore.parents.size).size := by
 1495          rw [parentsEq]
 1496        _ = coreBefore.parents.size + 1 := by simp
 1497        _ = stackBefore.nextAge + 1 := by rw [realizes.horizon_eq]
 1498        _ = stackAfter.nextAge := stackNextAgeEq.symm
 1499    · intro age ageBound
 1500      have ageBound' : age < stackBefore.nextAge + 1 := by
 1501        simpa [stackNextAgeEq] using ageBound
 1502      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ageBound') with
 1503        oldAge | freshAge
 1504      · calc
 1505          sigmaBoundary? stackAfter.sigma age =
 1506              sigmaBoundary?
 1507                (stackBefore.sigma ++ [stackBefore.nextAge]) age := by
 1508            rw [stackSigmaEq]
 1509          _ = sigmaBoundary? stackBefore.sigma age :=
 1510            sigmaBoundary?_append_fresh_old oldAge
 1511          _ = some (coreBefore.representative age) :=
 1512            realizes.representative_eq_boundary oldAge
 1513          _ = some (coreAfter.representative age) := by
 1514            rw [certificate.reserveAxiomAt?_old_representative
 1515              ordered coreEquation]
 1516      · subst age
 1517        calc
 1518          sigmaBoundary? stackAfter.sigma stackBefore.nextAge =
 1519              sigmaBoundary?
 1520                (stackBefore.sigma ++ [stackBefore.nextAge])
 1521                stackBefore.nextAge := by
 1522            rw [stackSigmaEq]
 1523          _ = some stackBefore.nextAge :=
 1524            wellShaped.sigma_partition.sigmaBoundary?_append_fresh_self
 1525          _ =
 1526              some (coreAfter.representative stackBefore.nextAge) := by
 1527            rw [← realizes.horizon_eq]
 1528            rw [certificate.reserveAxiomAt?_fresh_representative coreEquation]
 1529  
```

## P09. `ProofNetIR.Link.restrictTo?_eq_none_of_mem_not_mem`

- Module / 模块: `ProofNetIR.Sequentialization`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Sequentialization.lean`
- Reconstruct / 重建: the whole proof, from line 1951 / 整个证明，从第 1951 行开始

```lean
 1949      (vertexMembership : vertex ∈ link.vertices)
 1950      (vertexAbsent : vertex ∉ vertices) :
 1951      link.restrictTo? vertices = none := by
 1952    cases link with
 1953    | «axiom» first second =>
 1954        simp [Link.vertices] at vertexMembership
 1955        rcases vertexMembership with rfl | rfl <;>
 1956          simp [restrictTo?, List.idxOf?_eq_none_iff.mpr vertexAbsent]
 1957    | tensor first second result =>
 1958        simp [Link.vertices] at vertexMembership
 1959        rcases vertexMembership with rfl | rfl | rfl <;>
 1960          simp [restrictTo?, List.idxOf?_eq_none_iff.mpr vertexAbsent]
 1961    | par first second result =>
 1962        simp [Link.vertices] at vertexMembership
 1963        rcases vertexMembership with rfl | rfl | rfl <;>
 1964          simp [restrictTo?, List.idxOf?_eq_none_iff.mpr vertexAbsent]
 1965  
```

## P10. `MultilinearMap.mkPiRing_eq_iff`

- Module / 模块: `Mathlib.LinearAlgebra.Multilinear.Basic`
- File / 文件: `.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- Reconstruct / 重建: the whole proof, from line 1269 / 整个证明，从第 1269 行开始

```lean
 1267  
 1268  theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
 1269      MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
 1270    simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
 1271    constructor <;> intro h
 1272    · simpa using h fun _ => 1
 1273    · simp [h]
 1274  
```

## P11. `ProofNetIR.SequentialFigure7.tensorReferencePath`

- Module / 模块: `ProofNetIR.SequentialFigure7OlderRawMarkedRegionNewPreservation`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7OlderRawMarkedRegionNewPreservation.lean`
- Reconstruct / 重建: the whole proof, from line 42 / 整个证明，从第 42 行开始

```lean
   40      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
   41        path.start = left ∧ path.finish = right ∧
   42          path.vertices = [left, conclusion, right] := by
   43    have wellFormed :
   44        certificate.LinkWellFormed (.tensor left right conclusion) :=
   45      structural.2.2.2.2.1 _ membership
   46    have referenceTensorEdges :=
   47      UnificationMarking.referenceSwitchingGraph_tensorEdges
   48        certificate membership
   49    let leftEdge : Edge := { first := left, second := conclusion }
   50    let rightEdge : Edge := { first := right, second := conclusion }
   51    have leftEdgeMembership :
   52        leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
   53      simpa [leftEdge] using referenceTensorEdges.1
   54    have rightEdgeMembership :
   55        rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
   56      simpa [rightEdge] using referenceTensorEdges.2
   57    rcases List.getElem?_of_mem leftEdgeMembership with
   58      ⟨leftIndex, leftEdgeLookup⟩
   59    rcases List.getElem?_of_mem rightEdgeMembership with
   60      ⟨rightIndex, rightEdgeLookup⟩
   61    let leftDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
   62      index := leftIndex
   63      edge := leftEdge
   64      lookup := leftEdgeLookup
   65      forward := true }
   66    let rightDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
   67      index := rightIndex
   68      edge := rightEdge
   69      lookup := rightEdgeLookup
   70      forward := false }
   71    let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
   72      start := left
   73      finish := right
   74      traversed := [leftDirected, rightDirected]
   75      walk := by
   76        simpa [leftDirected, rightDirected, leftEdge, rightEdge,
   77          Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
   78          Graph.EdgeWalk.step
   79            (Graph.EdgeWalk.step
   80              (Graph.EdgeWalk.refl
   81                (graph := certificate.referenceSwitchingGraph) left)
   82              leftDirected rfl rfl)
   83            rightDirected rfl rfl
   84      verticesNodup := by
   85        simp [Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
   86          leftEdge, rightEdge, Graph.DirectedEdge.target,
   87          wellFormed.2.1]
   88        exact
   89          ⟨wellFormed.1,
   90            fun same => wellFormed.2.2.1 same.symm⟩ }
   91    refine ⟨path, rfl, rfl, ?_⟩
   92    simp [path, Graph.EdgeSimplePath.vertices,
   93      Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
```

## P12. `ProofNetIR.Graph.EdgeWalk.CyclicImmediateReverseSite.segmentJunction_of_flatten`

- Module / 模块: `ProofNetIR.Graph`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Graph.lean`
- Reconstruct / 重建: the whole proof, from line 1627 / 整个证明，从第 1627 行开始

```lean
 1625        ∀ segment ∈ segments, NoImmediateReverse segment)
 1626      (site : CyclicImmediateReverseSite segments.flatten) :
 1627      CyclicSegmentJunctionReverse segments := by
 1628    rcases site with
 1629      ⟨before, incoming, after, internal⟩ |
 1630        ⟨first, last, flattenedHead, flattenedLast, closing⟩
 1631    · exact .inl
 1632        (NoImmediateReverse.junction_reverse_of_flatten_cancel
 1633          segmentsNonempty segmentsReduced internal)
 1634    · let firstSegment := segments.head familyNonempty
 1635      let lastSegment := segments.getLast familyNonempty
 1636      have firstSegmentFamilyHead :
 1637          segments.head? = some firstSegment :=
 1638        List.head?_eq_some_head familyNonempty
 1639      have lastSegmentFamilyLast :
 1640          segments.getLast? = some lastSegment :=
 1641        List.getLast?_eq_some_getLast familyNonempty
 1642      have firstSegmentNonempty : firstSegment ≠ [] :=
 1643        segmentsNonempty firstSegment
 1644          (List.head_mem familyNonempty)
 1645      have lastSegmentNonempty : lastSegment ≠ [] :=
 1646        segmentsNonempty lastSegment
 1647          (List.getLast_mem familyNonempty)
 1648      rcases List.head?_eq_some_iff.mp firstSegmentFamilyHead with
 1649        ⟨familyTail, familyHeadEquation⟩
 1650      rcases List.getLast?_eq_some_iff.mp lastSegmentFamilyLast with
 1651        ⟨familyInitial, familyLastEquation⟩
 1652      have firstSegmentHead :
 1653          firstSegment.head? = some first := by
 1654        calc
 1655          firstSegment.head? =
 1656              segments.flatten.head? := by
 1657                rw [familyHeadEquation]
 1658                simp [List.head?_append,
 1659                  List.head?_eq_some_head firstSegmentNonempty]
 1660          _ = some first := flattenedHead
 1661      have lastSegmentLast :
 1662          lastSegment.getLast? = some last := by
 1663        calc
 1664          lastSegment.getLast? =
 1665              segments.flatten.getLast? := by
 1666                rw [familyLastEquation]
 1667                simp [List.getLast?_append,
 1668                  List.getLast?_eq_some_getLast lastSegmentNonempty]
 1669          _ = some last := flattenedLast
 1670      exact .inr
 1671        ⟨firstSegment, lastSegment, first, last,
```

## W1. `ProofNetIR.Certificate.fireTensor?_success_frontier_of_ne`

- Module / 模块: `ProofNetIR.Unification`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`
- Reconstruct / 重建: the steps on lines 5753 to 5788 / 第 5753 至 5788 行上的步骤
- The proof starts at line 5666 / 证明从第 5666 行开始

```lean
 5738    rcases state.tokenAt?_some_witness vertexToken with
 5739      ⟨rawToken, rawMarked, rawRepresentative⟩
 5740    have rawBound : rawToken < state.parents.size :=
 5741      abstractable.markedTokenBound rawMarked
 5742    have rawLookup :
 5743        state.marks[vertex]? = some (some rawToken) :=
 5744      UnificationState.assignedToken?_some_raw rawMarked
 5745    have mergedRawRepresentative :
 5746        UnificationState.representative
 5747          (state.mergeConclusion conclusion survivor retired)
 5748          rawToken =
 5749            if token = retired then survivor else token := by
 5750      have updated :=
 5751        ordered.setParent_representative survivorBound retiredBound
 5752          survivorLt survivorRoot retiredRoot rawBound
 5753      change
 5754        (state.setParent retired survivor).representative rawToken =
 5755          if token = retired then survivor else token
 5756      rw [updated, rawRepresentative]
 5757    have nextRawRepresentative :
 5758        next.representative rawToken =
 5759          if token = retired then survivor else token := by
 5760      rw [observation.representative_eq rawToken]
 5761      simpa [survivor, retired] using mergedRawRepresentative
 5762    have nextRawLookup :
 5763        next.marks[vertex]? = some (some rawToken) := by
 5764      rw [← observation.marks]
 5765      simpa [UnificationState.mergeConclusion,
 5766        UnificationState.setParent, UnificationState.markConclusion,
 5767        vertexDifferentConclusion.symm] using rawLookup
 5768    have nextVertexToken :
 5769        next.tokenAt? vertex =
 5770          some (if token = retired then survivor else token) := by
 5771      unfold UnificationState.tokenAt?
 5772      rw [nextRawLookup]
 5773      simp [nextRawRepresentative]
 5774    unfold fireTensor? at equation
 5775    rw [unifyEquation] at equation
 5776    cases leftComponentLookup :
 5777        state.componentAt? leftToken with
 5778    | none =>
 5779        simp [leftComponentLookup] at equation
 5780    | some leftComponent =>
 5781        simp only [leftComponentLookup] at equation
 5782        cases rightComponentLookup :
 5783            state.componentAt? rightToken with
 5784        | none =>
 5785            simp [rightComponentLookup] at equation
 5786        | some rightComponent =>
 5787            simp only [rightComponentLookup] at equation
 5788            cases leftPick :
 5789                pickVertex? leftComponent.frontier left with
```

## W2. `ProofNetIR.SequentialFigure7.UnifyPayloadStep.tensorShadow_readyBucketFrontierExactWithGap`

- Module / 模块: `ProofNetIR.SequentialFigure7UnifyPayloadInvariant`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyPayloadInvariant.lean`
- Reconstruct / 重建: the steps on lines 2505 to 2546 / 第 2505 至 2546 行上的步骤
- The proof starts at line 2285 / 证明从第 2285 行开始

```lean
 2490      refine ⟨step.tensorComponent, ?_, ?_⟩
 2491      · change step.coreTensor.components[step.previousBoundary]? =
 2492          some (some step.tensorComponent)
 2493        rw [step.tensor_components_eq,
 2494          Array.getElem?_setIfInBounds_ne
 2495            (Nat.ne_of_gt step.previous_lt_active)]
 2496        simp [step.previous_bound invariant]
 2497      · intro vertex
 2498        change vertex ∈ step.consumer.conclusion ::
 2499              (step.payload ++
 2500                (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) ↔
 2501          (vertex ∈ step.tensorComponent.frontier ∧
 2502            step.coreTensor.marks[vertex]? = some none) ∨
 2503          (step.previousBoundary = step.previousBoundary ∧
 2504            vertex ∈ step.payload)
 2505        rw [step.tensor_core_marks_eq]
 2506        rcases step.tokens_eq_adjacent with orientation | orientation
 2507        · have rightRaw := step.right_component_raw invariant
 2508          have leftRaw := step.left_component_raw invariant
 2509          rw [orientation.2.2] at rightRaw
 2510          rw [orientation.2.1] at leftRaw
 2511          have previousComponentEq :
 2512              previousComponent = step.tensorStep.rightComponent :=
 2513            Option.some.inj (Option.some.inj
 2514              (previousComponentLookup.symm.trans rightRaw))
 2515          have activeComponentEq :
 2516              activeComponent = step.tensorStep.leftComponent :=
 2517            Option.some.inj (Option.some.inj
 2518              (activeComponentLookup.symm.trans leftRaw))
 2519          subst previousComponent
 2520          subst activeComponent
 2521          simp only [tensorComponent, eq_self, true_and]
 2522          change vertex ∈ step.consumer.conclusion ::
 2523              (step.payload ++
 2524                (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) ↔
 2525            (vertex ∈ step.consumer.conclusion ::
 2526                (step.tensorStep.leftContext ++
 2527                  step.tensorStep.rightContext) ∧
 2528              step.prepared.coreMarked.marks[vertex]? = some none) ∨
 2529            vertex ∈ step.payload
 2530          constructor
 2531          · intro membership
 2532            simp only [List.mem_cons, List.mem_append] at membership ⊢
 2533            rcases membership with rfl | inPayload | inPrevious | inActive
 2534            · exact Or.inl ⟨Or.inl rfl, tokenGuards.1⟩
 2535            · exact Or.inr inPayload
 2536            · have facts := (previousExact vertex).mp inPrevious
 2537              exact Or.inl ⟨Or.inr (Or.inr
 2538                (right_context_of_frontier_unmarked facts.1 facts.2)),
 2539                facts.2⟩
 2540            · have facts := (activeExact vertex).mp inActive
 2541              exact Or.inl ⟨Or.inr (Or.inl
 2542                (left_context_of_frontier_unmarked facts.1 facts.2)),
 2543                facts.2⟩
 2544          · intro target
 2545            simp only [List.mem_cons, List.mem_append] at target ⊢
 2546            rcases target with ⟨frontier, unmarked⟩ | inPayload
 2547            · rcases frontier with rfl | inLeft | inRight
```

## W3. `ProofNetIR.Certificate.StructurallyWellFormed.appendTensorOccurrence`

- Module / 模块: `ProofNetIR.StructuralComposition`
- File / 文件: `.lake/packages/proofnet-ir/ProofNetIR/StructuralComposition.lean`
- Reconstruct / 重建: the steps on lines 1392 to 1420 / 第 1392 至 1420 行上的步骤
- The proof starts at line 1216 / 证明从第 1216 行开始

```lean
 1377              parentUseCount_appendTensorOccurrence_left_selected leftPremise
 1378                rightPremise left right leftRootInBounds]
 1379            rw [if_pos leftBoundary] at oldNode
 1380            omega
 1381          · have boundaryIff : vertex ∈
 1382                  (leftPremise.appendTensorOccurrence rightPremise left right
 1383                    leftRoot rightRoot boundary).conclusions ↔
 1384                vertex ∈ leftPremise.conclusions := by
 1385              change vertex ∈ boundary ↔ vertex ∈ leftPremise.conclusions
 1386              constructor
 1387              · intro membership
 1388                simp only [boundary, shiftedRight, List.mem_cons, List.mem_append,
 1389                  List.mem_map] at membership
 1390                rcases membership with freshEquality | inRemaining | inShifted
 1391                · have vertexBeforeFresh : vertex < fresh := by
 1392                    exact Nat.lt_of_lt_of_le inLeft (by simp [leftSize, fresh])
 1393                  exact False.elim ((Nat.ne_of_lt vertexBeforeFresh)
 1394                    freshEquality)
 1395                · exact leftBoundaryPermutation.mem_iff.mpr (by
 1396                    simp [selected, inRemaining])
 1397                · rcases inShifted with ⟨source, sourceMembership, equality⟩
 1398                  have vertexBeforeShifted : vertex < source + leftSize :=
 1399                    Nat.lt_of_lt_of_le inLeft
 1400                      (Nat.le_add_left leftSize source)
 1401                  exact False.elim ((Nat.ne_of_gt vertexBeforeShifted) equality)
 1402              · intro membership
 1403                have decomposed := leftBoundaryPermutation.mem_iff.mp membership
 1404                have inRemaining : vertex ∈ leftRemaining := by
 1405                  simpa [selected] using decomposed
 1406                simp [boundary, inRemaining]
 1407            rw [parentUseCount_appendTensorOccurrence_left_other leftPremise
 1408              rightPremise left right inLeft selected]
 1409            by_cases oldBoundary : vertex ∈ leftPremise.conclusions
 1410            · rw [if_pos (boundaryIff.mpr oldBoundary)]
 1411              rw [if_pos oldBoundary] at oldNode
 1412              exact oldNode.2
 1413            · rw [if_neg (fun membership =>
 1414                oldBoundary (boundaryIff.mp membership))]
 1415              rw [if_neg oldBoundary] at oldNode
 1416              exact oldNode.2
 1417      · by_cases isFresh : vertex = fresh
 1418        · subst vertex
 1419          unfold NodeWellFormed
 1420          constructor
 1421          · have formulaAtFresh :
```

