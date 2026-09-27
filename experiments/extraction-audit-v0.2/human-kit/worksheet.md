# Worksheet

## 1. `ProofNetIR.SequentialFigure7.tensorReferencePath` (try-first-repeat)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7CommitmentEdgeTargetAvoidance.lean`, from line 298.

```lean
  296      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
  297        path.start = left ∧ path.finish = right ∧
  298          path.vertices = [left, conclusion, right] := by
  299    have wellFormed : certificate.LinkWellFormed (.tensor left right conclusion) :=
  300      structural.2.2.2.2.1 _ membership
  301    have edges := UnificationMarking.referenceSwitchingGraph_tensorEdges
  302      certificate membership
  303    let leftEdge : Edge := { first := left, second := conclusion }
  304    let rightEdge : Edge := { first := right, second := conclusion }
  305    rcases List.getElem?_of_mem (by simpa [leftEdge] using edges.1) with
  306      ⟨leftIndex, leftLookup⟩
  307    rcases List.getElem?_of_mem (by simpa [rightEdge] using edges.2) with
  308      ⟨rightIndex, rightLookup⟩
  309    let leftDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
  310      index := leftIndex
  311      edge := leftEdge
  312      lookup := leftLookup
  313      forward := true }
  314    let rightDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
  315      index := rightIndex
  316      edge := rightEdge
  317      lookup := rightLookup
  318      forward := false }
  319    let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
  320      start := left
  321      finish := right
  322      traversed := [leftDirected, rightDirected]
  323      walk := by
  324        simpa [leftDirected, rightDirected, leftEdge, rightEdge,
  325          Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
  326          Graph.EdgeWalk.step
  327            (Graph.EdgeWalk.step
  328              (Graph.EdgeWalk.refl
  329                (graph := certificate.referenceSwitchingGraph) left)
  330              leftDirected rfl rfl)
  331            rightDirected rfl rfl
  332      verticesNodup := by
  333        simp [Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
  334          leftEdge, rightEdge, Graph.DirectedEdge.target, wellFormed.2.1]
  335        exact ⟨wellFormed.1, fun same ↦ wellFormed.2.2.1 same.symm⟩ }
  336    refine ⟨path, rfl, rfl, ?_⟩
  337    simp [path, Graph.EdgeSimplePath.vertices,
  338      Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
```

Steps (line, tactic):

Edges [i, j]:

## 2. `ProofNetIR.Certificate.CuspFreeTraversal.append` (try-first-repeat)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Sequentialization.lean`, from line 5986.

```lean
 5984      (boundary : ¬certificate.Cusp (first.getLast firstNonempty)
 5985        (second.head secondNonempty)) :
 5986      certificate.CuspFreeTraversal (first ++ second) := by
 5987    induction first with
 5988    | nil => exact False.elim (firstNonempty rfl)
 5989    | cons head tail ih =>
 5990        cases tail with
 5991        | nil =>
 5992            cases second with
 5993            | nil => exact False.elim (secondNonempty rfl)
 5994            | cons next rest =>
 5995                exact ⟨by simpa using boundary, secondFree⟩
 5996        | cons next rest =>
 5997            have tailNonempty : next :: rest ≠ [] := by simp
 5998            have tailBoundary :
 5999                ¬certificate.Cusp ((next :: rest).getLast tailNonempty)
 6000                  (second.head secondNonempty) := by
 6001              simpa using boundary
 6002            exact ⟨firstFree.1,
 6003              ih firstFree.2 tailNonempty tailBoundary⟩
 6004  
 6005  /-- Failure of traversal cusp-freedom exposes an internal adjacent cusp. -/
 6006  theorem CuspFreeTraversal.exists_cusp_of_not_free
 6007      (certificate : Certificate)
 6008      {traversed : List certificate.fullGraph.DirectedEdge}
 6009      (notFree : ¬certificate.CuspFreeTraversal traversed) :
 6010      ∃ before incoming outgoing after,
 6011        traversed = before ++ incoming :: outgoing :: after ∧
 6012          certificate.Cusp incoming outgoing := by
 6013    induction traversed with
 6014    | nil => exact False.elim (notFree trivial)
 6015    | cons first rest ih =>
 6016        cases rest with
 6017        | nil => exact False.elim (notFree trivial)
 6018        | cons second tail =>
 6019            by_cases cusp : certificate.Cusp first second
 6020            · exact ⟨[], first, second, tail, by simp, cusp⟩
 6021            · have tailNotFree :
 6022                  ¬certificate.CuspFreeTraversal (second :: tail) := by
 6023                intro tailFree
 6024                exact notFree ⟨cusp, tailFree⟩
 6025              rcases ih tailNotFree with
 6026                ⟨before, incoming, outgoing, after, equation, found⟩
```

Steps (line, tactic):

Edges [i, j]:

## 3. `ProofNetIR.SequentialFigure7.UnifyEmptyStep.output_unique` (try-first-repeat)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7Rules.lean`, from line 3405.

```lean
 3403      (left : UnifyEmptyStep certificate before first)
 3404      (right : UnifyEmptyStep certificate before second) :
 3405      first = second := by
 3406    have invariantEquation :
 3407        left.before_invariant = right.before_invariant :=
 3408      Subsingleton.elim _ _
 3409    cases invariantEquation
 3410    have leftExecutable :
 3411        unifyEmpty? certificate before left.before_invariant = some first :=
 3412      (unifyEmpty?_some_iff left.before_invariant).mpr ⟨left⟩
 3413    have rightExecutable :
 3414        unifyEmpty? certificate before left.before_invariant = some second :=
 3415      (unifyEmpty?_some_iff left.before_invariant).mpr ⟨right⟩
 3416    exact Option.some.inj (leftExecutable.symm.trans rightExecutable)
 3417  
 3418  end UnifyEmptyStep
 3419  
 3420  /-- Executable bounded empty-cell unification is sound for the independent
 3421  direct relation without a global certificate-validity assumption. -/
 3422  theorem unifyEmpty?_sound
 3423      {certificate : Certificate}
 3424      {before after : ReservationState}
 3425      (invariant : ReservationInvariant certificate before)
 3426      (equation : unifyEmpty? certificate before invariant = some after) :
 3427      UnifyEmptyRule certificate before after := by
 3428    rcases (unifyEmpty?_some_iff invariant).mp equation with ⟨step⟩
 3429    exact step.toRule
 3430  
 3431  /-- Executable empty-waiting-cell tensor unification preserves the complete
 3432  reservation invariant. -/
 3433  theorem unifyEmpty?_reservationInvariant
 3434      {certificate : Certificate}
 3435      {before after : ReservationState}
 3436      (invariant : ReservationInvariant certificate before)
 3437      (equation :
 3438        unifyEmpty? certificate before invariant = some after) :
 3439      ReservationInvariant certificate after := by
 3440    rcases (unifyEmpty?_some_iff invariant).mp equation with ⟨step⟩
 3441    exact step.reservationInvariant
 3442  
 3443  /-- Executable `forward` is sound for the independent direct relation without
 3444  a global certificate-validity assumption. -/
 3445  theorem forward?_sound
```

Steps (line, tactic):

Edges [i, j]:

## 4. `ProofNetIR.Graph.EdgeWalk.CyclicImmediateReverseNormalization.survives_or_reverse_mem` (try-first-repeat)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Graph.lean`, from line 1932.

```lean
 1930      (directed : graph.DirectedEdge)
 1931      (membership : directed ∈ before) :
 1932      directed ∈ after ∨ directed.reverse ∈ before := by
 1933    induction normalization with
 1934    | finish internal =>
 1935        exact internal.survives_or_reverse_mem directed membership
 1936    | @closing before middle after first last internal
 1937        closingReverse tail induction =>
 1938        rcases internal.survives_or_reverse_mem directed membership with
 1939          survived | paired
 1940        · simp at survived
 1941          rcases survived with atFirst | inMiddle | atLast
 1942          · subst directed
 1943            exact .inr
 1944              (internal.membership_subset first.reverse (by
 1945                simp [closingReverse]))
 1946          · rcases induction inMiddle with survived | pairedInMiddle
 1947            · exact .inl survived
 1948            · exact .inr
 1949                (internal.membership_subset directed.reverse (by
 1950                  simp [pairedInMiddle]))
 1951          · subst directed
 1952            exact .inr
 1953              (internal.membership_subset last.reverse (by
 1954                simp [closingReverse]))
 1955        · exact .inr paired
 1956  
 1957  /-- If cyclic normalization ends empty, the reverse of every directed-edge
 1958  value represented in the original traversal also occurs there, at the same
 1959  stored edge index. This theorem does not assert a bijection between list
 1960  positions. -/
 1961  theorem reverse_mem_of_normalizes_to_nil {graph : Graph}
 1962      {before after : List graph.DirectedEdge}
 1963      (normalization :
 1964        CyclicImmediateReverseNormalization before after)
 1965      (afterEmpty : after = [])
 1966      (directed : graph.DirectedEdge)
 1967      (membership : directed ∈ before) :
 1968      directed.reverse ∈ before := by
 1969    rcases normalization.survives_or_reverse_mem directed membership with
 1970      survived | paired
 1971    · rw [afterEmpty] at survived
 1972      contradiction
```

Steps (line, tactic):

Edges [i, j]:

## 5. `ProofNetIR.Graph.EdgeWalk.reverse` (try-first-repeat)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Graph.lean`, from line 1162.

```lean
 1160      {traversed : List graph.DirectedEdge}
 1161      (walk : graph.EdgeWalk start traversed finish) :
 1162      graph.EdgeWalk finish (reverseTraversal traversed) start := by
 1163    induction walk with
 1164    | refl => exact .refl _
 1165    | @step stepStart stepFinish priorSteps prior directed starts finishes ih =>
 1166        have first : graph.EdgeWalk stepFinish [directed.reverse]
 1167            stepStart := by
 1168          apply EdgeWalk.step (.refl stepFinish) directed.reverse
 1169          · rw [DirectedEdge.reverse_source, finishes]
 1170          · rw [DirectedEdge.reverse_target, starts]
 1171        have combined := first.trans ih
 1172        simpa [reverseTraversal] using combined
 1173  
 1174  /-- Reversing a valid traversal reverses its visited-vertex list exactly. -/
 1175  theorem visitedVertices_reverse {graph : Graph} {start finish : Vertex}
 1176      {traversed : List graph.DirectedEdge}
 1177      (walk : graph.EdgeWalk start traversed finish) :
 1178      visitedVertices finish (reverseTraversal traversed) =
 1179        (visitedVertices start traversed).reverse := by
 1180    induction walk with
 1181    | refl => simp [visitedVertices, reverseTraversal]
 1182    | @step stepStart stepFinish priorSteps prior directed starts finishes ih =>
 1183        have reversedEquation :
 1184            reverseTraversal (priorSteps ++ [directed]) =
 1185              directed.reverse :: reverseTraversal priorSteps := by
 1186          simp [reverseTraversal]
 1187        rw [reversedEquation]
 1188        simp only [visitedVertices, List.map_cons,
 1189          DirectedEdge.reverse_target]
 1190        rw [starts]
 1191        change stepFinish :: visitedVertices stepStart
 1192            (reverseTraversal priorSteps) = _
 1193        rw [ih]
 1194        simp [visitedVertices, List.map_append, finishes]
 1195  
 1196  end EdgeWalk
 1197  
 1198  namespace EdgeChain
 1199  
 1200  theorem sources_eq_start_targets_dropLast {graph : Graph}
 1201      {start finish : Vertex} {traversed : List graph.DirectedEdge}
 1202      (chain : graph.EdgeChain start traversed finish)
```

Steps (line, tactic):

Edges [i, j]:

## 6. `SimpleGraph.Walk.reverse_map` (several-goals)

Source: `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Walk/Maps.lean`, from line 93.

```lean
   91  
   92  @[simp]
   93  theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]
   94  
   95  @[simp]
   96  theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]
   97  
   98  @[simp]
   99  theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]
  100  
  101  @[simp]
  102  theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  103    induction p <;> simp [*]
  104  
  105  @[simp]
  106  theorem edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet := by ext; simp
  107  
  108  @[simp]
  109  theorem getVert_map (n : ℕ) : (p.map f).getVert n = f (p.getVert n) := by
  110    induction p generalizing n <;> cases n <;> simp [*]
  111  
  112  theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
  113      Function.Injective (Walk.map f : G.Walk u v → G'.Walk (f u) (f v)) := by
  114    intro p p' h
  115    induction p with
  116    | nil => cases p' <;> simp at h ⊢
  117    | cons _ _ ih =>
  118      cases p' with
  119      | nil => simp at h
  120      | cons _ _ =>
  121        simp only [map_cons, cons.injEq] at h
  122        grind
  123  
  124  section mapLe
  125  
  126  variable {G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v)
  127  
  128  /-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
  129  abbrev mapLe : G'.Walk u v :=
  130    p.map (.ofLE h)
  131  
  132  set_option backward.isDefEq.respectTransparency false in
  133  lemma support_mapLe_eq_support : (p.mapLe h).support = p.support := by simp
```

Steps (line, tactic):

Edges [i, j]:

## 7. `ProofNetIR.SequentialUnification.sum_sourceMultiplicity_eq_axiomCount` (several-goals)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialUnification.lean`, from line 253.

```lean
  251        ∀ link ∈ links, certificate.LinkWellFormed link) :
  252      (links.map (sourceMultiplicity vertex)).sum =
  253        (links.filter (·.containsAxiomEndpoint vertex)).length := by
  254    induction links with
  255    | nil =>
  256        simp
  257    | cons head tail induction =>
  258        have headWellFormed := allWellFormed head (by simp)
  259        have tailWellFormed :
  260            ∀ link ∈ tail, certificate.LinkWellFormed link := by
  261          intro link membership
  262          exact allWellFormed link (by simp [membership])
  263        rw [List.map_cons, List.sum_cons,
  264          sourceMultiplicity_eq_axiomIndicator_of_atom
  265            headWellFormed formulaLookup,
  266          induction tailWellFormed]
  267        by_cases accepted :
  268            head.containsAxiomEndpoint vertex = true <;>
  269          simp [accepted, Nat.add_comm]
  270  
  271  private theorem sum_sourceMultiplicity_eq_producerCount
  272      {certificate : Certificate} {vertex : Vertex} {formula : Formula}
  273      (formulaLookup : certificate.formula? vertex = some formula)
  274      (compound : formula.isAtom = false)
  275      (links : List Link)
  276      (allWellFormed :
  277        ∀ link ∈ links, certificate.LinkWellFormed link) :
  278      (links.map (sourceMultiplicity vertex)).sum =
  279        (links.filter (·.produces vertex)).length := by
  280    induction links with
  281    | nil =>
  282        simp
  283    | cons head tail induction =>
  284        have headWellFormed := allWellFormed head (by simp)
  285        have tailWellFormed :
  286            ∀ link ∈ tail, certificate.LinkWellFormed link := by
  287          intro link membership
  288          exact allWellFormed link (by simp [membership])
  289        rw [List.map_cons, List.sum_cons,
  290          sourceMultiplicity_eq_producerIndicator_of_compound
  291            headWellFormed formulaLookup compound,
  292          induction tailWellFormed]
  293        by_cases accepted : head.produces vertex = true <;>
```

Steps (line, tactic):

Edges [i, j]:

## 8. `ProofNetIR.SequentialFigure7.connectivePremiseMembership` (several-goals)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7MarkedTargetRawReturnFirstDescent.lean`, from line 33.

```lean
   31      {certificate : Certificate} {vertex : Vertex}
   32      (consumer : ConnectiveBelow certificate vertex) :
   33      vertex ∈ consumer.submittedLink.premises := by
   34    rcases consumer with
   35      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
   36        consumerEq, linkEq, wellFormed, premiseEq⟩
   37    subst vertex
   38    cases kind <;> cases side <;>
   39      simp [ConnectiveBelow.submittedLink,
   40        SequentialConnectiveKind.asLink, Link.premises,
   41        TensorPremiseSide.premise]
   42  
   43  private theorem connectiveBelow_conclusion_eq_of_parent
   44      {certificate : Certificate}
   45      (structural : certificate.StructurallyWellFormed)
   46      {vertex linkIndex : Nat} {kind : SequentialConnectiveKind}
   47      {storedLeft storedRight conclusion : Vertex}
   48      (consumer : ConnectiveBelow certificate vertex)
   49      (lookup :
   50        certificate.links[linkIndex]? =
   51          some (kind.asLink storedLeft storedRight conclusion))
   52      (membership :
   53        vertex ∈ (kind.asLink storedLeft storedRight conclusion).premises) :
   54      consumer.conclusion = conclusion := by
   55    have sameLink :
   56        consumer.submittedLink =
   57          kind.asLink storedLeft storedRight conclusion :=
   58      UnificationState.StructurallyWellFormed.parentLink_unique structural
   59        (List.mem_of_getElem? consumer.link_eq)
   60        (connectivePremiseMembership consumer)
   61        (List.mem_of_getElem? lookup) membership
   62    cases consumerKind : consumer.kind <;> cases kindEq : kind <;>
   63      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
   64        consumerKind, kindEq] at sameLink
   65    · exact sameLink.2.2
   66    · exact sameLink.2.2
   67  
   68  private theorem ReadyHeadInput.markedRepresentative_le_active
   69      {certificate : Certificate} {state : ReservationState}
   70      (input : ReadyHeadInput state)
   71      (invariant : SchedulerInvariant certificate state)
   72      {vertex : Vertex} {rawAge : RawTokenAge}
   73      (marked : state.core.marks[vertex]? = some (some rawAge)) :
```

Steps (line, tactic):

Edges [i, j]:

## 9. `ProofNetIR.SequentialFigure7.connectivePremiseMembership` (several-goals)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit.lean`, from line 88.

```lean
   86      {certificate : Certificate} {vertex : Vertex}
   87      (consumer : ConnectiveBelow certificate vertex) :
   88      vertex ∈ consumer.submittedLink.premises := by
   89    rcases consumer with
   90      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
   91        consumerEq, linkEq, wellFormed, premiseEq⟩
   92    subst vertex
   93    cases kind <;> cases side <;>
   94      simp [ConnectiveBelow.submittedLink,
   95        SequentialConnectiveKind.asLink, Link.premises,
   96        TensorPremiseSide.premise]
   97  
   98  private theorem connectiveMateMembership
   99      {certificate : Certificate} {vertex : Vertex}
  100      (consumer : ConnectiveBelow certificate vertex) :
  101      consumer.mate ∈ consumer.submittedLink.premises := by
  102    cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
  103      simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
  104        SequentialConnectiveKind.asLink, Link.premises,
  105        TensorPremiseSide.mate, kindEq, sideEq]
  106  
  107  private theorem connectiveSubmitted
  108      {certificate : Certificate} {vertex : Vertex}
  109      (consumer : ConnectiveBelow certificate vertex) :
  110      certificate.links[consumer.linkIndex]? =
  111          some (.tensor consumer.storedLeft consumer.storedRight
  112            consumer.conclusion) ∨
  113        certificate.links[consumer.linkIndex]? =
  114          some (.par consumer.storedLeft consumer.storedRight
  115            consumer.conclusion) := by
  116    cases kindEq : consumer.kind with
  117    | tensor =>
  118        exact Or.inl (by
  119          simpa [ConnectiveBelow.submittedLink,
  120            SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)
  121    | par =>
  122        exact Or.inr (by
  123          simpa [ConnectiveBelow.submittedLink,
  124            SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)
  125  
  126  private theorem connectiveVertexOwned_of_premisesOwned
  127      {certificate : Certificate} {vertex : Vertex}
  128      (consumer : ConnectiveBelow certificate vertex)
```

Steps (line, tactic):

Edges [i, j]:

## 10. `Finsupp.embDomain_apply` (several-goals)

Source: `.lake/packages/mathlib/Mathlib/Data/Finsupp/Defs.lean`, from line 429.

```lean
  427  @[grind =]
  428  theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (b : β) :
  429      embDomain f v b = if h : ∃ a, f a = b then v h.choose else 0 := by
  430    simp only [embDomain, coe_mk]
  431    -- TODO: investigate why `grind` needs `split_ifs` first; this should never happen.
  432    split_ifs <;> grind
  433  
  434  @[simp, grind =]
  435  theorem embDomain_apply_self (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  436    simp_rw [embDomain, coe_mk]
  437    grind
  438  
  439  @[grind =>]
  440  theorem embDomain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.range f) :
  441      embDomain f v a = 0 := by grind [embDomain]
  442  
  443  theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  444    fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply_self] using DFunLike.ext_iff.1 h (f a)
  445  
  446  @[simp]
  447  theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  448    (embDomain_injective f).eq_iff
  449  
  450  @[simp]
  451  theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  452    (embDomain_injective f).eq_iff' <| embDomain_zero f
  453  
  454  theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
  455      embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by grind
  456  
  457  @[simp]
  458  lemma embDomain_refl : embDomain (M := M) (Function.Embedding.refl α) = id := by
  459    ext; simp [embDomain_apply]
  460  
  461  end EmbDomain
  462  
  463  /-! ### Declarations about `zipWith` -/
  464  
  465  
  466  section ZipWith
  467  
  468  variable [Zero M] [Zero N] [Zero O]
  469  
```

Steps (line, tactic):

Edges [i, j]:

## 11. `ProofNetIR.SequentialFigure7.UnifyPayloadGapInvariant.queueParReservationInvariant` (calc)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyPayloadInvariant.lean`, from line 463.

```lean
  461        (conclusion :: payload))
  462      (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
  463      ReservationInvariant certificate { state with core := afterCore } := by
  464    have alignment := Certificate.queuePar?_reservationAlignment
  465      invariant.core_carriers_aligned invariant.core_counter_aligned step.queue_eq
  466    exact {
  467      stack_wellShaped := invariant.stack_wellShaped
  468      stack_operationalWaitingDomain := invariant.stack_operationalWaitingDomain
  469      realizesSigma := {
  470        marks_eq := step.exact.2.1.trans invariant.realizesSigma.marks_eq
  471        horizon_eq := by
  472          rw [step.exact.2.2.1]
  473          exact invariant.realizesSigma.horizon_eq
  474        representative_eq_boundary := by
  475          intro age ageBound
  476          have oldBound : age < state.stack.nextAge := by simpa using ageBound
  477          calc
  478            sigmaBoundary? state.stack.sigma age =
  479                some (state.core.representative age) :=
  480              invariant.realizesSigma.representative_eq_boundary oldBound
  481            _ = some (afterCore.representative age) := by
  482              unfold UnificationState.representative
  483              rw [step.exact.2.2.1] }
  484      core_orderedParents :=
  485        Certificate.queuePar?_orderedParents invariant.core_orderedParents
  486          step.queue_eq
  487      core_abstractable :=
  488        Certificate.queuePar?_abstractable invariant.core_abstractable
  489          step.queue_eq
  490      core_componentsFormulaConsistent :=
  491        Certificate.queuePar?_componentsFormulaConsistent
  492          invariant.core_componentsFormulaConsistent step.producer.wellFormed
  493          step.queue_eq
  494      core_carriers_aligned := alignment.1
  495      core_counter_aligned := alignment.2
  496      tags_size := invariant.tags_size }
  497  
  498  /-- Updating the surviving component in place preserves the exact equivalence
  499  between live raw slots and final sigma boundaries. -/
  500  private theorem queueParComponentDomainExact
  501      {certificate : Certificate} {state : ReservationState}
  502      {gapBoundary : RawTokenAge} {conclusion : Vertex}
  503      {payload : List Vertex} {afterCore : UnificationState}
```

Steps (line, tactic):

Edges [i, j]:

## 12. `TensorialAt.zero` (calc)

Source: `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tensoriality.lean`, from line 104.

```lean
  102  /-- A tensorial operation on sections of a vector bundle respects zero (since it respects scalar
  103  multiplication). -/
  104  theorem zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0 := by
  105    calc
  106      Φ 0 = Φ ((0 : M → 𝕜) • (0 : Π x, V x)) := by simp
  107      _   = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
  108      _   = 0 := by simp
  109  
  110  /-- A tensorial operation on sections of a vector bundle respects sums (since it respects binary
  111  addition). -/
  112  theorem sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
  113      (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
  114      Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  115    classical
  116    induction s using Finset.induction_on with
  117    | empty =>
  118        rw [Finset.sum_empty]
  119        exact hΦ.zero
  120    | insert a s ha h =>
  121        simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
  122        simp only [Finset.sum_insert ha, ← h hσ.2]
  123        exact hΦ.add (hσ.1) (.sum_section hσ.2)
  124  
  125  variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
  126    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]
  127  
  128  /-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
  129  only on the value of the section at `x`. -/
  130  lemma pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
  131      (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) :
  132      Φ σ = Φ σ' := by
  133    -- Select a local frame `s` for the bundle `V` near `x`,
  134    -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  135    -- this frame
  136    let t := trivializationAt F V x
  137    have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  138    let b := Basis.ofVectorSpace 𝕜 F
  139    let s := t.localFrame b
  140    let c := t.localFrame_coeff I b
  141    have hs (i) : MDiffAt (T% (s i)) x :=
  142      (contMDiffAt_localFrame_of_mem 1 _ b i x_mem).mdifferentiableAt (by simp)
  143    have hc {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) (i) :
  144        MDiffAt (LinearMap.piApply (c i) σ) x :=
```

Steps (line, tactic):

Edges [i, j]:

## 13. `ProofNetIR.SequentialFigure7.WaitStep.continuationCredit_of_rawMateSelected` (calc)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7ContinuationCreditPreservation.lean`, from line 387.

```lean
  385      (consumer : ConnectiveBelow certificate vertex)
  386      (selected : consumer.mate = step.prepared.stackResult.vertex) :
  387      ContinuationCredit certificate after vertex := by
  388    let opposite :=
  389      connectiveBelowAtMateEq consumer structural selected
  390    have sameConclusion :
  391        consumer.conclusion = step.consumer.conclusion := by
  392      calc
  393        consumer.conclusion = opposite.conclusion :=
  394          (connectiveBelowAtMateEq_conclusion
  395            consumer structural selected).symm
  396        _ = step.consumer.conclusion :=
  397          connectiveBelow_conclusion_eq opposite step.consumer
  398    apply ContinuationCredit.futureConclusion
  399      consumer step.destination.boundary
  400    rw [sameConclusion]
  401    rcases step.destination.exact with
  402      ⟨payload, _beforeCell, afterCell, _marks, _nextAge,
  403        _sigma, _ready, _core, _tags⟩
  404    exact FutureWorkAt.waiting afterCell (by simp)
  405  
  406  /-- Every old continuation credit crosses a complete wait step. The only
  407  prepared-prefix residual is a raw mate equal to the selected occurrence; the
  408  wait destination upgrades exactly that residual to future-conclusion credit. -/
  409  theorem continuationCredit
  410      {certificate : Certificate} {before after : ReservationState}
  411      (step : WaitStep certificate before after)
  412      (structural : certificate.StructurallyWellFormed)
  413      {vertex : Vertex}
  414      (credit : ContinuationCredit certificate before vertex) :
  415      ContinuationCredit certificate after vertex := by
  416    rcases step.prepared.continuationCredit_or_rawMateSelected credit with
  417      middleCredit | ⟨consumer, _mateUnmarked, selected⟩
  418    · exact middleCredit.afterWaitDestination step.destination
  419    · exact step.continuationCredit_of_rawMateSelected
  420        structural consumer selected
  421  
  422  end WaitStep
  423  
  424  namespace ConclStep
  425  
  426  /-- A `concl` step transports any prior continuation credit.
  427  The raw-mate-selected residual is impossible because the selected occurrence
```

Steps (line, tactic):

Edges [i, j]:

## 14. `ProofNetIR.Certificate.TerminalTensor.tensorPlacement_inverse_conclusion` (calc)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Sequentialization.lean`, from line 13459.

```lean
13457      (TerminalTensor.tensorPlacement structural terminal).inverse conclusion =
13458        (certificate.tensorLeftVertices left conclusion).length +
13459          (certificate.tensorRightVertices left conclusion).length := by
13460    let placement := TerminalTensor.tensorPlacement structural terminal
13461    have forward := TerminalTensor.tensorPlacement_forward_last structural terminal
13462    calc
13463      placement.inverse conclusion = placement.inverse
13464          (placement.forward
13465            ((certificate.tensorLeftVertices left conclusion).length +
13466              (certificate.tensorRightVertices left conclusion).length)) := by
13467        exact congrArg placement.inverse forward.symm
13468      _ = (certificate.tensorLeftVertices left conclusion).length +
13469            (certificate.tensorRightVertices left conclusion).length :=
13470        placement.inverse_forward _
13471  
13472  /-- The tensor rule's canonical boundary order (new tensor first, followed by
13473  the left and right contexts) is a vertex-occurrence permutation of the input
13474  boundary pulled back through the canonical component placement. -/
13475  theorem occurrenceBoundaryReconstruction
13476      {certificate : Certificate} {left right conclusion : Vertex}
13477      (structural : certificate.StructurallyWellFormed)
13478      (terminal : certificate.TerminalTensor left right conclusion) :
13479      let leftVertices := certificate.tensorLeftVertices left conclusion
13480      let rightVertices := certificate.tensorRightVertices left conclusion
13481      let otherConclusions := certificate.tensorOtherConclusions conclusion
13482      let leftContext := otherConclusions.filter leftVertices.contains
13483      let rightContext := otherConclusions.filter rightVertices.contains
13484      let placement := TerminalTensor.tensorPlacement structural terminal
13485      ([leftVertices.length + rightVertices.length] ++
13486        leftContext.map leftVertices.idxOf ++
13487        (rightContext.map rightVertices.idxOf).map
13488          (fun vertex => vertex + leftVertices.length)).Perm
13489        (certificate.conclusions.map placement.inverse) := by
13490    dsimp only
13491    let leftVertices := certificate.tensorLeftVertices left conclusion
13492    let rightVertices := certificate.tensorRightVertices left conclusion
13493    let otherConclusions := certificate.tensorOtherConclusions conclusion
13494    let leftContext := otherConclusions.filter leftVertices.contains
13495    let rightContext := otherConclusions.filter rightVertices.contains
13496    let placement := TerminalTensor.tensorPlacement structural terminal
13497    have originalNodup : certificate.conclusions.Nodup :=
13498      nodup_of_eraseDups_length_eq structural.2.2.2.1
13499    have rightFilterEquation : rightContext =
```

Steps (line, tactic):

Edges [i, j]:

## 15. `ProofNetIR.SequentialFigure7.UnifyPayloadStep.realizesSigma` (calc)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyPayload.lean`, from line 979.

```lean
  977      {certificate : Certificate} {before after : ReservationState}
  978      (step : UnifyPayloadStep certificate before after) :
  979      RealizesSigma step.stackAfter step.coreAfter := by
  980    have tensorRealizes := step.tensor_realizesSigma
  981    have marksEquation := step.activationFold.marks_eq
  982    have parentsEquation := step.activationFold.parents_eq
  983    exact {
  984      marks_eq := by
  985        rw [marksEquation]
  986        exact tensorRealizes.marks_eq
  987      horizon_eq := by
  988        rw [parentsEquation]
  989        exact tensorRealizes.horizon_eq
  990      representative_eq_boundary := by
  991        intro age ageBound
  992        calc
  993          sigmaBoundary? step.stackAfter.sigma age =
  994              some (step.coreTensor.representative age) :=
  995            tensorRealizes.representative_eq_boundary ageBound
  996          _ = some (step.coreAfter.representative age) := by
  997            unfold UnificationState.representative
  998            rw [parentsEquation] }
  999  
 1000  /-- Atomic tensor-plus-payload-fold unification preserves the complete
 1001  reservation invariant.  This theorem deliberately does not mention or imply
 1002  the stronger `SchedulerInvariant`. -/
 1003  theorem reservationInvariant
 1004      {certificate : Certificate} {before after : ReservationState}
 1005      (step : UnifyPayloadStep certificate before after) :
 1006      ReservationInvariant certificate after := by
 1007    have middleInvariant :
 1008        ReservationInvariant certificate step.prepared.after :=
 1009      step.prepared.reservationInvariant step.before_invariant
 1010    have tensorWellFormed :
 1011        certificate.LinkWellFormed
 1012          (.tensor step.consumer.storedLeft step.consumer.storedRight
 1013            step.consumer.conclusion) :=
 1014      Certificate.tensorBelow?_wellFormed step.consumer_eq
 1015    have tensorConclusionBound :
 1016        step.consumer.conclusion < certificate.formulas.size :=
 1017      tensorWellFormed.2.2.2.2.2.1
 1018    have payloadInBounds :
 1019        ∀ {payload},
```

Steps (line, tactic):

Edges [i, j]:

## 16. `smul_ball` (conv)

Source: `.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`, from line 81.

```lean
   79  variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
   80  
   81  theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ball x r = ball (c • x) (‖c‖ * r) := by
   82    ext y
   83    rw [mem_smul_set_iff_inv_smul_mem₀ hc]
   84    conv_lhs => rw [← inv_smul_smul₀ hc x]
   85    simp [← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hc), mul_comm _ r, dist_smul₀]
   86  
   87  theorem smul_unitBall {c : 𝕜} (hc : c ≠ 0) : c • ball (0 : E) (1 : ℝ) = ball (0 : E) ‖c‖ := by
   88    rw [_root_.smul_ball hc, smul_zero, mul_one]
   89  
   90  theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
   91      c • sphere x r = sphere (c • x) (‖c‖ * r) := by
   92    ext y
   93    rw [mem_smul_set_iff_inv_smul_mem₀ hc]
   94    conv_lhs => rw [← inv_smul_smul₀ hc x]
   95    simp only [mem_sphere, dist_smul₀, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
   96      mul_comm r]
   97  
   98  theorem smul_closedBall' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
   99      c • closedBall x r = closedBall (c • x) (‖c‖ * r) := by
  100    simp only [← ball_union_sphere, Set.smul_set_union, _root_.smul_ball hc, smul_sphere' hc]
  101  
  102  theorem set_smul_sphere_zero {s : Set 𝕜} (hs : 0 ∉ s) (r : ℝ) :
  103      s • sphere (0 : E) r = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) :=
  104    calc
  105      s • sphere (0 : E) r = ⋃ c ∈ s, c • sphere (0 : E) r := iUnion_smul_left_image.symm
  106      _ = ⋃ c ∈ s, sphere (0 : E) (‖c‖ * r) := iUnion₂_congr fun c hc ↦ by
  107        rw [smul_sphere' (ne_of_mem_of_not_mem hc hs), smul_zero]
  108      _ = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) := by ext; simp [eq_comm]
  109  
  110  /-- Image of a bounded set in a normed space under scalar multiplication by a constant is
  111  bounded. See also `Bornology.IsBounded.smul` for a similar lemma about an isometric action. -/
  112  theorem Bornology.IsBounded.smul₀ {s : Set E} (hs : IsBounded s) (c : 𝕜) : IsBounded (c • s) :=
  113    (lipschitzWith_smul c).isBounded_image hs
  114  
  115  /-- If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is contained in any
  116  fixed neighborhood of `x`. -/
  117  theorem eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bornology.IsBounded s)
  118      {u : Set E} (hu : u ∈ 𝓝 x) : ∀ᶠ r in 𝓝 (0 : 𝕜), {x} + r • s ⊆ u := by
  119    obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  120    obtain ⟨R, Rpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ s ⊆ closedBall 0 R := hs.subset_closedBall_lt 0 0
  121    have : Metric.closedBall (0 : 𝕜) (ε / R) ∈ 𝓝 (0 : 𝕜) := closedBall_mem_nhds _ (div_pos εpos Rpos)
```

Steps (line, tactic):

Edges [i, j]:

## 17. `AddConstMapClass.map_sub_nsmul` (conv)

Source: `.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean`, from line 168.

```lean
  166  @[scoped simp]
  167  theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  168      (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  169    conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]
  170  
  171  @[scoped simp]
  172  theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  173      (f : F) (x : G) : f (x - a) = f x - b := by
  174    simpa using map_sub_nsmul f x 1
  175  
  176  theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
  177      (f : F) (x : G) : f (x - 1) = f x - b :=
  178    map_sub_const f x
  179  
  180  @[scoped simp]
  181  theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  182      (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  183    simpa using map_sub_nsmul f x n
  184  
  185  @[scoped simp]
  186  theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  187      (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
  188      f (x - ofNat(n)) = f x - ofNat(n) • b :=
  189    map_sub_nat' f x n
  190  
  191  @[scoped simp]
  192  theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  193      (f : F) (x : G) : ∀ n : ℤ, f (x + n • a) = f x + n • b
  194    | (n : ℕ) => by simp
  195    | .negSucc n => by simp [← sub_eq_add_neg]
  196  
  197  @[scoped simp]
  198  theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  199      (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  200    simpa using map_add_zsmul f 0 n
  201  
  202  @[scoped simp]
  203  theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  204      (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  205    rw [← map_add_zsmul f x n, zsmul_one]
  206  
  207  theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
  208      (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp
```

Steps (line, tactic):

Edges [i, j]:

## 18. `AnalyticOn.iteratedFDerivWithin_comp_perm` (conv)

Source: `.lake/packages/mathlib/Mathlib/Analysis/Analytic/IteratedFDeriv.lean`, from line 237.

```lean
  235      (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
  236      (σ : Perm (Fin n)) :
  237      iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  238    rcases h x hx with ⟨p, r, hp⟩
  239    rw [hp.iteratedFDerivWithin_eq_sum h hs hx, hp.iteratedFDerivWithin_eq_sum h hs hx]
  240    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  241    simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]
  242  
  243  theorem AnalyticOn.domDomCongr_iteratedFDerivWithin
  244      (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (σ : Perm (Fin n)) :
  245      (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  246    ext
  247    exact h.iteratedFDerivWithin_comp_perm hs hx _ _
  248  
  249  /-- The `n`-th iterated derivative of an analytic function on a set is symmetric. -/
  250  theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm
  251      (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
  252      (σ : Perm (Fin n)) :
  253      iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  254    rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  255    rw [insert_eq_of_mem hx] at hu
  256    have : iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  257      iteratedFDerivWithin_inter_open u_open xu
  258    rw [← this]
  259    exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.analyticOn (hs.inter u_open) ⟨hx, xu⟩ _ _
  260  
  261  theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
  262      (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ}
  263      (σ : Perm (Fin n)) :
  264      (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  265    ext
  266    exact h.iteratedFDerivWithin_comp_perm hs hx _ _
  267  
  268  /-- The `n`-th iterated derivative of an analytic function is symmetric. -/
  269  theorem AnalyticOn.iteratedFDeriv_comp_perm
  270      (h : AnalyticOn 𝕜 f univ) {n : ℕ} (v : Fin n → E) (σ : Perm (Fin n)) :
  271      iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  272    rw [← iteratedFDerivWithin_univ]
  273    exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _
  274  
  275  theorem AnalyticOn.domDomCongr_iteratedFDeriv (h : AnalyticOn 𝕜 f univ) {n : ℕ} (σ : Perm (Fin n)) :
  276      (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  277    rw [← iteratedFDerivWithin_univ]
```

Steps (line, tactic):

Edges [i, j]:

## 19. `Nat.ofDigits_modEq'` (conv)

Source: `.lake/packages/mathlib/Mathlib/Data/Nat/Digits/Lemmas.lean`, from line 241.

```lean
  239  
  240  theorem ofDigits_modEq' (b b' : ℕ) (k : ℕ) (h : b ≡ b' [MOD k]) (L : List ℕ) :
  241      ofDigits b L ≡ ofDigits b' L [MOD k] := by
  242    induction L with
  243    | nil => rfl
  244    | cons d L ih =>
  245      dsimp [ofDigits]
  246      dsimp [Nat.ModEq] at *
  247      conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
  248      conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
  249  
  250  theorem ofDigits_modEq (b k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  251    ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L
  252  
  253  theorem ofDigits_mod (b k : ℕ) (L : List ℕ) : ofDigits b L % k = ofDigits (b % k) L % k :=
  254    ofDigits_modEq b k L
  255  
  256  theorem ofDigits_mod_eq_head! (b : ℕ) (l : List ℕ) : ofDigits b l % b = l.head! % b := by
  257    induction l <;> simp [Nat.ofDigits]
  258  
  259  theorem head!_digits {b n : ℕ} (h : b ≠ 1) : (Nat.digits b n).head! = n % b := by
  260    by_cases hb : 1 < b
  261    · rcases n with _ | n
  262      · simp
  263      · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
  264        rw [Nat.ofDigits_mod_eq_head! _ _]
  265        exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
  266            Nat.digits_ne_nil_iff_ne_zero.mpr <| Nat.succ_ne_zero n)).symm
  267    · rcases n with _ | _ <;> simp_all [show b = 0 by lia]
  268  
  269  theorem ofDigits_zmodeq' (b b' : ℤ) (k : ℕ) (h : b ≡ b' [ZMOD k]) (L : List ℕ) :
  270      ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  271    induction L with
  272    | nil => rfl
  273    | cons d L ih =>
  274      dsimp [ofDigits]
  275      dsimp [Int.ModEq] at *
  276      conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
  277      conv_rhs => rw [Int.add_emod, Int.mul_emod]
  278  
  279  theorem ofDigits_zmodeq (b : ℤ) (k : ℕ) (L : List ℕ) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  280    ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L
  281  
```

Steps (line, tactic):

Edges [i, j]:

## 20. `QPF.Cofix.dest_corec` (conv)

Source: `.lake/packages/mathlib/Mathlib/Data/QPF/Univariate/Basic.lean`, from line 369.

```lean
  367  
  368  theorem Cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
  369      Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x := by
  370    conv =>
  371      lhs
  372      rw [Cofix.dest, Cofix.corec]
  373    dsimp
  374    rw [corecF_eq, abs_map, abs_repr, ← comp_map]; rfl
  375  
  376  private theorem Cofix.bisim_aux (r : Cofix F → Cofix F → Prop) (h' : ∀ x, r x x)
  377      (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
  378      ∀ x y, r x y → x = y := by
  379    rintro ⟨x⟩ ⟨y⟩ rxy
  380    apply Quot.sound
  381    let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  382    have : IsPrecongr r' := by
  383      intro a b r'ab
  384      have h₀ :
  385        Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest a) =
  386          Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest b) :=
  387        h _ _ r'ab
  388      have h₁ : ∀ u v : q.P.M, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
  389        intro u v cuv
  390        apply Quot.sound
  391        simp only [r']
  392        rw [Quot.sound cuv]
  393        apply h'
  394      let f : Quot r → Quot r' :=
  395        Quot.lift (Quot.lift (Quot.mk r') h₁) <| by
  396          rintro ⟨c⟩ ⟨d⟩ rcd
  397          exact Quot.sound rcd
  398      have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
  399      rw [← this, ← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map,
  400        abs_map, h₀]
  401      rw [← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map, abs_map]
  402    exact ⟨r', this, rxy⟩
  403  
  404  theorem Cofix.bisim_rel (r : Cofix F → Cofix F → Prop)
  405      (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
  406      ∀ x y, r x y → x = y := by
  407    let r' (x y) := x = y ∨ r x y
  408    intro x y rxy
  409    apply Cofix.bisim_aux r'
```

Steps (line, tactic):

Edges [i, j]:

## 21. `ProofNetIR.SequentialFigure7.waitingParProducer?_eq_some` (case-next)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7UnifyOne.lean`, from line 100.

```lean
   98      {certificate : Certificate} {conclusion : Vertex}
   99      (producer : WaitingParProducer certificate conclusion) :
  100      waitingParProducer? certificate conclusion = some producer := by
  101    rcases producer with
  102      ⟨producerIndex, producerLeft, producerRight,
  103        producerSource, producerLink, producerWellFormed⟩
  104    unfold waitingParProducer?
  105    split
  106    next linkIndex left right actualConclusion sourceEquation =>
  107      have singletonEquation :
  108          ({
  109            linkIndex := linkIndex
  110            link := .par left right actualConclusion } :
  111              SequentialUnification.SourceIncidence) =
  112            {
  113              linkIndex := producerIndex
  114              link := .par producerLeft producerRight conclusion } := by
  115        exact List.singleton_inj.mp
  116          (Option.some.inj (sourceEquation.symm.trans producerSource))
  117      have indexEquation : linkIndex = producerIndex :=
  118        congrArg SequentialUnification.SourceIncidence.linkIndex
  119          singletonEquation
  120      have linkValueEquation :
  121          (.par left right actualConclusion : Link) =
  122            .par producerLeft producerRight conclusion :=
  123        congrArg SequentialUnification.SourceIncidence.link
  124          singletonEquation
  125      injection linkValueEquation with leftEquation rightEquation conclusionEquation
  126      subst linkIndex
  127      subst left
  128      subst right
  129      subst actualConclusion
  130      simp [producerLink,
  131        (certificate.linkLocallyWellFormed_iff
  132          (.par producerLeft producerRight conclusion)).mpr
  133            producerWellFormed]
  134    next sourceEquation =>
  135      exact False.elim
  136        (sourceEquation producerIndex producerLeft producerRight
  137          conclusion producerSource)
  138  
  139  /-- Independent direct production-state relation for activating one waiting
  140  par conclusion.
```

Steps (line, tactic):

Edges [i, j]:

## 22. `SetLike.prod_mem_graded` (case-next)

Source: `.lake/packages/mathlib/Mathlib/Algebra/GradedMonoid.lean`, from line 679.

```lean
  677  variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}
  678  
  679  theorem prod_mem_graded (hF : ∀ k ∈ F, g k ∈ A (i k)) : ∏ k ∈ F, g k ∈ A (∑ k ∈ F, i k) := by
  680    classical
  681    induction F using Finset.induction_on
  682    · simp [GradedOne.one_mem]
  683    · case insert j F' hF2 h3 =>
  684      rw [Finset.prod_insert hF2, Finset.sum_insert hF2]
  685      apply SetLike.mul_mem_graded (by grind)
  686      grind
  687  
  688  theorem prod_pow_mem_graded (n : κ → ℕ) (hF : ∀ k ∈ F, g k ∈ A (i k)) :
  689      ∏ k ∈ F, g k ^ n k ∈ A (∑ k ∈ F, n k • i k) :=
  690    prod_mem_graded A _ _ fun k hk ↦ pow_mem_graded _ (hF k hk)
  691  
  692  end SetLike
  693  
  694  end CommMonoid
  695  
```

Steps (line, tactic):

Edges [i, j]:

## 23. `ProofNetIR.SequentialFigure7.exists_prepare?_eq_some_of_ok` (case-next)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7Rules.lean`, from line 402.

```lean
  400            stackResult.vertex stackResult.rawAge =
  401          .ok coreMarked) :
  402      ∃ prepared, prepare? before = some prepared := by
  403    let prepared : PreparedStep before := {
  404      stackResult
  405      coreMarked
  406      stack_eq := stackEquation
  407      core_mark_eq := coreEquation }
  408    refine ⟨prepared, ?_⟩
  409    unfold prepare?
  410    split
  411    next stackError stackFailure =>
  412      rw [stackEquation] at stackFailure
  413      simp at stackFailure
  414    next actualStack stackSuccess =>
  415      have actualStackEq : actualStack = stackResult :=
  416        Except.ok.inj (stackSuccess.symm.trans stackEquation)
  417      subst actualStack
  418      split
  419      next coreError coreFailure =>
  420        rw [coreEquation] at coreFailure
  421        simp at coreFailure
  422      next actualCore coreSuccess =>
  423        have actualCoreEq : actualCore = coreMarked :=
  424          Except.ok.inj (coreSuccess.symm.trans coreEquation)
  425        subst actualCore
  426        congr 2
  427  
  428  /-- Independent proposition-level meaning of the synchronized common prefix
  429  at one selected occurrence and raw age.
  430  
  431  This relation does not mention `prepare?`, either executable query, or either
  432  rule executable.  It directly states the list decomposition selected by the
  433  concrete scheduler policy and the two synchronized raw-mark updates. -/
  434  def RulePrefixAt (before after : ReservationState)
  435      (vertex : Vertex) (rawAge : RawTokenAge) : Prop :=
  436    ∃ (readyPrefix : List (List Vertex))
  437        (readyTail : List Vertex)
  438        (sigmaPrefix : List RawTokenAge),
  439      before.stack.ready =
  440          readyPrefix ++ [vertex :: readyTail] ∧
  441      before.stack.sigma =
  442          sigmaPrefix ++ [rawAge] ∧
```

Steps (line, tactic):

Edges [i, j]:

## 24. `ProofNetIR.SequentialUnification.SourceLeftChain.reachable_of_head_last` (case-next)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialRoute.lean`, from line 153.

```lean
  151      (head : trace.head? = some source)
  152      (last : trace.getLast? = some target) :
  153      SourceLeftReachable certificate source target := by
  154    induction chain generalizing source target with
  155    | singleton vertex =>
  156        simp only [List.head?_cons, Option.some.injEq] at head
  157        simp only [List.getLast?_singleton, Option.some.injEq] at last
  158        subst source
  159        subst target
  160        exact .refl vertex
  161    | @cons current next tail step rest induction =>
  162        simp only [List.head?_cons, Option.some.injEq] at head
  163        subst source
  164        have restHead : (next :: tail).head? = some next := by
  165          simp
  166        have restLast : (next :: tail).getLast? = some target := by
  167          simpa [List.getLast?_cons_of_ne_nil (by simp :
  168            next :: tail ≠ [])] using last
  169        exact .step step (induction restHead restLast)
  170  
  171  /-- The oriented semantic content of a successful bounded `NEXTAXIOM` call.
  172  
  173  `reached` is the final vertex actually visited by the recursive search;
  174  `partner` is the other endpoint of the submitted axiom.  The disjunction in
  175  `exactAxiom` is intentional: the submitted link keeps its own stored
  176  orientation, independently of the search orientation. -/
  177  structure NextAxiomRoute
  178      {certificate : Certificate} {state : UnificationState} {fuel : Nat}
  179      {inputTags : Array Bool}
  180      (start : Vertex)
  181      (result : NextAxiomResult certificate state fuel inputTags)
  182      (reached partner : Vertex) : Prop where
  183    traceNonempty : result.trace ≠ []
  184    traceHead : result.trace.head? = some start
  185    traceLast : result.trace.getLast? = some reached
  186    chain : SourceLeftChain certificate result.trace
  187    reachable : SourceLeftReachable certificate start reached
  188    exactAxiom :
  189      certificate.links[result.linkIndex]? =
  190          some (.axiom reached partner) ∨
  191        certificate.links[result.linkIndex]? =
  192          some (.axiom partner reached)
  193    storedEndpoints :
```

Steps (line, tactic):

Edges [i, j]:

## 25. `FirstOrder.Language.BoundedFormula.realize_foldr_imp` (case-next)

Source: `.lake/packages/mathlib/Mathlib/ModelTheory/Semantics.lean`, from line 293.

```lean
  291      ∀ (v : α → M) xs,
  292        (l.foldr BoundedFormula.imp f).Realize v xs =
  293        ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
  294    intro v xs
  295    induction l
  296    next => simp
  297    next f' _ _ => by_cases f'.Realize v xs <;> simp [*]
  298  
  299  @[simp]
  300  theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term _} :
  301      (R.boundedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  302    Iff.rfl
  303  
  304  @[simp]
  305  theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
  306      (R.boundedFormula₁ t).Realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  307    rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]
  308    refine congr rfl (funext fun _ => ?_)
  309    simp only [Matrix.cons_val_fin_one]
  310  
  311  @[simp]
  312  theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
  313      (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
  314        RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  315    rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  316    refine congr rfl (funext (Fin.cases ?_ ?_))
  317    · simp only [Matrix.cons_val_zero]
  318    · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
  319  
  320  @[simp]
  321  theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  322    simp only [max]
  323    tauto
  324  
  325  @[simp]
  326  theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
  327      (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  328    induction l with
  329    | nil => simp
  330    | cons φ l ih =>
  331      simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
  332        exists_eq_left]
  333  
```

Steps (line, tactic):

Edges [i, j]:

## 26. `ProofNetIR.SequentialFigure7.tensorSibling_not_owned` (patterns)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7ActiveTopDebtParentEscapeTemporal.lean`, from line 546.

```lean
  544        ((premise = left ∧ sibling = right) ∨
  545          (premise = right ∧ sibling = left)) ∧
  546        sibling ∉ owned := by
  547    have linkMembership : Link.tensor left right conclusion ∈ certificate.links :=
  548      List.mem_of_getElem? linkLookup
  549    have premiseCases : premise = left ∨ premise = right := by
  550      simpa [Link.premises] using premiseMembership
  551    rcases premiseCases with premiseEq | premiseEq
  552    · subst premise
  553      refine ⟨right, Or.inl ⟨rfl, rfl⟩, ?_⟩
  554      intro rightOwned
  555      rcases occurrence.referencePath_within_owned premiseOwned rightOwned with
  556        ⟨path, pathStarts, pathFinishes, pathWithin⟩
  557      apply referenceAcyclic_no_tensorBypass structural acyclic linkMembership
  558        path pathStarts pathFinishes
  559      intro conclusionInPath
  560      exact conclusionNotOwned (pathWithin conclusion conclusionInPath)
  561    · subst premise
  562      refine ⟨left, Or.inr ⟨rfl, rfl⟩, ?_⟩
  563      intro leftOwned
  564      rcases occurrence.referencePath_within_owned leftOwned premiseOwned with
  565        ⟨path, pathStarts, pathFinishes, pathWithin⟩
  566      apply referenceAcyclic_no_tensorBypass structural acyclic linkMembership
  567        path pathStarts pathFinishes
  568      intro conclusionInPath
  569      exact conclusionNotOwned (pathWithin conclusion conclusionInPath)
  570  
  571  namespace CanonicalTagHistory
  572  
  573  /-- Exact tensor-specific residue after occurrence geometry and raw-mark
  574  history have been exhausted. The escaped source is anchored inside the
  575  active carrier, while both its tensor sibling and its tensor conclusion are
  576  outside.  Its concrete raw age resolves to the active sigma boundary, so the
  577  strict-older premise of `OlderMarkedTensorPredecessorInvariant` is unavailable
  578  for this occurrence. -/
  579  def ActiveCarrierTensorSameBoundaryResidual
  580      {certificate : Certificate} {state : ReservationState}
  581      {history : ExecutedHistory certificate state}
  582      (tagHistory : CanonicalTagHistory certificate history)
  583      (input : ReadyHeadInput state)
  584      (component : UnificationComponent) (owned : List Vertex) : Prop :=
  585    ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
  586        (storedLeft storedRight conclusion sibling : Vertex)
```

Steps (line, tactic):

Edges [i, j]:

## 27. `ProofNetIR.Graph.retainedIndex_injective_of_kept` (patterns)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Graph.lean`, from line 206.

```lean
  204      (secondKept : mask[second]? = some true)
  205      (same : retainedIndex mask first = retainedIndex mask second) :
  206      first = second := by
  207    rcases Nat.lt_trichotomy first second with less | equal | greater
  208    · have strict := retainedIndex_lt_of_lt_of_kept less firstKept
  209      omega
  210    · exact equal
  211    · have strict := retainedIndex_lt_of_lt_of_kept greater secondKept
  212      omega
  213  
  214  /-- Undirected adjacency induced by one stored edge. -/
  215  def Adjacent (graph : Graph) (left right : Vertex) : Prop :=
  216    ∃ edge ∈ graph.edges,
  217      (edge.first = left ∧ edge.second = right) ∨
  218      (edge.first = right ∧ edge.second = left)
  219  
  220  /-- One oriented occurrence of a stored multigraph edge. The list index keeps
  221  parallel equal-valued edges distinct, which vertex-only `Walk` deliberately
  222  does not do. -/
  223  structure DirectedEdge (graph : Graph) where
  224    index : Nat
  225    edge : Edge
  226    lookup : graph.edges[index]? = some edge
  227    forward : Bool
  228  
  229  namespace DirectedEdge
  230  
  231  def source {graph : Graph} (directed : graph.DirectedEdge) : Vertex :=
  232    if directed.forward then directed.edge.first else directed.edge.second
  233  
  234  def target {graph : Graph} (directed : graph.DirectedEdge) : Vertex :=
  235    if directed.forward then directed.edge.second else directed.edge.first
  236  
  237  def reverse {graph : Graph} (directed : graph.DirectedEdge) :
  238      graph.DirectedEdge where
  239    index := directed.index
  240    edge := directed.edge
  241    lookup := directed.lookup
  242    forward := !directed.forward
  243  
  244  @[simp] theorem reverse_source {graph : Graph}
  245      (directed : graph.DirectedEdge) :
  246      directed.reverse.source = directed.target := by
```

Steps (line, tactic):

Edges [i, j]:

## 28. `ProofNetIR.Certificate.restrictTo?_linksWellFormed` (patterns)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Sequentialization.lean`, from line 11300.

```lean
11298      (linksWellFormed : ∀ link ∈ certificate.links,
11299        certificate.LinkWellFormed link) :
11300      ∀ link ∈ restricted.links, restricted.LinkWellFormed link := by
11301    intro link membership
11302    rw [certificate.restrictTo?_links certificateEquation] at membership
11303    rcases List.mem_filterMap.mp membership with
11304      ⟨original, originalMembership, linkEquation⟩
11305    exact (linksWellFormed original originalMembership).restrictTo
11306      verticesInBounds boundaryContained certificateEquation linkEquation
11307  
11308  /-- All structural obligations for a restriction except per-occurrence source
11309  and parent ownership.  The omitted ownership field is where component closure
11310  is used by tensor splitting. -/
11311  theorem restrictTo?_structuralPrefix
11312      {certificate restricted : Certificate}
11313      {vertices boundary : List Vertex}
11314      (verticesInBounds : ∀ vertex ∈ vertices,
11315        vertex < certificate.formulas.size)
11316      (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
11317      (verticesNonempty : 0 < vertices.length)
11318      (boundaryNonempty : 0 < boundary.length)
11319      (boundaryNodup : boundary.Nodup)
11320      (linksWellFormed : ∀ link ∈ certificate.links,
11321        certificate.LinkWellFormed link)
11322      (certificateEquation :
11323        certificate.restrictTo? vertices boundary = some restricted) :
11324      0 < restricted.formulas.size ∧
11325        0 < restricted.conclusions.length ∧
11326        (∀ vertex ∈ restricted.conclusions,
11327          vertex < restricted.formulas.size) ∧
11328        restricted.conclusions.eraseDups.length =
11329          restricted.conclusions.length ∧
11330        (∀ link ∈ restricted.links, restricted.LinkWellFormed link) := by
11331    have formulasSize := certificate.restrictTo?_formulas_size certificateEquation
11332    have conclusionsLength :=
11333      certificate.restrictTo?_conclusions_length certificateEquation
11334    have conclusionsEquation := certificate.restrictTo?_conclusions
11335      verticesInBounds boundaryContained certificateEquation
11336    have localBoundaryNodup : (boundary.map vertices.idxOf).Nodup := by
11337      apply nodup_map_of_injective_on boundaryNodup
11338      intro first firstMembership second secondMembership same
11339      exact idxOf_injective_of_mem
11340        (boundaryContained first firstMembership)
```

Steps (line, tactic):

Edges [i, j]:

## 29. `ProofNetIR.Certificate.FullyCancellingDependencyCycleAllReflexive.flippedTaggedForwardParCuspState_exists` (patterns)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 39647.

```lean
39645                SchedulerTaggedForwardSearchTrace
39646                  certificate chainAt count flippedSegments
39647                  terminal (tagSchedulerFamily flippedSegments) := by
39648    rcases
39649        allReflexive.flippedParObstruction_exists
39650          correct positive closed with
39651      ⟨flippedSegments, segmentCount, flattenedNonempty,
39652        closedWalk, _cyclicReduced, cuspFree, closingCuspFree,
39653        indexedFlipped, allForwardKept, obstruction⟩
39654    have schedulerProvenance :
39655        ∀ directed,
39656          directed ∈ flippedSegments.flatten →
39657            ∃ step segment,
39658              step < count ∧
39659                flippedSegments[step]? = some segment ∧
39660                  directed ∈ segment ∧
39661                    QuiescentWaitingParDependencyFlippedTraversalAvoidsTargetLeft
39662                      certificate
39663                        (chainAt step) (chainAt (step + 1))
39664                          segment := by
39665      intro directed membership
39666      exact
39667        flippedSchedulerSegment_of_mem_flatten
39668          segmentCount indexedFlipped membership
39669    have schedulerLocated :
39670        SchedulerLocatedParObstruction
39671          certificate chainAt count flippedSegments
39672            flippedSegments.flatten :=
39673      obstruction.schedulerLocated
39674        schedulerProvenance prefixInjective
39675    have initialState :
39676        SchedulerCyclicParState
39677          certificate chainAt count flippedSegments
39678            flippedSegments.flatten :=
39679      ⟨chainAt 0, flattenedNonempty, closedWalk, cuspFree,
39680        closingCuspFree, allForwardKept, schedulerProvenance,
39681        obstruction, schedulerLocated⟩
39682    have initialTagged := initialState.taggedInitial
39683    rcases
39684        schedulerTaggedCyclicParState_forward_exists_traced
39685          segmentCount indexedFlipped correct prefixInjective initialTagged with
39686      ⟨terminal, terminalExact, forwardTrace⟩
39687    exact
```

Steps (line, tactic):

Edges [i, j]:

## 30. `ProofNetIR.SequentialFigure7.forward?_success_iff_enabled` (patterns)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7PriorityEnabled.lean`, from line 250.

```lean
  248        forward? certificate before invariant.toReservationInvariant =
  249          some after) ↔
  250        ForwardEnabled certificate before := by
  251    constructor
  252    · rintro ⟨after, equation⟩
  253      rcases
  254          (forward?_some_iff invariant.toReservationInvariant).mp equation with
  255        ⟨step⟩
  256      exact step.enabled
  257    · exact forward?_exists_of_enabled invariant
  258  
  259  /-- Existential arbitrary-payload unification executor success is exactly
  260  input-only `UnifyPayloadEnabled`, under the complete scheduler invariant. -/
  261  theorem unifyPayload?_success_iff_enabled
  262      {certificate : Certificate} {before : ReservationState}
  263      (invariant : SchedulerInvariant certificate before) :
  264      (∃ after,
  265        unifyPayload? certificate before invariant.toReservationInvariant =
  266          some after) ↔
  267        UnifyPayloadEnabled certificate before := by
  268    constructor
  269    · rintro ⟨after, equation⟩
  270      rcases
  271          (unifyPayload?_some_iff invariant.toReservationInvariant).mp
  272              equation with
  273        ⟨step⟩
  274      exact step.enabled
  275    · exact unifyPayload?_exists_of_enabled invariant
  276  
  277  private theorem executor_none_of_not_success
  278      {executor : Option α}
  279      (failure : ¬ ∃ output, executor = some output) : executor = none := by
  280    cases equation : executor with
  281    | none => rfl
  282    | some output => exact False.elim (failure ⟨output, equation⟩)
  283  
  284  /-- Exact fixed-precedence applicability classification for the canonical
  285  dispatcher.  Later constructors retain negations of every earlier branch.
  286  
  287  Every positive field and every stored earlier-branch negation is input-only. -/
  288  inductive PriorityEnabled (certificate : Certificate)
  289      (before : ReservationState)
  290      (invariant : SchedulerInvariant certificate before) :
```

Steps (line, tactic):

Edges [i, j]:

## 31. `ProofNetIR.CutFreeDerivation.reorder?_exists_of_map_eq_some` (alternatives)

Source: `.lake/packages/proofnet-ir/ProofNetIR/DerivationTree.lean`, from line 477.

```lean
  475      ∃ reordered : List α,
  476        reorder? values order = some reordered ∧
  477          reordered.map function = mapped := by
  478    rw [reorder?_eq_reorderCandidate?] at accepted ⊢
  479    rw [reorderCandidate?_map] at accepted
  480    cases candidate : reorderCandidate? values order with
  481    | none => simp [candidate] at accepted
  482    | some reordered =>
  483        simp [candidate] at accepted
  484        subst mapped
  485        exact ⟨reordered, rfl, rfl⟩
  486  
  487  /-- A par rule focused on the final two occurrences has the expected
  488  right-boundary sequent, independently of the size of the preceding context. -/
  489  theorem infer?_parLast
  490      {premise : CutFreeDerivation} {context : List Formula}
  491      {left right : Formula}
  492      (premiseInference : premise.infer? = some (context ++ [left, right])) :
  493      (CutFreeDerivation.par context.length context.length premise).infer? =
  494        some (context ++ [.par left right]) := by
  495    simp [infer?, premiseInference, pick?_append_cons]
  496  
  497  /-- Tensor focused on the final occurrence of each premise produces the
  498  tensor formula followed by the two untouched contexts. -/
  499  theorem infer?_tensorLast
  500      {leftTree rightTree : CutFreeDerivation}
  501      {leftContext rightContext : List Formula}
  502      {left right : Formula}
  503      (leftInference : leftTree.infer? = some (leftContext ++ [left]))
  504      (rightInference : rightTree.infer? = some (rightContext ++ [right])) :
  505      (CutFreeDerivation.tensor leftContext.length rightContext.length
  506        leftTree rightTree).infer? =
  507        some (.tensor left right :: (leftContext ++ rightContext)) := by
  508    simp [infer?, leftInference, rightInference, pick?_append_cons]
  509  
  510  /-- Successful first-order inference denotes a genuine kernel-typed derivation
  511  in the independent `Derivation` sequent calculus. -/
  512  theorem infer?_sound {tree : CutFreeDerivation} {sequent : List Formula}
  513      (accepted : tree.infer? = some sequent) :
  514      Nonempty (Derivation sequent) := by
  515    induction tree generalizing sequent with
  516    | «axiom» name positive =>
  517        simp [infer?] at accepted
```

Steps (line, tactic):

Edges [i, j]:

## 32. `ProofNetIR.SequentialFigure7.MarkedConclusionChain.terminalComparable` (alternatives)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7MarkedTargetRawReturnSiblingExitOpen.lean`, from line 99.

```lean
   97      (secondChain : MarkedConclusionChain certificate state origin second) :
   98      MarkedConclusionChain certificate state first second ∨
   99        MarkedConclusionChain certificate state second first := by
  100    induction firstChain generalizing second with
  101    | refl vertex => exact Or.inl secondChain
  102    | @step vertex terminal rawAge firstConsumer firstMarked firstNotGlobal
  103        firstTail induction =>
  104        cases secondChain with
  105        | refl =>
  106            exact Or.inr (.step firstConsumer firstMarked firstNotGlobal firstTail)
  107        | @step _ secondTerminal secondAge secondConsumer secondMarked
  108            secondNotGlobal secondTail =>
  109            have conclusionEq :
  110                firstConsumer.conclusion = secondConsumer.conclusion :=
  111              connectiveBelowConclusionEq firstConsumer secondConsumer
  112            have secondTail' :
  113                MarkedConclusionChain certificate state firstConsumer.conclusion
  114                  second := by
  115              rw [conclusionEq]
  116              exact secondTail
  117            exact induction secondTail'
  118  
  119  /-- A continuation exit whose endpoint remains open: either a raw opposite
  120  premise or scheduled conclusion work. -/
  121  inductive ContinuationExitRawOrFuture (certificate : Certificate)
  122      (state : ReservationState) (origin : Vertex) : Prop where
  123    | rawMate {terminal : Vertex}
  124        (chain : MarkedConclusionChain certificate state origin terminal)
  125        (consumer : ConnectiveBelow certificate terminal)
  126        (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
  127        ContinuationExitRawOrFuture certificate state origin
  128    | futureConclusion {terminal : Vertex}
  129        (chain : MarkedConclusionChain certificate state origin terminal)
  130        (consumer : ConnectiveBelow certificate terminal)
  131        (boundary : RawTokenAge)
  132        (work : FutureWorkAt state boundary consumer.conclusion) :
  133        ContinuationExitRawOrFuture certificate state origin
  134  
  135  private theorem selectedPremise_not_marked
  136      {certificate : Certificate} {state : ReservationState}
  137      {history : ExecutedHistory certificate state}
  138      (tagHistory : CanonicalTagHistory certificate history)
  139      (input : ReadyHeadInput state)
```

Steps (line, tactic):

Edges [i, j]:

## 33. `ProofNetIR.Certificate.list_mapM_eq_some_map_of_forall` (alternatives)

Source: `.lake/packages/proofnet-ir/ProofNetIR/ExecutableSequentialization.lean`, from line 94.

```lean
   92      (values : List α) (function : α → Option β) (result : α → β)
   93      (defined : ∀ value ∈ values, function value = some (result value)) :
   94      values.mapM function = some (values.map result) := by
   95    induction values with
   96    | nil => rfl
   97    | cons head tail ih =>
   98        have headDefined := defined head (by simp)
   99        have tailDefined : ∀ value ∈ tail,
  100            function value = some (result value) := by
  101          intro value membership
  102          exact defined value (by simp [membership])
  103        simp [headDefined, ih tailDefined]
  104  
  105  /-- A bounded bijection permutes the complete finite vertex range even when
  106  written in inverse-image order. -/
  107  private theorem vertexRenaming_inverse_range_perm {bound : Nat}
  108      (vertexMap : VertexRenaming bound) :
  109      (List.range bound).map vertexMap.inverse |>.Perm (List.range bound) := by
  110    apply VertexRenaming.perm_range_of_nodup_complete
  111    · exact nodup_map_of_injective vertexMap.inverse
  112        vertexMap.symm.forward_injective (List.range bound) List.nodup_range
  113    · intro vertex
  114      constructor
  115      · intro inBounds
  116        apply List.mem_map.mpr
  117        refine ⟨vertexMap.forward vertex, ?_, vertexMap.inverse_forward vertex⟩
  118        simp [(vertexMap.forward_lt_iff vertex).mpr inBounds]
  119      · intro membership
  120        rcases List.mem_map.mp membership with
  121          ⟨image, imageInRange, same⟩
  122        have imageInBounds : image < bound := by simpa using imageInRange
  123        rw [← same]
  124        exact (vertexMap.inverse_lt_iff image).mpr imageInBounds
  125  
  126  /-- Reading the source formula array in inverse-image order returns exactly
  127  the reindexed formula array. -/
  128  theorem reindexFormulaOrder_lookup (certificate : Certificate)
  129      (vertexMap : VertexRenaming certificate.formulas.size) :
  130      ((List.range certificate.formulas.size).map vertexMap.inverse).mapM
  131          (fun index => certificate.formulas.toList[index]?) =
  132        some (certificate.reindex vertexMap).formulas.toList := by
  133    let source := certificate.formulas.toList
  134    let target := (certificate.reindex vertexMap).formulas.toList
```

Steps (line, tactic):

Edges [i, j]:

## 34. `ExteriorAlgebra.ιMulti_span` (alternatives)

Source: `.lake/packages/mathlib/Mathlib/LinearAlgebra/ExteriorAlgebra/Grading.lean`, from line 87.

```lean
   85  all natural numbers spans the exterior algebra. -/
   86  lemma ιMulti_span :
   87      Submodule.span R (Set.range fun x : Σ n, (Fin n → M) => ιMulti R x.1 x.2) = ⊤ := by
   88    rw [Submodule.eq_top_iff']
   89    intro x
   90    induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
   91    | zero => exact Submodule.zero_mem _
   92    | add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
   93    | homogeneous hm =>
   94      let ⟨m, hm⟩ := hm
   95      apply Set.mem_of_mem_of_subset hm
   96      rw [← ιMulti_span_fixedDegree]
   97      refine Submodule.span_mono fun _ hx ↦ ?_
   98      obtain ⟨y, rfl⟩ := hx
   99      exact ⟨⟨_, y⟩, rfl⟩
  100  
  101  end ExteriorAlgebra
  102  
```

Steps (line, tactic):

Edges [i, j]:

## 35. `ProofNetIR.Certificate.runUnificationWorklist_preserves_assigned` (alternatives)

Source: `.lake/packages/proofnet-ir/ProofNetIR/Unification.lean`, from line 13508.

```lean
13506      (marked : state.core.assignedToken? vertex ≠ none) :
13507      ((runUnificationWorklist certificate consumers fuel state).state.core
13508        |>.assignedToken? vertex) ≠ none := by
13509    induction fuel generalizing state with
13510    | zero =>
13511        simpa [runUnificationWorklist] using marked
13512    | succ fuel induction =>
13513        cases popEquation : popWorklist? state with
13514        | none =>
13515            simpa [runUnificationWorklist, popEquation] using marked
13516        | some result =>
13517            rcases result with ⟨index, popped⟩
13518            have poppedCore : popped.core = state.core :=
13519              popWorklist?_success_core popEquation
13520            have poppedMarked :
13521                popped.core.assignedToken? vertex ≠ none := by
13522              simpa [poppedCore] using marked
13523            have poppedInvariant :
13524                WorklistCoreInvariant certificate popped := by
13525              unfold WorklistCoreInvariant at invariant ⊢
13526              simpa [poppedCore] using invariant
13527            have processedMarked :
13528                ((processWorklistLink certificate consumers index popped).core
13529                    |>.assignedToken? vertex) ≠ none :=
13530              processWorklistLink_preserves_assigned
13531                structural poppedInvariant.1 poppedMarked
13532            have processedInvariant :
13533                WorklistCoreInvariant certificate
13534                  (processWorklistLink certificate consumers
13535                    index popped) :=
13536              processWorklistLink_coreInvariant
13537                structural poppedInvariant
13538            simpa [runUnificationWorklist, popEquation] using
13539              induction
13540                (state :=
13541                  processWorklistLink certificate consumers index popped)
13542                processedInvariant processedMarked
13543  
13544  /-- The exact production scheduler preserves its complete invariant through
13545  every finite fuel prefix, including early quiescence and conservative fuel
13546  exhaustion. -/
13547  private theorem runUnificationWorklist_runInvariant
13548      (certificate : Certificate)
```

Steps (line, tactic):

Edges [i, j]:

## 36. `RCLike.exists_norm_eq_mul_self` (nested-by)

Source: `.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean`, from line 516.

```lean
  514  
  515  --TODO: Do we rather want the map as an explicit definition?
  516  lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  517    obtain rfl | hx := eq_or_ne x 0
  518    · exact ⟨1, by simp⟩
  519    · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩
  520  
  521  lemma exists_norm_mul_eq_self (x : K) : ∃ c, ‖c‖ = 1 ∧ c * ‖x‖ = x := by
  522    obtain rfl | hx := eq_or_ne x 0
  523    · exact ⟨1, by simp⟩
  524    · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩
  525  
  526  @[rclike_simps, norm_cast]
  527  theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  528    map_div₀ (algebraMap ℝ K) r s
  529  
  530  theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  531    rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, re_ofReal_mul]
  532  
  533  @[rclike_simps, norm_cast]
  534  theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  535    map_zpow₀ (algebraMap ℝ K) r n
  536  
  537  theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  538    I_mul_I_ax.resolve_left
  539  
  540  @[simp, rclike_simps]
  541  theorem inv_I : (I : K)⁻¹ = -I := by
  542    by_cases h : (I : K) = 0
  543    · simp [h]
  544    · field_simp
  545      linear_combination I_mul_I_of_nonzero h
  546  
  547  @[simp, rclike_simps]
  548  theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]
  549  
  550  -- Not `@[simp]` since `simp` can prove this.
  551  @[rclike_simps]
  552  theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  553    map_inv₀ normSq z
  554  
  555  -- Not `@[simp]` since `simp` can prove this.
  556  @[rclike_simps]
```

Steps (line, tactic):

Edges [i, j]:

## 37. `ProofNetIR.SequentialFigure7.UnifyEmptyStep.map_sum_set_balance` (nested-by)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialSchedulerInvariant.lean`, from line 5683.

```lean
 5681      (lookup : values[index]? = some oldValue) :
 5682      ((values.set index newValue).map weight).sum + weight oldValue =
 5683        (values.map weight).sum + weight newValue := by
 5684    induction values generalizing index with
 5685    | nil => simp at lookup
 5686    | cons head tail induction =>
 5687        cases index with
 5688        | zero =>
 5689            have headEq : head = oldValue := by simpa using lookup
 5690            subst head
 5691            simp
 5692            omega
 5693        | succ prior =>
 5694            simp only [List.getElem?_cons_succ] at lookup
 5695            simp only [List.set, List.map_cons, List.sum_cons]
 5696            have inner := induction lookup
 5697            omega
 5698  
 5699  private theorem map_sum_set_merge_clear
 5700      {alpha : Type} {values : List alpha}
 5701      {survivor retired : Nat}
 5702      {survivorValue retiredValue mergedValue clearedValue : alpha}
 5703      (weight : alpha → Nat)
 5704      (different : survivor ≠ retired)
 5705      (survivorLookup : values[survivor]? = some survivorValue)
 5706      (retiredLookup : values[retired]? = some retiredValue)
 5707      (clearedWeight : weight clearedValue = 0)
 5708      (mergedWeight :
 5709        weight mergedValue =
 5710          weight survivorValue + weight retiredValue + 1) :
 5711      ((((values.set survivor mergedValue).set retired clearedValue).map
 5712          weight).sum) =
 5713        (values.map weight).sum + 1 := by
 5714    have retiredAfter :
 5715        (values.set survivor mergedValue)[retired]? =
 5716          some retiredValue := by
 5717      rw [List.getElem?_set_ne different]
 5718      exact retiredLookup
 5719    have first := map_sum_set_balance weight survivorLookup
 5720      (newValue := mergedValue)
 5721    have second := map_sum_set_balance weight retiredAfter
 5722      (newValue := clearedValue)
 5723    rw [clearedWeight] at second
```

Steps (line, tactic):

Edges [i, j]:

## 38. `RCLike.lipschitzWith_im` (nested-by)

Source: `.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean`, from line 1204.

```lean
 1202    _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)
 1203  
 1204  lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
 1205    intro x y
 1206    simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
 1207    calc ‖im x - im y‖ₑ
 1208    _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
 1209    _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)
 1210  
 1211  /-- The canonical map between `RCLike` types. It maps `x : 𝕜` to `re x + im x * I`. -/
 1212  @[simps] def map (𝕜 𝕜' : Type*) [RCLike 𝕜] [RCLike 𝕜'] : 𝕜 →L[ℝ] 𝕜' where
 1213    toFun x := re x + im x * (I : 𝕜')
 1214    map_add' _ _ := by simp only [map_add, add_mul]; ring
 1215    map_smul' _ _ := by simp [real_smul_eq_coe_mul, mul_assoc]
 1216  
 1217  @[simp] theorem map_same_eq_id : map K K = .id ℝ K := by ext; simp
 1218  
 1219  @[simp] theorem map_to_real : map K ℝ = reCLM := by
 1220    ext; simp only [map_apply, I, mul_zero, add_zero]; rfl
 1221  
 1222  @[simp] theorem map_from_real : map ℝ K = ofRealCLM := by ext; simp
 1223  
 1224  open scoped ComplexOrder in
 1225  lemma instOrderClosedTopology : OrderClosedTopology K where
 1226    isClosed_le' := by
 1227      conv in _ ≤ _ => rw [RCLike.le_iff_re_im]
 1228      simp_rw [Set.setOf_and]
 1229      refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> fun_prop
 1230  
 1231  scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosedTopology
 1232  
 1233  end LinearMaps
 1234  
 1235  /-!
 1236  ### ℝ-dependent results
 1237  
 1238  Here we gather results that depend on whether `K` is `ℝ`.
 1239  -/
 1240  section CaseSpecific
 1241  
 1242  lemma im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0 := by
 1243    rw [← re_add_im z, h]
 1244    simp
```

Steps (line, tactic):

Edges [i, j]:

## 39. `ProofNetIR.Certificate.referenceSwitchingGraph_connected_eq_true_iff` (nested-by)

Source: `.lake/packages/proofnet-ir/ProofNetIR/AcyclicDecision.lean`, from line 510.

```lean
  508      (structural : certificate.StructurallyWellFormed) :
  509      certificate.referenceSwitchingGraph.connected = true ↔
  510        certificate.ReferenceSwitchingConnected := by
  511    apply certificate.referenceSwitchingGraph.connected_iff_connected
  512    have aligned :
  513        certificate.fullGraph.edges.length =
  514          certificate.referenceSwitchingMask.length := by
  515      change (linkFullEdges certificate.links).length =
  516        certificate.referenceSwitchingMask.length
  517      exact certificate.referenceFullSwitchingSelection.mask_length.symm
  518    simpa [referenceSwitchingGraph] using
  519      structural.fullGraph_bounded.retainEdges aligned
  520  
  521  /-- The compact specification checker accepts exactly the same certificates
  522  as the original all-switchings checker. -/
  523  theorem compactCheck_eq_true_iff_check (certificate : Certificate) :
  524      certificate.compactCheck = true ↔ certificate.check = true := by
  525    constructor
  526    · intro accepted
  527      have parts :
  528          (certificate.wellFormed = true ∧
  529            certificate.isCuspAcyclic = true) ∧
  530            certificate.referenceSwitchingGraph.connected = true := by
  531        simpa only [compactCheck, Bool.and_eq_true] using accepted
  532      have structural : certificate.StructurallyWellFormed :=
  533        certificate.wellFormed_iff_structurallyWellFormed.mp parts.1.1
  534      have cuspAcyclic : certificate.CuspAcyclic :=
  535        certificate.isCuspAcyclic_eq_true_iff.mp parts.1.2
  536      have referenceConnected : certificate.ReferenceSwitchingConnected :=
  537        (certificate.referenceSwitchingGraph_connected_eq_true_iff
  538          structural).mp parts.2
  539      exact
  540        certificate.check_iff_structural_cuspAcyclic_referenceConnected.mpr
  541          ⟨structural, cuspAcyclic, referenceConnected⟩
  542    · intro accepted
  543      have semantic :=
  544        certificate.check_iff_structural_cuspAcyclic_referenceConnected.mp
  545          accepted
  546      have wellFormed : certificate.wellFormed = true :=
  547        certificate.wellFormed_iff_structurallyWellFormed.mpr semantic.1
  548      have cuspAccepted : certificate.isCuspAcyclic = true :=
  549        certificate.isCuspAcyclic_eq_true_iff.mpr semantic.2.1
  550      have referenceAccepted :
```

Steps (line, tactic):

Edges [i, j]:

## 40. `ProofNetIR.SequentialFigure7.CanonicalTagHistory.unify_before_sigma_eq_after_append_active` (nested-by)

Source: `.lake/packages/proofnet-ir/ProofNetIR/SequentialFigure7CommitmentSpine.lean`, from line 136.

```lean
  134      (step : UnifyPayloadStep certificate before after) :
  135      before.stack.sigma =
  136        after.stack.sigma ++ [step.mergeStep.activeBoundary] := by
  137    have middleSigma :
  138        step.prepared.after.stack.sigma =
  139          step.mergeStep.sigmaPrefix ++
  140            [step.previousBoundary, step.mergeStep.activeBoundary] := by
  141      simpa [PreparedStep.after] using step.mergeStep.sigma_eq
  142    have beforeSigma :
  143        before.stack.sigma =
  144          step.mergeStep.sigmaPrefix ++
  145            [step.previousBoundary, step.mergeStep.activeBoundary] :=
  146      (prepared_sigma_eq_before step.prepared).symm.trans middleSigma
  147    have outputStack : after.stack = step.stackAfter :=
  148      congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  149    have afterSigma :
  150        after.stack.sigma =
  151          step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  152      calc
  153        after.stack.sigma = step.stackAfter.sigma :=
  154          congrArg (fun stack : SequentialStackState ↦ stack.sigma)
  155            outputStack
  156        _ = step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  157          simpa using congrArg
  158            (fun stack : SequentialStackState ↦ stack.sigma)
  159            step.mergeStep.after_eq
  160    rw [beforeSigma, afterSigma]
  161    simp [List.append_assoc]
  162  
  163  private theorem empty_commitmentSpine :
  164      (CanonicalTagHistory.empty
  165        (certificate := certificate)).CommitmentSpine := by
  166    intro position parent child _first second
  167    have bound := (List.getElem?_eq_some_iff.mp second).choose
  168    simp [ReservationState.empty, SequentialStackState.empty] at bound
  169  
  170  private theorem init_commitmentSpine
  171      {certificate : Certificate} {after : ReservationState} {start : Vertex}
  172      (step : InitialReservationStep certificate after start) :
  173      (CanonicalTagHistory.init step).CommitmentSpine := by
  174    intro position parent child _first second
  175    rcases SequentialStackState.initEnqueue?_exact step.stack_eq with
  176      ⟨_marks, _nextAge, sigma, _ready, _waiting, _activeUndefined⟩
```

Steps (line, tactic):

Edges [i, j]:

