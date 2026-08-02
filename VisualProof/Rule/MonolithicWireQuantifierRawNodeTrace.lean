import VisualProof.Rule.MonolithicWireQuantifierRawRegionTrace

namespace VisualProof

namespace MonolithicWireQuantifier

open _root_.VisualProof.ConcreteWireQuantifier

section RawNodeTrace

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- Cast a prefix target back to the exact prior node carrier owned by a
checked construction snoc. -/
def priorNodeCast
    {current : CheckedDiagram definitions}
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current) :
    current.val.NodeId → step.prior.val.NodeId :=
  cast (congrArg (fun diagram : CheckedDiagram definitions =>
    diagram.val.NodeId) priorExact.symm)

/-- One construction-owned ordered node ledger together with the exact
checked carrier length needed to read it by a checked node identifier. -/
structure NodeLedger {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) : Type where
  rows : List (RelationJoinPrefixNodeOrigin (source := source)
    (dying := dying) (content := content) steps)
  length_exact : rows.length = final.val.nodeCount

/-- The sole ordered node-placement authority.  Every snoc reads retained
prior rows in dense-erasure target order, then appends copied content nodes
and generated request nodes in checked allocation order. -/
def nodeLedger {args : List Sig} :
    ∀ {steps : List (RelationJoinStep source dying content)}
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      (trace : RelationJoinConstructionTrace source dying content parameters
        args steps final finalRegionImage finalNodeImage finalWireImage
          finalDying finalScope) → NodeLedger trace
  | _, _, _, _, _, _, _, .nil =>
      { rows := source.val.nodesList.map Sum.inl
        length_exact := by
          simp [ConcreteDiagram.nodesList,
            Data.Finite.allFin_eq_finRange] }
  | _, _, _, _, _, _, _,
      .snoc (steps := priorSteps) trace step priorExact
        priorRegionImageExact priorNodeImageExact
        priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact =>
      let prior := nodeLedger trace
      by
        subst priorExact
        cases eq_of_heq priorRegionImageExact
        cases eq_of_heq priorNodeImageExact
        cases eq_of_heq priorWireImageExact
        cases eq_of_heq priorDyingExact
        cases eq_of_heq priorScopeExact
        cases relationArgsExact
        let retained :=
          ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
            [step.priorApplication]
        let retainedRows := retained.map fun target =>
          prefixNodeOriginLift step
            (prior.rows.get (Fin.cast prior.length_exact.symm target))
        let contentRows := content.val.diagram.nodesList.map
          (prefixNodeFreshContentOrigin (steps := priorSteps) step)
        let requestRows :=
          (Data.Finite.allFin
            step.attachment.identityRequests.length).map
              (prefixNodeFreshRequestOrigin (steps := priorSteps) step)
        refine
          { rows := retainedRows ++ contentRows ++ requestRows
            length_exact := ?_ }
        have retainedCount : retained.length + 1 =
            step.prior.val.nodeCount := by
          exact Data.Finite.filter_not_mem_length_add_removed_length
            [step.priorApplication] (by simp)
        have checkedCount := step.checked_nodeCount_add_one
        simp only [retainedRows, contentRows, requestRows, List.length_append,
          List.length_map, ConcreteDiagram.nodesList,
          Data.Finite.allFin_eq_finRange, List.length_finRange]
        omega
termination_by steps _ _ _ _ _ _ _ => steps.length

/-- Exact recursive construction node origins. -/
def relationJoinConstructionNodeOrigins {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    List (RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps) :=
  (nodeLedger trace).rows

theorem relationJoinConstructionNodeOrigins_length {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    (relationJoinConstructionNodeOrigins trace).length =
      final.val.nodeCount :=
  (nodeLedger trace).length_exact

/-- A Type-valued exact-row witness.  It introduces no placement choice: its
only field reads the authoritative construction ledger at the checked target. -/
structure PrefixNodeLands {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (target : final.val.NodeId) : Type where
  exact : (relationJoinConstructionNodeOrigins trace).get
      (Fin.cast (relationJoinConstructionNodeOrigins_length trace).symm
        target) = origin

/-- Exact retained-prior row lookup for one checked construction snoc. -/
theorem relationJoinConstructionNodeOrigins_get_checkedPriorNode
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    {currentRegionImage : source.val.RegionId → current.val.RegionId}
    {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
    {currentWireImage : source.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps current currentRegionImage currentNodeImage currentWireImage
        currentDying currentScope)
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current)
    (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
    (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (step.priorRegionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (node : current.val.NodeId)
    (different : priorNodeCast step priorExact node ≠ step.priorApplication) :
    (relationJoinConstructionNodeOrigins
      (.snoc trace step priorExact priorRegionImageExact priorNodeImageExact
        priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact)).get
      (Fin.cast
        (relationJoinConstructionNodeOrigins_length
          (.snoc trace step priorExact priorRegionImageExact
            priorNodeImageExact priorWireImageExact priorDyingExact
            priorScopeExact relationArgsExact sourceParametersExact)).symm
        (step.checkedPriorNode (priorNodeCast step priorExact node) different)) =
      prefixNodeOriginLift step
        ((relationJoinConstructionNodeOrigins trace).get
          (Fin.cast (relationJoinConstructionNodeOrigins_length trace).symm
            node)) := by
  subst priorExact
  cases eq_of_heq priorRegionImageExact
  cases eq_of_heq priorNodeImageExact
  cases eq_of_heq priorWireImageExact
  cases eq_of_heq priorDyingExact
  cases eq_of_heq priorScopeExact
  cases relationArgsExact
  cases sourceParametersExact
  cases Subsingleton.elim priorRegionImageExact HEq.rfl
  cases Subsingleton.elim priorNodeImageExact HEq.rfl
  cases Subsingleton.elim priorWireImageExact HEq.rfl
  cases Subsingleton.elim priorDyingExact HEq.rfl
  cases Subsingleton.elim priorScopeExact HEq.rfl
  have castNode : priorNodeCast step rfl node = node := by
    apply Fin.ext
    rfl
  have different' : node ≠ step.priorApplication := by
    simpa [castNode] using different
  let retained := ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
    [step.priorApplication]
  have member : node ∈ retained := by
    simp [retained, ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, different']
  have targetValue :
      (step.checkedPriorNode node different').val =
        (DenseList.index retained node member).val := by
    simp only [RelationJoinStep.checkedPriorNode_val]
    rfl
  have rowExact := DenseList.get_index retained node member
  simp only [relationJoinConstructionNodeOrigins, nodeLedger]
  simp [retained, targetValue,
    relationJoinConstructionNodeOrigins_length] at rowExact ⊢
  simp [castNode, nodeLedger, retained, targetValue] at rowExact ⊢
  exact congrArg (prefixNodeOriginLift step)
    (congrArg (fun target =>
      (nodeLedger trace).rows.get
        (Fin.cast (nodeLedger trace).length_exact.symm target)) rowExact)

/-- Exact copied-content row lookup for one checked construction snoc. -/
theorem relationJoinConstructionNodeOrigins_get_checkedFragmentNode
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    {currentRegionImage : source.val.RegionId → current.val.RegionId}
    {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
    {currentWireImage : source.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps current currentRegionImage currentNodeImage currentWireImage
        currentDying currentScope)
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current)
    (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
    (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (step.priorRegionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (node : content.val.diagram.NodeId) :
    (relationJoinConstructionNodeOrigins
      (.snoc trace step priorExact priorRegionImageExact priorNodeImageExact
        priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact)).get
      (Fin.cast
        (relationJoinConstructionNodeOrigins_length
          (.snoc trace step priorExact priorRegionImageExact
            priorNodeImageExact priorWireImageExact priorDyingExact
            priorScopeExact relationArgsExact sourceParametersExact)).symm
        (step.checkedFragmentNode node)) =
      prefixNodeFreshContentOrigin step node := by
  subst priorExact
  cases eq_of_heq priorRegionImageExact
  cases eq_of_heq priorNodeImageExact
  cases eq_of_heq priorWireImageExact
  cases eq_of_heq priorDyingExact
  cases eq_of_heq priorScopeExact
  cases relationArgsExact
  cases sourceParametersExact
  cases Subsingleton.elim priorRegionImageExact HEq.rfl
  cases Subsingleton.elim priorNodeImageExact HEq.rfl
  cases Subsingleton.elim priorWireImageExact HEq.rfl
  cases Subsingleton.elim priorDyingExact HEq.rfl
  cases Subsingleton.elim priorScopeExact HEq.rfl
  let retained := ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
    [step.priorApplication]
  have retainedCount : retained.length + 1 = step.prior.val.nodeCount := by
    exact Data.Finite.filter_not_mem_length_add_removed_length
      [step.priorApplication] (by simp)
  have baseCount : step.base.val.nodeCount = retained.length := by
    have baseExact := step.base_nodeCount_add_one
    omega
  simp [relationJoinConstructionNodeOrigins, nodeLedger, retained, baseCount,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange]

/-- Exact generated-request row lookup for one checked construction snoc. -/
theorem relationJoinConstructionNodeOrigins_get_checkedIdentityNode
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    {currentRegionImage : source.val.RegionId → current.val.RegionId}
    {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
    {currentWireImage : source.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps current currentRegionImage currentNodeImage currentWireImage
        currentDying currentScope)
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current)
    (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
    (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (step.priorRegionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (request : Fin step.attachment.identityRequests.length) :
    (relationJoinConstructionNodeOrigins
      (.snoc trace step priorExact priorRegionImageExact priorNodeImageExact
        priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact)).get
      (Fin.cast
        (relationJoinConstructionNodeOrigins_length
          (.snoc trace step priorExact priorRegionImageExact
            priorNodeImageExact priorWireImageExact priorDyingExact
            priorScopeExact relationArgsExact sourceParametersExact)).symm
        (step.checkedIdentityNode request)) =
      prefixNodeFreshRequestOrigin step request := by
  subst priorExact
  cases eq_of_heq priorRegionImageExact
  cases eq_of_heq priorNodeImageExact
  cases eq_of_heq priorWireImageExact
  cases eq_of_heq priorDyingExact
  cases eq_of_heq priorScopeExact
  cases relationArgsExact
  cases sourceParametersExact
  cases Subsingleton.elim priorRegionImageExact HEq.rfl
  cases Subsingleton.elim priorNodeImageExact HEq.rfl
  cases Subsingleton.elim priorWireImageExact HEq.rfl
  cases Subsingleton.elim priorDyingExact HEq.rfl
  cases Subsingleton.elim priorScopeExact HEq.rfl
  let retained := ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
    [step.priorApplication]
  have retainedCount : retained.length + 1 = step.prior.val.nodeCount := by
    exact Data.Finite.filter_not_mem_length_add_removed_length
      [step.priorApplication] (by simp)
  have baseCount : step.base.val.nodeCount = retained.length := by
    have baseExact := step.base_nodeCount_add_one
    omega
  simp [relationJoinConstructionNodeOrigins, nodeLedger, retained, baseCount,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange]
  rw [List.getElem_append_right (by
    simp only [List.length_map]
    omega)]
  rw [List.getElem_append_right (by
    simp only [List.length_map, List.length_finRange]
    omega)]
  rw [List.getElem_map]
  congr 1
  apply Fin.ext
  simp only [List.getElem_finRange, Fin.val_cast, Fin.val_mk,
    List.length_map, List.length_finRange]
  omega

private theorem get_injective_of_nodup [DecidableEq α]
    {values : List α} (nodup : values.Nodup) :
    Function.Injective values.get := by
  intro left right same
  apply Fin.ext
  have valuesSame : values[left.val]? = values[right.val]? := by
    rw [List.getElem?_eq_getElem left.isLt,
      List.getElem?_eq_getElem right.isLt]
    exact congrArg some same
  exact (List.getElem?_inj left.isLt nodup).mp valuesSame

private theorem map_nodup_of_injective
    {values : List α} (nodup : values.Nodup) (function : α → β)
    (injective : Function.Injective function) :
    (values.map function).Nodup := by
  induction nodup with
  | nil => simp
  | @cons head tail headFresh tailNodup induction =>
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, induction⟩
      intro headMember
      rcases List.mem_map.mp headMember with ⟨value, valueMember, same⟩
      have valueExact := injective same
      exact (headFresh value valueMember) valueExact.symm

/-- Every checked target has a distinct row in the sole ordered node ledger. -/
theorem relationJoinConstructionNodeOrigins_nodup {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    (relationJoinConstructionNodeOrigins trace).Nodup := by
  classical
  induction trace with
  | nil =>
      have sourceNodup : source.val.nodesList.Nodup :=
        Data.Finite.allFin_nodup _
      have mappedNodup := map_nodup_of_injective sourceNodup
        (fun node => (Sum.inl node :
        RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
          (content := content) [])) (by
            intro left right same
            exact Sum.inl.inj same)
      simpa [relationJoinConstructionNodeOrigins, nodeLedger] using mappedNodup
  | @snoc priorSteps current currentRegionImage currentNodeImage currentWireImage
      currentDying currentScope trace step priorExact priorRegionImageExact
      priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      cases Subsingleton.elim priorRegionImageExact HEq.rfl
      cases Subsingleton.elim priorNodeImageExact HEq.rfl
      cases Subsingleton.elim priorWireImageExact HEq.rfl
      cases Subsingleton.elim priorDyingExact HEq.rfl
      cases Subsingleton.elim priorScopeExact HEq.rfl
      let retained := ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
        [step.priorApplication]
      let retainedRows := retained.map fun target =>
        prefixNodeOriginLift step
          ((nodeLedger trace).rows.get
            (Fin.cast (nodeLedger trace).length_exact.symm target))
      let contentRows := content.val.diagram.nodesList.map
        (prefixNodeFreshContentOrigin (steps := priorSteps) step)
      let requestRows :=
        (Data.Finite.allFin step.attachment.identityRequests.length).map
          (prefixNodeFreshRequestOrigin (steps := priorSteps) step)
      have retainedNodup : retained.Nodup := by
        exact (Data.Finite.allFin_nodup _).filter _
      have retainedRowsNodup : retainedRows.Nodup := by
        apply retainedNodup.map _
        intro left right different same
        apply different
        have priorSame := prefixNodeOriginLift_injective step same
        have targetSame := get_injective_of_nodup induction priorSame
        apply Fin.ext
        simpa using congrArg Fin.val targetSame
      have contentRowsNodup : contentRows.Nodup := by
        exact (Data.Finite.allFin_nodup _).map _ (by
          intro left right different same
          exact different (prefixNodeFreshContent_injective step same))
      have requestRowsNodup : requestRows.Nodup := by
        exact (Data.Finite.allFin_nodup _).map _ (by
          intro left right different same
          exact different (prefixNodeFreshRequest_injective step same))
      simp only [relationJoinConstructionNodeOrigins, nodeLedger]
      change (retainedRows ++ contentRows ++ requestRows).Nodup
      rw [List.nodup_append]
      refine ⟨?_, requestRowsNodup, ?_⟩
      · rw [List.nodup_append]
        refine ⟨retainedRowsNodup, contentRowsNodup, ?_⟩
        intro priorOrigin priorMember contentOrigin contentMember same
        rcases List.mem_map.mp priorMember with ⟨target, _, rfl⟩
        rcases List.mem_map.mp contentMember with ⟨node, _, rfl⟩
        exact prefixNodeOriginLift_ne_freshContent step _ node same
      · intro priorOrigin priorMember requestOrigin requestMember same
        rcases List.mem_map.mp requestMember with ⟨request, _, rfl⟩
        rcases List.mem_append.mp priorMember with retainedMember | contentMember
        · rcases List.mem_map.mp retainedMember with ⟨target, _, rfl⟩
          exact prefixNodeOriginLift_ne_freshRequest step _ request same
        · rcases List.mem_map.mp contentMember with ⟨node, _, rfl⟩
          exact prefixNodeFreshContent_ne_freshRequest step node request same

/-- Read the sole ordered ledger at any checked target. -/
def prefixNodeLands_at {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (target : final.val.NodeId) :
    PrefixNodeLands trace
      ((relationJoinConstructionNodeOrigins trace).get
        (Fin.cast (relationJoinConstructionNodeOrigins_length trace).symm
          target)) target :=
  ⟨rfl⟩

/-- A checked target has exactly one broad construction origin. -/
theorem prefixNodeLands_injective {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    {trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope}
    {leftOrigin rightOrigin : RelationJoinPrefixNodeOrigin (source := source)
      (dying := dying) (content := content) steps}
    {target : final.val.NodeId}
    (leftLanding : PrefixNodeLands trace leftOrigin target)
    (rightLanding : PrefixNodeLands trace rightOrigin target) :
    leftOrigin = rightOrigin :=
  leftLanding.exact.symm.trans rightLanding.exact

/-- One broad construction origin cannot land at two checked targets. -/
theorem prefixNodeLands_functional {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    {trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope}
    {origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps}
    {left right : final.val.NodeId}
    (leftLanding : PrefixNodeLands trace origin left)
    (rightLanding : PrefixNodeLands trace origin right) : left = right := by
  classical
  have castSame := get_injective_of_nodup
    (relationJoinConstructionNodeOrigins_nodup trace)
    (leftLanding.exact.trans rightLanding.exact.symm)
  apply Fin.ext
  simpa using congrArg Fin.val castSame

theorem prefixNodeLands_lookup {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    {trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope}
    {origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps}
    {target : final.val.NodeId}
    (landing : PrefixNodeLands trace origin target) :
    (relationJoinConstructionNodeOrigins trace).get
      (Fin.cast (relationJoinConstructionNodeOrigins_length trace).symm
        target) = origin :=
  landing.exact

/-- A surviving source node's final checked image reads back to that exact
source origin in the construction ledger. -/
theorem relationJoinConstructionNodeOrigins_source {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (sourceNode : source.val.NodeId) (finalNode : final.val.NodeId)
    (imageExact : finalNodeImage sourceNode = some finalNode) :
    (relationJoinConstructionNodeOrigins trace).get
      (Fin.cast (relationJoinConstructionNodeOrigins_length trace).symm
        finalNode) = (.inl sourceNode :
          RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
            (content := content) steps) := by
  induction trace with
  | nil =>
      have nodeExact : sourceNode = finalNode := Option.some.inj imageExact
      subst finalNode
      simp [relationJoinConstructionNodeOrigins, nodeLedger,
        ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange]
  | @snoc priorSteps current currentRegionImage currentNodeImage currentWireImage
      currentDying currentScope trace step priorExact priorRegionImageExact
      priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      cases Subsingleton.elim priorRegionImageExact HEq.rfl
      cases Subsingleton.elim priorNodeImageExact HEq.rfl
      cases Subsingleton.elim priorWireImageExact HEq.rfl
      cases Subsingleton.elim priorDyingExact HEq.rfl
      cases Subsingleton.elim priorScopeExact HEq.rfl
      cases priorImageExact : step.priorNodeImage sourceNode with
      | none =>
          rw [step.checkedNodeImageExact, step.baseNodeImageExact,
            priorImageExact] at imageExact
          contradiction
      | some priorNode =>
          have different : priorNode ≠ step.priorApplication := by
            intro same
            subst priorNode
            have sourceExact : sourceNode = step.application :=
              step.priorNodeImage_injective priorImageExact
                step.priorApplicationImage
            subst sourceNode
            rw [step.checkedNodeImage_application] at imageExact
            contradiction
          rw [step.checkedNodeImage_of_prior priorImageExact different]
            at imageExact
          have finalExact :
              finalNode = step.checkedPriorNode priorNode different :=
            (Option.some.inj imageExact).symm
          subst finalNode
          have castNode : priorNodeCast step rfl priorNode = priorNode := by
            apply Fin.ext
            rfl
          have differentCast :
              priorNodeCast step rfl priorNode ≠ step.priorApplication := by
            simpa [castNode] using different
          have retainedExact :=
            relationJoinConstructionNodeOrigins_get_checkedPriorNode
              trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl rfl
              priorNode differentCast
          calc
            _ = prefixNodeOriginLift step
                ((relationJoinConstructionNodeOrigins trace).get
                  (Fin.cast
                    (relationJoinConstructionNodeOrigins_length trace).symm
                    priorNode)) := by
              simpa [castNode] using retainedExact
            _ = prefixNodeOriginLift step (.inl sourceNode) :=
              congrArg (prefixNodeOriginLift step)
                (induction priorNode priorImageExact)
            _ = .inl sourceNode := rfl

/-- Every row retained by the sole ordered construction ledger is live in
that prefix.  In particular, a source row is absent as soon as its
application is consumed. -/
theorem relationJoinConstructionNodeOrigins_live {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (member : origin ∈ relationJoinConstructionNodeOrigins trace) :
    RelationJoinPrefixNodeLive origin := by
  classical
  induction trace with
  | nil =>
      simp only [relationJoinConstructionNodeOrigins, nodeLedger] at member
      rcases List.mem_map.mp member with ⟨node, _, rfl⟩
      simp [RelationJoinPrefixNodeLive]
  | @snoc priorSteps current currentRegionImage currentNodeImage currentWireImage
      currentDying currentScope trace step priorExact priorRegionImageExact
      priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      cases Subsingleton.elim priorRegionImageExact HEq.rfl
      cases Subsingleton.elim priorNodeImageExact HEq.rfl
      cases Subsingleton.elim priorWireImageExact HEq.rfl
      cases Subsingleton.elim priorDyingExact HEq.rfl
      cases Subsingleton.elim priorScopeExact HEq.rfl
      let retained := ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
        [step.priorApplication]
      simp only [relationJoinConstructionNodeOrigins, nodeLedger] at member
      rcases List.mem_append.mp member with prefixMember | requestMember
      · rcases List.mem_append.mp prefixMember with retainedMember | contentMember
        · rcases List.mem_map.mp retainedMember with ⟨target, targetMember, rfl⟩
          let priorOrigin := (nodeLedger trace).rows.get
            (Fin.cast (nodeLedger trace).length_exact.symm target)
          have priorMember : priorOrigin ∈
              relationJoinConstructionNodeOrigins trace := by
            exact List.get_mem _ _
          have priorLive := induction priorOrigin priorMember
          change RelationJoinPrefixNodeLive
            (prefixNodeOriginLift step
              ((nodeLedger trace).rows.get
                (Fin.cast (nodeLedger trace).length_exact.symm target)))
          cases originData : ((nodeLedger trace).rows.get
              (Fin.cast (nodeLedger trace).length_exact.symm target)) with
          | inr occurrence =>
              rcases occurrence with ⟨occurrence, node⟩
              cases node <;>
                simp [RelationJoinPrefixNodeLive, prefixNodeOriginLift]
          | inl sourceNode =>
              simp only [priorOrigin, originData,
                RelationJoinPrefixNodeLive] at priorLive
              simp only [originData, RelationJoinPrefixNodeLive,
                prefixNodeOriginLift,
                List.map_append, List.map_cons, List.map_nil,
                List.mem_append, List.mem_singleton]
              intro finalMember
              rcases finalMember with priorApplication | sourceExact
              · exact priorLive priorApplication
              · have sourceRow := relationJoinConstructionNodeOrigins_source
                  trace step.application step.priorApplication
                    step.priorApplicationImage
                have rowSame :
                    (relationJoinConstructionNodeOrigins trace).get
                        (Fin.cast
                          (relationJoinConstructionNodeOrigins_length trace).symm
                          target) =
                      (relationJoinConstructionNodeOrigins trace).get
                        (Fin.cast
                          (relationJoinConstructionNodeOrigins_length trace).symm
                          step.priorApplication) := by
                  calc
                    _ = .inl sourceNode := by
                      simpa [relationJoinConstructionNodeOrigins] using
                        originData
                    _ = .inl step.application := congrArg Sum.inl sourceExact
                    _ = _ := sourceRow.symm
                have targetExact := get_injective_of_nodup
                  (relationJoinConstructionNodeOrigins_nodup trace) rowSame
                have different : target ≠ step.priorApplication := by
                  have targetFacts :
                      target ∈ step.prior.val.nodesList ∧
                        target ≠ step.priorApplication := by
                    simpa [retained,
                      ConcreteDiagram.DenseErasure.retainedNodes] using
                        targetMember
                  exact targetFacts.2
                apply different
                apply Fin.ext
                simpa using congrArg Fin.val targetExact
        · rcases List.mem_map.mp contentMember with ⟨node, _, rfl⟩
          trivial
      · rcases List.mem_map.mp requestMember with ⟨request, _, rfl⟩
        trivial

/-- Compute a checked landing for every live broad node origin by structural
recursion on the Type-valued construction trace. -/
def prefixNodeLands_total {args : List Sig} :
    ∀ {steps : List (RelationJoinStep source dying content)}
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      (trace : RelationJoinConstructionTrace source dying content parameters args
        steps final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope) →
      (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
        (content := content) steps) →
      RelationJoinPrefixNodeLive origin →
      Σ target, PrefixNodeLands trace origin target
  | _, _, _, _, _, _, _, .nil, origin, live => by
      cases origin with
      | inl node =>
          exact ⟨node, ⟨relationJoinConstructionNodeOrigins_source
            .nil node node rfl⟩⟩
      | inr occurrence =>
          exact Fin.elim0 occurrence.1
  | _, _, _, _, _, _, _,
      .snoc (steps := priorSteps) trace step priorExact priorRegionImageExact
        priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
        relationArgsExact sourceParametersExact,
      origin, live =>
      let recurse := prefixNodeLands_total trace
      by
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases Subsingleton.elim priorRegionImageExact HEq.rfl
      cases Subsingleton.elim priorNodeImageExact HEq.rfl
      cases Subsingleton.elim priorWireImageExact HEq.rfl
      cases Subsingleton.elim priorDyingExact HEq.rfl
      cases Subsingleton.elim priorScopeExact HEq.rfl
      rcases prefixNodeOriginView step origin with lifted | fresh
      · rcases lifted with ⟨priorOrigin, ⟨originExact⟩⟩
        subst origin
        have priorLive := prefixNodeOriginLift_live step priorOrigin live
        obtain ⟨priorTarget, priorLanding⟩ :=
          recurse priorOrigin priorLive
        have castTarget : priorNodeCast step rfl priorTarget = priorTarget := by
          apply Fin.ext
          rfl
        by_cases targetExact : priorTarget = step.priorApplication
        ·
          subst priorTarget
          have sourceExact := relationJoinConstructionNodeOrigins_source
            trace step.application step.priorApplication
              step.priorApplicationImage
          have priorOriginExact : priorOrigin = (.inl step.application :
              RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
                (content := content) priorSteps) :=
            priorLanding.exact.symm.trans sourceExact
          subst priorOrigin
          simp [RelationJoinPrefixNodeLive, prefixNodeOriginLift] at live
        · have differentCast :
              priorNodeCast step rfl priorTarget ≠ step.priorApplication := by
            simpa [castTarget] using targetExact
          refine ⟨step.checkedPriorNode
            (priorNodeCast step rfl priorTarget) differentCast, ⟨?_⟩⟩
          have retainedExact :=
            relationJoinConstructionNodeOrigins_get_checkedPriorNode
            trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
            sourceParametersExact
            priorTarget differentCast
          exact retainedExact.trans
            (congrArg (prefixNodeOriginLift step) priorLanding.exact)
      · rcases fresh with contentOrigin | requestOrigin
        · rcases contentOrigin with ⟨node, ⟨originExact⟩⟩
          subst origin
          refine ⟨step.checkedFragmentNode node, ⟨?_⟩⟩
          exact relationJoinConstructionNodeOrigins_get_checkedFragmentNode
            trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
            sourceParametersExact
            node
        · rcases requestOrigin with ⟨request, ⟨originExact⟩⟩
          subst origin
          refine ⟨step.checkedIdentityNode request, ⟨?_⟩⟩
          exact relationJoinConstructionNodeOrigins_get_checkedIdentityNode
            trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
            sourceParametersExact
            request
termination_by steps _ _ _ _ _ _ _ _ _ => steps.length

end ConcreteWireQuantifier.RelationJoinConstructionTrace

end RawNodeTrace

end MonolithicWireQuantifier

end VisualProof
