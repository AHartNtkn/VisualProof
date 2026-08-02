import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawConstructionAtlas

namespace VisualProof

namespace ConcreteWireQuantifier

inductive RelationJoinSemanticTrace
    (source : CheckedDiagram definitions) (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) (args : List Sig) :
    (steps : List (RelationJoinStep source dying content)) →
    (final : CheckedDiagram definitions) →
    (source.val.RegionId → final.val.RegionId) →
    (source.val.NodeId → Option final.val.NodeId) →
    (source.val.WireId → final.val.WireId) →
    final.val.WireId → final.val.RegionId → Prop
  | nil :
      RelationJoinSemanticTrace source dying content parameters args []
        source id (fun node => some node) id dying
          (source.val.wires dying).scope
  | snoc
      {steps current currentRegionImage currentNodeImage currentWireImage
        currentDying currentScope}
      (trace :
        RelationJoinSemanticTrace source dying content parameters args steps
          current currentRegionImage currentNodeImage currentWireImage
            currentDying currentScope)
      (step : RelationJoinStep source dying content)
      (_ : step.prior = current)
      (_ : HEq step.priorRegionImage currentRegionImage)
      (_ : HEq step.priorNodeImage currentNodeImage)
      (_ : HEq step.priorWireImage currentWireImage)
      (_ : HEq (step.priorWireImage dying) currentDying)
      (_ : HEq
        (step.priorRegionImage (source.val.wires dying).scope) currentScope)
      (_ : step.relationArgs = args)
      (_ : step.sourceParameters = parameters) :
      RelationJoinSemanticTrace source dying content parameters args
        (steps ++ [step]) step.checked step.checkedRegionImage
        step.checkedNodeImage step.checkedWireImage
        (step.checkedWireImage dying)
        (step.checkedRegionImage (source.val.wires dying).scope)

/-- Data-bearing checked relation-join construction.  Unlike the semantic Prop
view, every snoc receipt remains available to structural recursion and
inversion. -/
inductive RelationJoinConstructionTrace
    (source : CheckedDiagram definitions) (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) (args : List Sig) :
    (steps : List (RelationJoinStep source dying content)) →
    (final : CheckedDiagram definitions) →
    CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final →
    (source.val.WireId → final.val.WireId) →
    final.val.WireId → final.val.RegionId → Type
  | nil :
      RelationJoinConstructionTrace source dying content parameters args []
        source initialAtlas id dying
          (source.val.wires dying).scope
  | snoc
      {steps}
      (step : RelationJoinStep source dying content)
      {currentAtlas : CertifiedAtlas (source := source) (dying := dying)
        (content := content) steps step.prior}
      {currentWireImage : source.val.WireId → step.prior.val.WireId}
      {currentDying : step.prior.val.WireId}
      {currentScope : step.prior.val.RegionId}
      (trace :
        RelationJoinConstructionTrace source dying content parameters args steps
          step.prior currentAtlas currentWireImage currentDying currentScope)
      (_ : HEq step.priorWireImage currentWireImage)
      (_ : HEq (step.priorWireImage dying) currentDying)
      (_ : HEq
        (currentAtlas.regionImage (source.val.wires dying).scope) currentScope)
      (_ : step.relationArgs = args)
      (_ : step.sourceParameters = parameters)
      (receipt : AtlasStepReceipt step currentAtlas)
      (applicationLanding :
        NodeLands currentAtlas.rows (.inl step.application)
          step.priorApplication) :
      RelationJoinConstructionTrace source dying content parameters args
        (steps ++ [step]) step.checked
        (extendAtlas step currentAtlas receipt applicationLanding)
        step.checkedWireImage
        (step.checkedWireImage dying)
        ((extendAtlas step currentAtlas receipt applicationLanding).regionImage
          (source.val.wires dying).scope)

/-- Erase only the trace's data-bearing status, preserving its exact semantic
indices and receipts. -/
def RelationJoinConstructionTrace.semanticTrace
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying
        finalScope) :
    RelationJoinSemanticTrace source dying content parameters args steps final
      finalAtlas.regionImage finalAtlas.nodeImage finalWireImage finalDying
        finalScope := by
  induction trace with
  | nil => exact .nil
  | snoc step trace priorWireImageExact priorDyingExact
      priorScopeExact relationArgsExact sourceParametersExact receipt
      applicationLanding induction =>
      rw [extendAtlas_regionImageAgreement step _ receipt applicationLanding,
        extendAtlas_nodeImageAgreement step _ receipt applicationLanding]
      exact .snoc induction step rfl
        (heq_of_eq receipt.priorRegionImageAgreement)
        (heq_of_eq receipt.priorNodeImageAgreement)
        priorWireImageExact priorDyingExact
        ((heq_of_eq (congrArg
          (fun image : source.val.RegionId → step.prior.val.RegionId =>
            image (source.val.wires dying).scope)
          receipt.priorRegionImageAgreement)).trans priorScopeExact)
        relationArgsExact sourceParametersExact

private theorem checkedWire_injective
    {definitions : List (List Sig)}
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Function.Injective (Internal.checkedWire generated) := by
  intro left right same
  apply Fin.ext
  simpa [Internal.checkedWire] using congrArg Fin.val same

private theorem relationJoin_checkedRegion_injective
    {definitions : List (List Sig)}
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Function.Injective (Internal.checkedRegion generated) := by
  intro left right same
  apply Fin.ext
  simpa [Internal.checkedRegion] using congrArg Fin.val same

private theorem relationJoin_checkedNode_injective
    {definitions : List (List Sig)}
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Function.Injective (Internal.checkedNode generated) := by
  intro left right same
  apply Fin.ext
  simpa [Internal.checkedNode] using congrArg Fin.val same

private theorem retainedRegionIndex_injective
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    {left right : source.val.RegionId}
    (leftMember : left ∈ Internal.retainedRegions source removed)
    (rightMember : right ∈ Internal.retainedRegions source removed)
    (same :
      Internal.retainedRegionIndex source removed left leftMember =
        Internal.retainedRegionIndex source removed right rightMember) :
    left = right := by
  have values :=
    congrArg (Internal.retainedRegions source removed).get same
  unfold Internal.retainedRegionIndex at values
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

private theorem retainedNodeIndex_injective
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    {left right : source.val.NodeId}
    (leftMember : left ∈ Internal.retainedNodes source removed)
    (rightMember : right ∈ Internal.retainedNodes source removed)
    (same :
      Internal.retainedNodeIndex source removed left leftMember =
        Internal.retainedNodeIndex source removed right rightMember) :
    left = right := by
  have values := congrArg (Internal.retainedNodes source removed).get same
  unfold Internal.retainedNodeIndex at values
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

private theorem retainedWireIndex_injective
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    {left right : source.val.WireId}
    (leftMember : left ∈ Internal.retainedWires source removed)
    (rightMember : right ∈ Internal.retainedWires source removed)
    (same :
      Internal.retainedWireIndex source removed left leftMember =
        Internal.retainedWireIndex source removed right rightMember) :
    left = right := by
  have values :=
    congrArg (Internal.retainedWires source removed).get same
  unfold Internal.retainedWireIndex at values
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

private structure RelationJoinState
    (source : CheckedDiagram definitions)
    (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig) : Type where
  checked : CheckedDiagram definitions
  processed : List source.val.NodeId
  steps : List (RelationJoinStep source dying content)
  traceExact :
    steps.map RelationJoinStep.application = processed
  atlas : CertifiedAtlas (source := source) (dying := dying)
    (content := content) steps checked
  regionImage_val : ∀ region, (atlas.regionImage region).val = region.val
  regionImage_encloses :
    ∀ outer inner,
      checked.val.Encloses (atlas.regionImage outer) (atlas.regionImage inner) ↔
        source.val.Encloses outer inner
  wireImage : source.val.WireId → checked.val.WireId
  wireImage_injective : Function.Injective wireImage
  wireScopeExact :
    ∀ sourceWire,
      (checked.val.wires (wireImage sourceWire)).scope =
        atlas.regionImage (source.val.wires sourceWire).scope
  nodeImage_injective :
    ∀ {left right checkedNode},
      atlas.nodeImage left = some checkedNode →
      atlas.nodeImage right = some checkedNode →
      left = right
  constructionTrace :
    RelationJoinConstructionTrace source dying content parameters args steps
      checked atlas wireImage (wireImage dying)
        (atlas.regionImage (source.val.wires dying).scope)

private def RelationJoinState.regionImage
    (state : RelationJoinState source dying content parameters args) :
    source.val.RegionId → state.checked.val.RegionId :=
  state.atlas.regionImage

private def RelationJoinState.nodeImage
    (state : RelationJoinState source dying content parameters args) :
    source.val.NodeId → Option state.checked.val.NodeId :=
  state.atlas.nodeImage

private structure RelationJoinStepResult
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source dying content parameters args)
    (application : RelationJoinApplication source args) : Type where
  next : RelationJoinState source dying content parameters args
  processedExact :
    next.processed = state.processed ++ [application.node]

private theorem relationJoinRegionRetained
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    region ∈ Internal.retainedRegions source [] := by
  simp [Internal.retainedRegions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin]

private theorem relationJoinWireRetained
    (source : CheckedDiagram definitions)
    (dying candidate : source.val.WireId)
    (different : candidate ≠ dying) :
    candidate ∈ Internal.retainedWires source [] := by
  simp [Internal.retainedWires, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin]

private structure RelationJoinInitialResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (plan : RelationJoinPlan source wire content parameters) : Type where
  state : RelationJoinState source wire content parameters plan.args
  checkedExact : state.checked = source
  processedEmpty : state.processed = []

private def relationJoinInitialState
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (plan : RelationJoinPlan source wire content parameters) :
    RelationJoinInitialResult plan := by
  let state : RelationJoinState source wire content parameters plan.args :=
    { checked := source
      processed := []
      steps := []
      traceExact := rfl
      atlas := initialAtlas
      regionImage_val := fun _ => rfl
      regionImage_encloses := fun _ _ => Iff.rfl
      wireImage := id
      wireImage_injective := Function.injective_id
      wireScopeExact := fun _ => rfl
      nodeImage_injective := by
        intro left right checkedNode leftExact rightExact
        exact Option.some.inj (leftExact.trans rightExact.symm)
      constructionTrace := .nil }
  exact
    { state := state
      checkedExact := rfl
      processedEmpty := rfl }

private def relationJoinAttachments
    {source : CheckedDiagram definitions}
    (application : RelationJoinApplication source args)
    (parameters : List source.val.WireId) :
    List source.val.WireId :=
  application.arguments ++ parameters

private def spliceRelationApplication
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig)
    (state : RelationJoinState source wire content parameters args)
    (application : RelationJoinApplication source args) :
    Except Error (RelationJoinStepResult state application) := by
  match priorApplicationAccepted :
      state.nodeImage application.node with
  | none =>
      exact .error (.invalidApplication application.node.val)
  | some priorApplication =>
      if priorNodeExact :
          state.checked.val.nodes priorApplication =
            .atom (state.regionImage application.region) args then
        if priorDyingOwner :
            state.checked.val.endpointOwner?
                ⟨priorApplication, .head⟩ =
              some (state.wireImage wire) then
          match priorArgumentsAccepted :
              relationArgumentWires? state.checked priorApplication args 0 with
          | none =>
              exact .error (.invalidApplication application.node.val)
          | some priorArguments =>
              if priorArgumentsExact :
                  priorArguments =
                    application.arguments.map state.wireImage then
                match removalAccepted :
                    Internal.checkBatchRemovalPlan? state.checked []
                      [priorApplication] [] with
                | none =>
                    exact .error .invalidRemoval
                | some removal =>
                    let baseCandidate :=
                      ConcreteDiagram.DenseErasure.eraseNodeCandidate
                        state.checked priorApplication
                    match baseAccepted :
                        ConcreteDiagram.checkWellFormed definitions
                          baseCandidate with
                    | .error error =>
                        exact .error (.wellFormed error)
                    | .ok base =>
                        have baseGenerated :=
                          ConcreteDiagram.checkWellFormed_preserves_input
                            baseAccepted
                        let baseRegionImage :
                            source.val.RegionId → base.val.RegionId :=
                          fun region =>
                            Internal.checkedRegion baseGenerated
                              (ConcreteDiagram.DenseErasure.eraseNodeRegion
                                state.checked priorApplication
                                (state.regionImage region))
                        let baseWireImage :
                            source.val.WireId → base.val.WireId :=
                          fun sourceWire =>
                            Internal.checkedWire baseGenerated
                              (ConcreteDiagram.DenseErasure.eraseNodeWire
                                state.checked priorApplication
                                (state.wireImage sourceWire))
                        let baseNodeImage :
                            source.val.NodeId →
                              Option base.val.NodeId :=
                          fun sourceNode =>
                            match state.nodeImage sourceNode with
                            | none => none
                            | some priorNode =>
                                if retained :
                                    priorNode ∈
                                      ConcreteDiagram.DenseErasure.retainedNodes
                                        state.checked.val [priorApplication] then
                                  some
                                    (Internal.checkedNode baseGenerated
                                      (ConcreteDiagram.DenseErasure.eraseNodeIndex
                                        state.checked priorApplication
                                        priorNode retained))
                                else
                                  none
                        let sources :=
                          relationJoinAttachments application parameters
                        if exactArity :
                            sources.length =
                              content.val.boundary.length then
                          if allSurvive :
                              sources.all fun sourceWire =>
                                decide (sourceWire ≠ wire) then
                            let target :
                                Fin content.val.boundary.length →
                                  base.val.WireId :=
                              fun position =>
                                let sourcePosition : Fin sources.length :=
                                  Fin.cast exactArity.symm position
                                let sourceWire :=
                                  sources.get sourcePosition
                                baseWireImage sourceWire
                            let site :=
                              baseRegionImage application.region
                            match attachmentAccepted :
                                checkConcreteSpliceAttachment base site
                                  content target with
                            | none =>
                                exact .error .invalidAttachment
                            | some attachment =>
                                match checked :
                                    ConcreteDiagram.checkWellFormed
                                      definitions attachment.diagram with
                                | .error error =>
                                    exact .error (.wellFormed error)
                                | .ok next =>
                                    have generated :=
                                      ConcreteDiagram.checkWellFormed_preserves_input
                                        checked
                                    have exactTarget :
                                        attachment.target = target :=
                                      checkConcreteSpliceAttachment_target
                                        base site content target attachment
                                          attachmentAccepted
                                    have canonicalAccepted :
                                        checkConcreteSpliceAttachment base site
                                            content attachment.target =
                                          some attachment := by
                                      rw [exactTarget]
                                      exact attachmentAccepted
                                    have baseWireScopeExact :
                                        ∀ sourceWire,
                                          (base.val.wires
                                              (baseWireImage sourceWire)).scope =
                                            baseRegionImage
                                              (source.val.wires
                                                sourceWire).scope := by
                                      intro sourceWire
                                      unfold baseWireImage baseRegionImage
                                      rw [Internal.checkedWire_scope_transport]
                                      apply congrArg
                                        (Internal.checkedRegion baseGenerated)
                                      simp only [baseCandidate,
                                        ConcreteDiagram.DenseErasure.eraseNodeCandidate]
                                      have sourceExact :
                                          state.checked.val.wiresList.get
                                              (ConcreteDiagram.DenseErasure.eraseNodeWire
                                                state.checked priorApplication
                                                (state.wireImage sourceWire)) =
                                            state.wireImage sourceWire := by
                                        apply Fin.ext
                                        simp [ConcreteDiagram.DenseErasure.eraseNodeWire,
                                          ConcreteDiagram.wiresList,
                                          Data.Finite.allFin_eq_finRange]
                                      rw [sourceExact,
                                        state.wireScopeExact sourceWire]
                                      apply Fin.ext
                                      rfl
                                    match compileSite? state.checked
                                        (state.regionImage application.region) with
                                  | none =>
                                      exact .error .invalidRemoval
                                  | some priorSite =>
                                    let step :
                                        RelationJoinStep source wire content :=
                                      { application := application.node
                                        sourceRegion := application.region
                                        sourceArguments :=
                                          application.arguments
                                        sourceArgumentsAccepted :=
                                          application.argumentsAccepted
                                        sourceParameters := parameters
                                        sourceAttachments := sources
                                        sourceAttachmentsExact := rfl
                                        sourceAttachmentArity := exactArity
                                        sourceAttachmentsSurvive :=
                                          fun position =>
                                            of_decide_eq_true
                                              ((List.all_eq_true.mp
                                                  allSurvive)
                                                (sources.get position)
                                                (List.get_mem _ position))
                                        relationArgs := args
                                        sourceNodeExact := application.nodeExact
                                        prior := state.checked
                                        priorApplication :=
                                          priorApplication
                                        priorNodeImage := state.nodeImage
                                        priorNodeImage_injective :=
                                          state.nodeImage_injective
                                        priorApplicationImage :=
                                          priorApplicationAccepted
                                        priorRegionImage :=
                                          state.regionImage
                                        priorRegionImageVal :=
                                          state.regionImage_val
                                        priorRegionImageEncloses :=
                                          state.regionImage_encloses
                                        priorWireImage := state.wireImage
                                        priorWireScopeExact :=
                                          state.wireScopeExact
                                        priorNodeExact := priorNodeExact
                                        priorSite := priorSite
                                        priorDyingOwner := priorDyingOwner
                                        priorArguments := priorArguments
                                        priorArgumentsAccepted :=
                                          priorArgumentsAccepted
                                        priorArgumentsExact :=
                                          priorArgumentsExact
                                        removal := removal
                                        base := base
                                        baseGenerated := baseGenerated
                                        baseRegionImage := baseRegionImage
                                        baseRegionImageExact := fun _ => rfl
                                        baseWireImage := baseWireImage
                                        baseWireImageExact := fun _ => rfl
                                        baseNodeImage := baseNodeImage
                                        baseNodeImageExact := by
                                          intro sourceNode
                                          unfold baseNodeImage
                                          generalize imageExact :
                                            state.nodeImage sourceNode = image
                                          cases image with
                                          | none => rfl
                                          | some priorNode =>
                                              by_cases retained :
                                                  priorNode ∈
                                                    ConcreteDiagram.DenseErasure.retainedNodes
                                                      state.checked.val
                                                        [priorApplication]
                                              · simp [retained]
                                              · simp [retained]
                                        baseWireScopeExact :=
                                          baseWireScopeExact
                                        site := site
                                        siteExact := rfl
                                        attachment := attachment
                                        targetExact := by
                                          intro position
                                          rw [exactTarget]
                                        checked := next
                                        attachmentAccepted :=
                                          canonicalAccepted
                                        generated := generated
                                        checkedRegionImage := fun region =>
                                          Internal.checkedRegion generated
                                            (attachment.hostRegion
                                              (baseRegionImage region))
                                        checkedRegionImageExact :=
                                          fun _ => rfl
                                        checkedRegionImageEncloses := by
                                          intro outer inner
                                          rw [Internal.checkedRegion_encloses]
                                          rw [ConcreteSpliceAttachment.hostRegion_encloses_iff]
                                          unfold baseRegionImage
                                          rw [Internal.checkedRegion_encloses]
                                          rw [ConcreteDiagram.DenseErasure.eraseNodeRegion_encloses_iff]
                                          exact
                                            state.regionImage_encloses
                                              outer inner
                                        checkedNodeImage := fun sourceNode =>
                                          (baseNodeImage sourceNode).map
                                            fun baseNode =>
                                              Internal.checkedNode generated
                                                (attachment.hostNode baseNode)
                                        checkedNodeImageExact := fun _ => rfl
                                        checkedWireImage := fun sourceWire =>
                                          Internal.checkedWire generated
                                            (attachment.hostWire
                                              (baseWireImage sourceWire))
                                        checkedWireImageExact :=
                                          fun _ => rfl
                                        checkedWireScopeExact := by
                                          intro sourceWire
                                          rw [Internal.checkedWire_scope_transport,
                                            attachment.diagram_wire_hostWire_scope]
                                          exact
                                            congrArg (Internal.checkedRegion generated)
                                              (congrArg attachment.hostRegion
                                                (baseWireScopeExact
                                                  sourceWire)) }
                                    let receipt : AtlasStepReceipt step state.atlas :=
                                      { baseNodeCountAddOne :=
                                          step.base_nodeCount_add_one
                                        checkedNodeCountAddOne :=
                                          step.checked_nodeCount_add_one
                                        priorRegionImageAgreement := by
                                          rfl
                                        priorNodeImageAgreement := by
                                          rfl
                                        freshRegionAllocation :=
                                          checkedFreshRegionAtPosition_eq_checkedFragmentRegion
                                            step
                                        retainedRegionAllocation :=
                                          checkedRetainedRegion_eq_checkedPriorRegion
                                            step
                                        retainedNodeAllocation :=
                                          retainedNodeAllocation_generic
                                            step
                                            { baseNodeCountAddOne :=
                                                step.base_nodeCount_add_one
                                              checkedNodeCountAddOne :=
                                                step.checked_nodeCount_add_one } }
                                    let applicationLanding :
                                        NodeLands state.atlas.rows
                                          (.inl step.application)
                                          step.priorApplication :=
                                      state.atlas.nodeImageLandsOfEqSome
                                        application.node priorApplication
                                        priorApplicationAccepted
                                    let nextAtlas :=
                                      extendAtlas step state.atlas receipt
                                        applicationLanding
                                    let nextState :
                                        RelationJoinState source wire content
                                          parameters args :=
                                      { checked := next
                                        processed :=
                                          state.processed ++
                                            [application.node]
                                        steps := state.steps ++ [step]
                                        traceExact := by
                                          simp [step, state.traceExact]
                                        atlas := nextAtlas
                                        regionImage_val :=
                                          by
                                            intro region
                                            rw [extendAtlas_regionImageAgreement]
                                            exact step.checkedRegionImage_val region
                                        regionImage_encloses :=
                                          by
                                            intro outer inner
                                            rw [extendAtlas_regionImageAgreement]
                                            exact
                                              step.checkedRegionImageEncloses
                                                outer inner
                                        wireImage := step.checkedWireImage
                                        wireImage_injective := by
                                          intro left right same
                                          apply state.wireImage_injective
                                          apply
                                            ConcreteDiagram.DenseErasure.eraseNodeWire_injective
                                              state.checked priorApplication
                                          apply
                                            checkedWire_injective
                                              baseGenerated
                                          apply
                                            attachment.hostWire_injective
                                          apply
                                            checkedWire_injective generated
                                          exact same
                                        wireScopeExact :=
                                          by
                                            intro sourceWire
                                            rw [extendAtlas_regionImageAgreement]
                                            exact
                                              step.checkedWireScopeExact sourceWire
                                        nodeImage_injective :=
                                          by
                                            intro left right checkedNode
                                              leftExact rightExact
                                            rw [extendAtlas_nodeImageAgreement]
                                              at leftExact rightExact
                                            exact
                                              step.checkedNodeImage_injective
                                                leftExact rightExact
                                        constructionTrace :=
                                          .snoc step state.constructionTrace
                                            (by simp [step])
                                            (by simp [step]) (heq_of_eq rfl)
                                            rfl rfl
                                            receipt applicationLanding }
                                    exact .ok
                                      { next := nextState
                                        processedExact := rfl }
                          else
                            exact .error .dyingWireParameter
                        else
                          exact .error .boundaryArityMismatch
              else
                exact .error (.invalidApplication application.node.val)
        else
          exact .error (.invalidApplication application.node.val)
      else
        exact .error (.invalidApplication application.node.val)

private def spliceRelationApplications
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    (args : List Sig) →
    RelationJoinState source wire content parameters args →
      List (RelationJoinApplication source args) →
        Except Error
          (RelationJoinState source wire content parameters args)
  | _, state, [] => .ok state
  | args, state, application :: rest => do
      let step ←
        spliceRelationApplication source wire content parameters args
          state application
      spliceRelationApplications source wire content parameters args
        step.next rest

private theorem spliceRelationApplications_processed
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig)
    (state final : RelationJoinState source wire content parameters args)
    (applications : List (RelationJoinApplication source args))
    (accepted :
      spliceRelationApplications source wire content parameters args
          state applications =
        .ok final) :
    final.processed =
      state.processed ++
        applications.map RelationJoinApplication.node := by
  induction applications generalizing state with
  | nil =>
      simp only [spliceRelationApplications, Except.ok.injEq] at accepted
      subst final
      simp
  | cons application rest induction =>
      unfold spliceRelationApplications at accepted
      cases stepAccepted :
          spliceRelationApplication source wire content parameters args
            state application with
      | error error =>
          rw [stepAccepted] at accepted
          contradiction
      | ok step =>
          rw [stepAccepted] at accepted
          rw [induction step.next accepted, step.processedExact]
          simp [List.append_assoc]

private structure RelationJoinFinalRemoval
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source wire content parameters args) : Type where
  checked : CheckedDiagram definitions
  plan :
    Internal.BatchRemovalPlan state.checked [] [] [state.wireImage wire]
  generated :
    checked.val = Internal.batchRemovalCandidate plan
  allRegionImage : state.checked.val.RegionId → checked.val.RegionId
  allRegionImageExact :
    ∀ region,
      allRegionImage region =
        Internal.checkedRegion generated
          (Internal.retainedRegionIndex state.checked [] region (by
            simp [Internal.retainedRegions,
              ConcreteDiagram.regionsList,
              Data.Finite.mem_allFin]))
  allRegionImage_injective : Function.Injective allRegionImage
  allNodeImage : state.checked.val.NodeId → checked.val.NodeId
  allNodeImageExact :
    ∀ node,
      allNodeImage node =
        Internal.checkedNode generated
          (Internal.retainedNodeIndex state.checked [] node (by
            simp [Internal.retainedNodes,
              ConcreteDiagram.nodesList,
              Data.Finite.mem_allFin]))
  allNodeImage_injective : Function.Injective allNodeImage
  allWireImage :
    ∀ boundWire : state.checked.val.WireId,
      boundWire ≠ state.wireImage wire → checked.val.WireId
  allWireImageExact :
    ∀ (boundWire : state.checked.val.WireId)
      (different : boundWire ≠ state.wireImage wire),
      allWireImage boundWire different =
        Internal.checkedWire generated
          (Internal.retainedWireIndex state.checked [state.wireImage wire]
            boundWire (by
              simp [Internal.retainedWires,
                ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
                different]))
  allWireImage_injective :
    ∀ {left right : state.checked.val.WireId}
      (leftSurvives : left ≠ state.wireImage wire)
      (rightSurvives : right ≠ state.wireImage wire),
      allWireImage left leftSurvives = allWireImage right rightSurvives →
        left = right
  regionImage : source.val.RegionId → checked.val.RegionId
  wireImage :
    ∀ sourceWire : source.val.WireId,
      sourceWire ≠ wire → checked.val.WireId

private def removeRelationJoinWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source wire content parameters args) :
    Except Error (RelationJoinFinalRemoval state) := by
  let dying := state.wireImage wire
  match prepared :
      Internal.checkBatchRemovalPlan? state.checked [] [] [dying] with
  | none =>
      exact .error .invalidRemoval
  | some plan =>
      let candidate := Internal.batchRemovalCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          have generated :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          exact .ok
            { checked := checked
              plan := plan
              generated := generated
              allRegionImage := fun region =>
                Internal.checkedRegion generated
                  (Internal.retainedRegionIndex state.checked [] region (by
                    simp [Internal.retainedRegions,
                      ConcreteDiagram.regionsList,
                      Data.Finite.mem_allFin]))
              allRegionImageExact := fun _ => rfl
              allRegionImage_injective := by
                intro left right same
                apply retainedRegionIndex_injective state.checked []
                  (by simp [Internal.retainedRegions,
                    ConcreteDiagram.regionsList, Data.Finite.mem_allFin])
                  (by simp [Internal.retainedRegions,
                    ConcreteDiagram.regionsList, Data.Finite.mem_allFin])
                exact relationJoin_checkedRegion_injective generated same
              allNodeImage := fun node =>
                Internal.checkedNode generated
                  (Internal.retainedNodeIndex state.checked [] node (by
                    simp [Internal.retainedNodes,
                      ConcreteDiagram.nodesList,
                      Data.Finite.mem_allFin]))
              allNodeImageExact := fun _ => rfl
              allNodeImage_injective := by
                intro left right same
                apply retainedNodeIndex_injective state.checked []
                  (by simp [Internal.retainedNodes,
                    ConcreteDiagram.nodesList, Data.Finite.mem_allFin])
                  (by simp [Internal.retainedNodes,
                    ConcreteDiagram.nodesList, Data.Finite.mem_allFin])
                exact relationJoin_checkedNode_injective generated same
              allWireImage := fun boundWire different =>
                Internal.checkedWire generated
                  (Internal.retainedWireIndex state.checked [dying]
                    boundWire (by
                      simp only [Internal.retainedWires,
                        ConcreteDiagram.wiresList,
                        List.mem_filter, Data.Finite.mem_allFin, true_and,
                        List.mem_cons, List.not_mem_nil, or_false]
                      apply decide_eq_true
                      simpa [dying] using different))
              allWireImageExact := fun _ _ => rfl
              allWireImage_injective := by
                intro left right leftSurvives rightSurvives same
                apply retainedWireIndex_injective state.checked [dying]
                  (by
                    simp only [Internal.retainedWires,
                      ConcreteDiagram.wiresList, List.mem_filter,
                      Data.Finite.mem_allFin, true_and, List.mem_cons,
                      List.not_mem_nil, or_false]
                    apply decide_eq_true
                    simpa [dying] using leftSurvives)
                  (by
                    simp only [Internal.retainedWires,
                      ConcreteDiagram.wiresList, List.mem_filter,
                      Data.Finite.mem_allFin, true_and, List.mem_cons,
                      List.not_mem_nil, or_false]
                    apply decide_eq_true
                    simpa [dying] using rightSurvives)
                exact checkedWire_injective generated same
              regionImage := fun region =>
                Internal.checkedRegion generated
                  (Internal.retainedRegionIndex state.checked []
                    (state.regionImage region) (by
                      simp [Internal.retainedRegions,
                        ConcreteDiagram.regionsList,
                        Data.Finite.mem_allFin]))
              wireImage := fun sourceWire different =>
                Internal.checkedWire generated
                  (Internal.retainedWireIndex state.checked [dying]
                    (state.wireImage sourceWire) (by
                      have mappedDifferent :
                          state.wireImage sourceWire ≠ dying := by
                        intro same
                        exact different (state.wireImage_injective same)
                      simp [Internal.retainedWires,
                        ConcreteDiagram.wiresList,
                        Data.Finite.mem_allFin, mappedDifferent])) }

/-- Raw checked output of grounding every applied endpoint of one relation
wire, ending immediately after deletion of the exhausted relation wire. -/
structure RelationJoinResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  private mk ::
  private plan : RelationJoinPlan source wire content parameters
  private initial : RelationJoinInitialResult plan
  private finalState :
    RelationJoinState source wire content parameters plan.args
  private batchAccepted :
    spliceRelationApplications source wire content parameters plan.args
        initial.state plan.applications =
      .ok finalState
  private finalRemoval : RelationJoinFinalRemoval finalState

namespace RelationJoinResult

/-- Source applications consumed by the construction, in execution order. -/
def applications
    (result : RelationJoinResult source wire content parameters) :
    List source.val.NodeId :=
  result.finalState.processed

def args
    (result : RelationJoinResult source wire content parameters) :
    List Sig :=
  result.plan.args

def boundarySignatures
    (_result : RelationJoinResult source wire content parameters) :
    List Sig :=
  openBoundarySigs content

def parameterSignatures
    (_result : RelationJoinResult source wire content parameters) :
    List Sig :=
  parameterSigs source parameters

def initialChecked
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.initial.state.checked

section FinalDeletion

variable {definitions : List (List Sig)} {source : CheckedDiagram definitions}
variable {wire : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

def boundFinal
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.finalState.checked

def boundRegionImage
    (result : RelationJoinResult source wire content parameters) :
    source.val.RegionId → result.boundFinal.val.RegionId :=
  result.finalState.regionImage

@[simp] theorem boundRegionImage_val
    (result : RelationJoinResult source wire content parameters)
    (region : source.val.RegionId) :
    (result.boundRegionImage region).val = region.val :=
  result.finalState.regionImage_val region

/-- Exact source-node landing after the complete splice fold. Consumed
relation applications map to `none`; every surviving source node maps to its
checked final representative. -/
def boundNodeImage
    (result : RelationJoinResult source wire content parameters) :
    source.val.NodeId → Option result.boundFinal.val.NodeId :=
  result.finalState.nodeImage

theorem boundNodeImage_injective
    (result : RelationJoinResult source wire content parameters)
    {left right : source.val.NodeId}
    {checkedNode : result.boundFinal.val.NodeId}
    (leftExact : result.boundNodeImage left = some checkedNode)
    (rightExact : result.boundNodeImage right = some checkedNode) :
    left = right :=
  result.finalState.nodeImage_injective leftExact rightExact

def boundWireImage
    (result : RelationJoinResult source wire content parameters) :
    source.val.WireId → result.boundFinal.val.WireId :=
  result.finalState.wireImage

theorem boundWireImage_injective
    (result : RelationJoinResult source wire content parameters) :
    Function.Injective result.boundWireImage :=
  result.finalState.wireImage_injective

def boundDying
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.WireId :=
  result.boundWireImage wire

def plainFinal
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.finalRemoval.checked

/-- Exact final-deletion landing for every region present after all splices. -/
def plainBoundRegionImage
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.RegionId → result.plainFinal.val.RegionId :=
  result.finalRemoval.allRegionImage

@[simp] theorem plainBoundRegionImage_val
    (result : RelationJoinResult source wire content parameters)
    (region : result.boundFinal.val.RegionId) :
    (result.plainBoundRegionImage region).val = region.val := by
  unfold plainBoundRegionImage
  rw [result.finalRemoval.allRegionImageExact]
  unfold Internal.checkedRegion
  change (Internal.noRegionRemovalEquiv result.boundFinal region).val =
    region.val
  have inverseExact :=
    Internal.sourceRetainedRegion_noRegionRemovalEquiv
      result.boundFinal region
  simpa [Internal.sourceRetainedRegion, Internal.retainedRegions_nil,
    ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
      congrArg Fin.val inverseExact

@[simp] theorem plainFinal_root_val_of_bound
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.root.val = result.boundFinal.val.root.val := by
  have retainedVal :=
    result.plainBoundRegionImage_val result.boundFinal.val.root
  unfold plainBoundRegionImage at retainedVal
  rw [result.finalRemoval.allRegionImageExact] at retainedVal
  unfold plainFinal
  rw [Internal.checkedRoot_transport result.finalRemoval.generated]
  unfold Internal.checkedRegion
  change
    (Internal.batchRemovalCandidate result.finalRemoval.plan).root.val =
      result.boundFinal.val.root.val
  rw [Internal.batchRemovalCandidate_root_noRegions]
  change
    (Internal.noRegionRemovalEquiv result.boundFinal
      result.boundFinal.val.root).val = result.boundFinal.val.root.val
  exact retainedVal

theorem plainBoundRegionImage_injective
    (result : RelationJoinResult source wire content parameters) :
    Function.Injective result.plainBoundRegionImage :=
  result.finalRemoval.allRegionImage_injective

/-- Final exhausted-relation deletion preserves an exact sheet entry. -/
theorem plainBoundRegionImage_sheet
    (result : RelationJoinResult source wire content parameters)
    (region : result.boundFinal.val.RegionId)
    (data : result.boundFinal.val.regions region = .sheet) :
    result.plainFinal.val.regions
        (result.plainBoundRegionImage region) = .sheet := by
  unfold plainBoundRegionImage
  rw [result.finalRemoval.allRegionImageExact]
  apply Internal.checkedRegion_data_transport_sheet
    result.finalRemoval.generated
  apply Internal.batchRegionTable_retained_sheet result.finalRemoval.plan
    region _ data

/-- Final exhausted-relation deletion preserves an exact cut entry. -/
theorem plainBoundRegionImage_cut
    (result : RelationJoinResult source wire content parameters)
    (region parent : result.boundFinal.val.RegionId)
    (data : result.boundFinal.val.regions region = .cut parent) :
    result.plainFinal.val.regions
        (result.plainBoundRegionImage region) =
      .cut (result.plainBoundRegionImage parent) := by
  unfold plainBoundRegionImage
  rw [result.finalRemoval.allRegionImageExact,
    result.finalRemoval.allRegionImageExact]
  apply Internal.checkedRegion_data_transport_cut
    result.finalRemoval.generated
  apply Internal.batchRegionTable_retained_cut result.finalRemoval.plan
    region _ parent data

private theorem finalRemoval_allNodeImage_val
    (result : RelationJoinResult source wire content parameters)
    (node : result.boundFinal.val.NodeId) :
    (result.finalRemoval.allNodeImage node).val = node.val := by
  unfold boundFinal at node
  have retainedExact :
      Internal.retainedNodes result.finalState.checked [] =
        Data.Finite.allFin result.finalState.checked.val.nodeCount := by
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList]
  let position : Fin
      (Data.Finite.allFin result.finalState.checked.val.nodeCount).length :=
    Fin.cast (by simp [Data.Finite.allFin_eq_finRange]) node
  have getExact :
      (Data.Finite.allFin result.finalState.checked.val.nodeCount).get position =
        node := by
    apply Fin.ext
    simp [position, Data.Finite.allFin_eq_finRange, List.get_eq_getElem]
  have desiredIndex :
      DenseList.index
          (Data.Finite.allFin result.finalState.checked.val.nodeCount) node
          (Data.Finite.mem_allFin node) = position := by
    have same : DenseList.index
        (Data.Finite.allFin result.finalState.checked.val.nodeCount) node
        (Data.Finite.mem_allFin node) = DenseList.index _
          ((Data.Finite.allFin
            result.finalState.checked.val.nodeCount).get position)
          (List.get_mem _ position) := by
      congr
      exact getExact.symm
    rw [same]
    exact DenseList.index_get _
      (Data.Finite.allFin_nodup result.finalState.checked.val.nodeCount) position
  have indexVal (values : List result.finalState.checked.val.NodeId)
      (exact : values =
        Data.Finite.allFin result.finalState.checked.val.nodeCount)
      (member : node ∈ values) :
      (DenseList.index values node member).val = node.val := by
    subst values
    exact congrArg Fin.val desiredIndex
  rw [result.finalRemoval.allNodeImageExact]
  simpa [Internal.retainedNodeIndex, Internal.checkedNode] using
    indexVal (Internal.retainedNodes result.finalState.checked [])
      retainedExact _

private theorem filter_true_eq_self (values : List α) :
    values.filter (fun _ => true) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction => simp [induction]

/-- Exact final-deletion landing for every node present after all splices.
Because exhausted-wire deletion removes no nodes, this is the direct terminal
dense-index cast rather than an independently searched transport. -/
def plainBoundNodeImage
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.NodeId → result.plainFinal.val.NodeId :=
  Fin.cast (by
    unfold plainFinal boundFinal
    rw [result.finalRemoval.generated]
    symm
    simp [Internal.batchRemovalCandidate, Internal.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange,
      filter_true_eq_self])

theorem plainBoundNodeImage_eq_allNodeImage
    (result : RelationJoinResult source wire content parameters)
    (node : result.boundFinal.val.NodeId) :
    result.plainBoundNodeImage node =
      result.finalRemoval.allNodeImage node := by
  apply Fin.ext
  exact (result.finalRemoval_allNodeImage_val node).symm

theorem plainBoundNodeImage_injective
    (result : RelationJoinResult source wire content parameters) :
    Function.Injective result.plainBoundNodeImage := by
  intro left right same
  apply Fin.ext
  simpa [plainBoundNodeImage] using congrArg Fin.val same

/-- Final exhausted-relation deletion preserves every node constructor and
payload while transporting its sole region carrier. -/
theorem plainBoundNodeImage_data
    (result : RelationJoinResult source wire content parameters)
    (node : result.boundFinal.val.NodeId) :
    result.plainFinal.val.nodes (result.plainBoundNodeImage node) =
      (result.boundFinal.val.nodes node).relocate
        (result.plainBoundRegionImage
          (result.boundFinal.val.nodes node).region) := by
  have nodeImageExact :
      result.plainBoundNodeImage node =
        result.finalRemoval.allNodeImage node := by
    exact result.plainBoundNodeImage_eq_allNodeImage node
  rw [nodeImageExact]
  unfold plainBoundRegionImage
  rw [result.finalRemoval.allNodeImageExact,
      result.finalRemoval.allRegionImageExact]
  change result.plainFinal.val.nodes
      (Internal.checkedNode result.finalRemoval.generated _) = _
  rw [Internal.checkedNode_data_transport]
  let target := Internal.retainedNodeIndex result.boundFinal [] node (by
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin])
  change Internal.checkedNodeData result.finalRemoval.generated
      (Internal.batchNodeTable result.finalRemoval.plan target) = _
  rw [Internal.batchNodeTable_retained_data]
  have sourceAt :
      Internal.sourceRetainedNode result.boundFinal [] target = node :=
    DenseList.get_index _ _ _
  have transported_congr :
      ∀ (left right : result.boundFinal.val.NodeId)
        (leftRegion : (result.boundFinal.val.nodes left).region ∈
          Internal.retainedRegions result.boundFinal [])
        (rightRegion : (result.boundFinal.val.nodes right).region ∈
          Internal.retainedRegions result.boundFinal []),
        left = right →
          Internal.checkedNodeData result.finalRemoval.generated
              ((result.boundFinal.val.nodes left).relocate
                (Internal.retainedRegionIndex result.boundFinal []
                  (result.boundFinal.val.nodes left).region leftRegion)) =
            (result.boundFinal.val.nodes right).relocate
              (Internal.checkedRegion result.finalRemoval.generated
                (Internal.retainedRegionIndex result.boundFinal []
                  (result.boundFinal.val.nodes right).region rightRegion)) := by
    intro left right leftRegion rightRegion same
    subst right
    exact Internal.checkedNodeData_relocate _ _ _
  exact transported_congr _ _
    (result.finalRemoval.plan.nodeRegionRetained target)
    (by simp [Internal.retainedRegions, ConcreteDiagram.regionsList,
      Data.Finite.mem_allFin]) sourceAt

/-- Exact final-deletion landing for every surviving post-splice wire. -/
def plainBoundWireImage
    (result : RelationJoinResult source wire content parameters)
    (boundWire : result.boundFinal.val.WireId)
    (survives : boundWire ≠ result.boundDying) :
    result.plainFinal.val.WireId :=
  result.finalRemoval.allWireImage boundWire survives

theorem plainBoundWireImage_injective
    (result : RelationJoinResult source wire content parameters)
    {left right : result.boundFinal.val.WireId}
    (leftSurvives : left ≠ result.boundDying)
    (rightSurvives : right ≠ result.boundDying)
    (same :
      result.plainBoundWireImage left leftSurvives =
        result.plainBoundWireImage right rightSurvives) :
    left = right :=
  result.finalRemoval.allWireImage_injective leftSurvives rightSurvives same

theorem plainBoundWireImage_signature
    (result : RelationJoinResult source wire content parameters)
    (boundWire : result.boundFinal.val.WireId)
    (survives : boundWire ≠ result.boundDying) :
    (result.plainFinal.val.wires
      (result.plainBoundWireImage boundWire survives)).sig =
        (result.boundFinal.val.wires boundWire).sig := by
  unfold plainBoundWireImage
  rw [result.finalRemoval.allWireImageExact]
  change (result.plainFinal.val.wires
    (Internal.checkedWire result.finalRemoval.generated _)).sig = _
  rw [Internal.checkedWire_signature_transport]
  let target := Internal.retainedWireIndex result.boundFinal
    [result.boundDying] boundWire (by
      simp [Internal.retainedWires, ConcreteDiagram.wiresList,
        Data.Finite.mem_allFin, survives])
  change (Internal.batchWireTable result.finalRemoval.plan target).sig = _
  rw [Internal.batchWireTable_signature]
  have sourceAt : Internal.sourceRetainedWire result.boundFinal
      [result.boundDying] target = boundWire := DenseList.get_index _ _ _
  change Internal.sourceRetainedWire result.finalState.checked
      [result.finalState.wireImage wire] target = boundWire at sourceAt
  rw [sourceAt]
  rfl

theorem plainBoundWireImage_scope
    (result : RelationJoinResult source wire content parameters)
    (boundWire : result.boundFinal.val.WireId)
    (survives : boundWire ≠ result.boundDying) :
    (result.plainFinal.val.wires
      (result.plainBoundWireImage boundWire survives)).scope =
        result.plainBoundRegionImage
          (result.boundFinal.val.wires boundWire).scope := by
  unfold plainBoundWireImage plainBoundRegionImage
  rw [result.finalRemoval.allWireImageExact,
    result.finalRemoval.allRegionImageExact]
  change (result.plainFinal.val.wires
    (Internal.checkedWire result.finalRemoval.generated _)).scope = _
  rw [Internal.checkedWire_scope_transport]
  let target := Internal.retainedWireIndex result.boundFinal
    [result.boundDying] boundWire (by
      simp [Internal.retainedWires, ConcreteDiagram.wiresList,
        Data.Finite.mem_allFin, survives])
  change Internal.checkedRegion result.finalRemoval.generated
      (Internal.batchWireTable result.finalRemoval.plan target).scope = _
  rw [Internal.batchWireTable_scope]
  have sourceAt : Internal.sourceRetainedWire result.boundFinal
      [result.boundDying] target = boundWire := DenseList.get_index _ _ _
  change Internal.sourceRetainedWire result.finalState.checked
      [result.finalState.wireImage wire] target = boundWire at sourceAt
  have scope_congr :
      ∀ (left right : result.finalState.checked.val.WireId)
        (leftScope : (result.finalState.checked.val.wires left).scope ∈
          Internal.retainedRegions result.finalState.checked [])
        (rightScope : (result.finalState.checked.val.wires right).scope ∈
          Internal.retainedRegions result.finalState.checked []),
        left = right →
          Internal.checkedRegion result.finalRemoval.generated
              (Internal.retainedRegionIndex result.finalState.checked []
                (result.finalState.checked.val.wires left).scope leftScope) =
            Internal.checkedRegion result.finalRemoval.generated
              (Internal.retainedRegionIndex result.finalState.checked []
                (result.finalState.checked.val.wires right).scope
                rightScope) := by
    intro left right leftScope rightScope same
    subst right
    rfl
  exact scope_congr _ _
    (result.finalRemoval.plan.wireScopeRetained target)
    (by simp [Internal.retainedRegions, ConcreteDiagram.regionsList,
      Data.Finite.mem_allFin]) sourceAt

/-- Final exhausted-wire deletion preserves every endpoint of each surviving
bound wire, transporting only the dense node carrier. -/
theorem plainBoundWireImage_endpoint_mem
    (result : RelationJoinResult source wire content parameters)
    (boundWire : result.boundFinal.val.WireId)
    (survives : boundWire ≠ result.boundDying)
    (endpoint : CEndpoint result.boundFinal.val.nodeCount)
    (incident : endpoint ∈
      (result.boundFinal.val.wires boundWire).endpoints) :
    ({ node := result.plainBoundNodeImage endpoint.node
       port := endpoint.port } : CEndpoint result.plainFinal.val.nodeCount) ∈
      (result.plainFinal.val.wires
        (result.plainBoundWireImage boundWire survives)).endpoints := by
  have wireMember : boundWire ∈
      Internal.retainedWires result.boundFinal [result.boundDying] := by
    simp [Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  have nodeMember : endpoint.node ∈
      Internal.retainedNodes result.boundFinal [] := by
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin]
  have raw := Internal.batchWireTable_endpoint_mem
    result.finalRemoval.plan boundWire wireMember endpoint nodeMember incident
  have checked :
      Internal.checkedEndpoint result.finalRemoval.generated
          { node := Internal.retainedNodeIndex result.boundFinal []
              endpoint.node nodeMember
            port := endpoint.port } ∈
        (result.plainFinal.val.wires
          (Internal.checkedWire result.finalRemoval.generated
            (Internal.retainedWireIndex result.boundFinal
              [result.boundDying] boundWire wireMember))).endpoints := by
    rw [Internal.checkedWire_endpoints_transport]
    exact List.mem_map.mpr ⟨_, raw, rfl⟩
  simpa [plainBoundWireImage,
    result.plainBoundNodeImage_eq_allNodeImage,
    result.finalRemoval.allWireImageExact,
    result.finalRemoval.allNodeImageExact] using checked

/-- Final exhausted-wire deletion preserves the complete ordered endpoint
table of each surviving wire, transporting only its dense node carrier. -/
theorem plainBoundWireImage_endpoints
    (result : RelationJoinResult source wire content parameters)
    (boundWire : result.boundFinal.val.WireId)
    (survives : boundWire ≠ result.boundDying) :
    (result.plainFinal.val.wires
      (result.plainBoundWireImage boundWire survives)).endpoints =
        (result.boundFinal.val.wires boundWire).endpoints.map fun endpoint =>
          ({ node := result.plainBoundNodeImage endpoint.node
             port := endpoint.port } :
            CEndpoint result.plainFinal.val.nodeCount) := by
  unfold plainBoundWireImage
  rw [result.finalRemoval.allWireImageExact]
  simp only [result.plainBoundNodeImage_eq_allNodeImage]
  change (result.plainFinal.val.wires
      (Internal.checkedWire result.finalRemoval.generated _)).endpoints = _
  rw [Internal.checkedWire_endpoints_transport]
  let wireMember : boundWire ∈
      Internal.retainedWires result.boundFinal [result.boundDying] := by
    simp [Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  let target := Internal.retainedWireIndex result.boundFinal
    [result.boundDying] boundWire wireMember
  change (Internal.batchWireTable result.finalRemoval.plan target).endpoints.map
      (Internal.checkedEndpoint result.finalRemoval.generated) = _
  unfold Internal.batchWireTable
  have sourceAt :
      Internal.sourceRetainedWire result.boundFinal [result.boundDying]
        target = boundWire :=
    DenseList.get_index _ _ _
  change Internal.sourceRetainedWire result.finalState.checked
      [result.finalState.wireImage wire] target = boundWire at sourceAt
  simp only [sourceAt]
  change ((result.boundFinal.val.wires boundWire).endpoints.filterMap
      (Internal.batchEndpoint? result.boundFinal [])).map
        (Internal.checkedEndpoint result.finalRemoval.generated) = _
  have endpointExact
      (endpoint : CEndpoint result.boundFinal.val.nodeCount) :
      Internal.batchEndpoint? result.boundFinal [] endpoint =
        some
          ({ node := Internal.retainedNodeIndex result.boundFinal []
                endpoint.node (by
                  simp [Internal.retainedNodes,
                    ConcreteDiagram.nodesList,
                    Data.Finite.mem_allFin])
             port := endpoint.port } :
            CEndpoint (Internal.retainedNodes result.boundFinal []).length) := by
    unfold Internal.batchEndpoint?
    rw [dif_pos]
  have nodeImageExact (node : result.boundFinal.val.NodeId) :
      result.finalRemoval.allNodeImage node =
        Internal.checkedNode result.finalRemoval.generated
          (Internal.retainedNodeIndex result.boundFinal [] node (by
            simp [Internal.retainedNodes,
              ConcreteDiagram.nodesList,
              Data.Finite.mem_allFin])) :=
    result.finalRemoval.allNodeImageExact node
  induction (result.boundFinal.val.wires boundWire).endpoints with
  | nil => rfl
  | cons endpoint endpoints ih =>
      have ih' := ih
      simp only [nodeImageExact] at ih'
      simp [endpointExact, nodeImageExact]
      exact congrArg (List.cons _) ih'

/-- Ordered occurrence-removal/splice steps retained by the accepted join. -/
def steps
    (result : RelationJoinResult source wire content parameters) :
    List (RelationJoinStep source wire content) :=
  result.finalState.steps

/-- Exact dense source-region landing after final exhausted-wire deletion. -/
def plainRegionImage
    (result : RelationJoinResult source wire content parameters) :
    source.val.RegionId → result.plainFinal.val.RegionId :=
  result.finalRemoval.regionImage

/-- Exact dense surviving-wire landing after deleting the exhausted relation. -/
def plainWireImage
    (result : RelationJoinResult source wire content parameters)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ wire) :
    result.plainFinal.val.WireId :=
  result.finalRemoval.wireImage sourceWire survives

theorem final_deletion_exact
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val =
      ConcreteDiagram.DenseErasure.eraseWireCandidate
        result.boundFinal result.boundDying := by
  unfold plainFinal; rw [result.finalRemoval.generated]
  unfold boundFinal boundDying Internal.batchRemovalCandidate
    ConcreteDiagram.DenseErasure.eraseWireCandidate
    Internal.batchRegionTable Internal.batchNodeTable Internal.batchWireTable Internal.batchEndpoint?
  unfold Internal.retainedRegionIndex Internal.retainedNodeIndex
    Internal.sourceRetainedRegion Internal.sourceRetainedNode Internal.sourceRetainedWire
    DenseList.index
  unfold Internal.retainedRegions Internal.retainedNodes Internal.retainedWires
    ConcreteDiagram.DenseErasure.retainedWires
  congr 1
  funext target
  split
  · rename_i equation
    simp only [equation]
  · rename_i parent equation
    simp only [equation]

theorem plainFinal_regionCount
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.regionCount = result.boundFinal.val.regionCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  exact Internal.batchRemovalCandidate_regionCount_noRegions
    result.finalRemoval.plan

theorem plainFinal_nodeCount
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.nodeCount = result.boundFinal.val.nodeCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  simp [Internal.batchRemovalCandidate, Internal.retainedNodes,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange,
    filter_true_eq_self]

@[simp] theorem plainBoundNodeImage_val
    (result : RelationJoinResult source wire content parameters)
    (node : result.boundFinal.val.NodeId) :
    (result.plainBoundNodeImage node).val = node.val := by
  rfl

theorem plainFinal_wireCount_add_one
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.wireCount + 1 =
      result.boundFinal.val.wireCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  have countExact :=
    filter_ne_length_add_one_of_nodup_mem
      (by simpa [ConcreteDiagram.wiresList] using
        Data.Finite.allFin_nodup result.finalState.checked.val.wireCount)
      (result.finalState.wireImage wire)
      (Data.Finite.mem_allFin (result.finalState.wireImage wire))
  simpa [Internal.batchRemovalCandidate, Internal.retainedWires,
    ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange] using countExact

/-- The accepted construction's sole exact region/node atlas authority. -/
def constructionAtlas
    (result : RelationJoinResult source wire content parameters) :
    CertifiedAtlas (source := source) (dying := wire) (content := content)
      result.steps result.boundFinal :=
  result.finalState.atlas

/-- The accepted construction's sole data-bearing trace authority. -/
def construction_trace
    (result : RelationJoinResult source wire content parameters) :
    RelationJoinConstructionTrace source wire content parameters result.args
      result.steps result.boundFinal result.constructionAtlas
        result.boundWireImage result.boundDying
        (result.constructionAtlas.regionImage
          (source.val.wires wire).scope) :=
  result.finalState.constructionTrace

end FinalDeletion

theorem relation_signature
    (result : RelationJoinResult source wire content parameters) :
    (source.val.wires wire).sig = .rel result.args :=
  result.plan.relationSignature

theorem boundary_exact
    (result : RelationJoinResult source wire content parameters) :
    result.boundarySignatures =
      result.args ++ result.parameterSignatures :=
  result.plan.boundaryExact

theorem parameters_survive
    (result : RelationJoinResult source wire content parameters)
    (position : Fin parameters.length) :
    parameters.get position ≠ wire :=
  result.plan.parametersSurvive position

theorem initial_exact
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    result.initialChecked = source :=
  result.initial.checkedExact

theorem applications_complete
    (result : RelationJoinResult source wire content parameters) :
    result.applications =
      result.plan.applications.map RelationJoinApplication.node := by
  unfold applications
  calc
    result.finalState.processed =
        result.initial.state.processed ++
          result.plan.applications.map RelationJoinApplication.node :=
      spliceRelationApplications_processed source wire content parameters
        result.plan.args result.initial.state result.finalState
        result.plan.applications result.batchAccepted
    _ = result.plan.applications.map RelationJoinApplication.node := by
      rw [result.initial.processedEmpty]
      simp

/--
The accepted join retains its application order exactly: it is the source
node-storage order filtered by incidence at the dying wire.  This positional
equation is the bridge used by batch reconstruction; no later consumer needs
to rediscover which splice step belongs to which source application.
-/
theorem applications_storage_order
    (result : RelationJoinResult source wire content parameters) :
    result.applications =
      source.val.nodesList.filter fun node =>
        decide
          ((⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
            (source.val.wires wire).endpoints) := by
  rw [result.applications_complete]
  have mapped :=
    relationJoinApplications?_nodes source result.args
      (relationApplicationNodes source wire) result.plan.applications
      (by
        simpa [relationJoinApplications?] using
          result.plan.applicationsExact)
  simpa [relationApplicationNodes] using mapped

/-- The retained splice trace has exactly one step per accepted application. -/
theorem steps_application_order
    (result : RelationJoinResult source wire content parameters) :
    result.steps.map RelationJoinStep.application = result.applications :=
  result.finalState.traceExact

theorem endpoint_applied
    (result : RelationJoinResult source wire content parameters)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires wire).endpoints) :
    endpoint.port = .head ∧
      ∃ region,
        source.val.nodes endpoint.node = .atom region result.args := by
  have accepted :=
    (List.all_eq_true.mp result.plan.endpointsApplied) endpoint member
  unfold relationEndpointIsApplied at accepted
  cases portData : endpoint.port <;>
    cases nodeData : source.val.nodes endpoint.node <;>
    simp [portData, nodeData] at accepted
  rename_i region nodeArgs
  exact
    ⟨rfl, region, by
      simpa [args, accepted] using nodeData⟩

end RelationJoinResult

/-- Ground one relation wire by deleting all of its applied-head atoms,
splicing the supplied checked-open content at every application in source
node order, and deleting the exhausted relation wire. -/
def joinRelation
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except Error (RelationJoinResult source wire content parameters) := by
  match prepared :
      checkRelationJoinPlan source wire content parameters with
  | .error error =>
      exact .error error
  | .ok plan =>
      let initial :=
        relationJoinInitialState source wire content parameters plan
      match batchAccepted :
          spliceRelationApplications source wire content parameters plan.args
            initial.state plan.applications with
      | .error error =>
          exact .error error
      | .ok finalState =>
          match removed : removeRelationJoinWire finalState with
          | .error error =>
              exact .error error
          | .ok finalRemoval =>
              exact .ok
                (RelationJoinResult.mk plan initial finalState batchAccepted
                  finalRemoval)

end ConcreteWireQuantifier

end VisualProof
