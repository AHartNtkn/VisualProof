import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

namespace ConcreteWireQuantifier

private structure RelationJoinApplication
    (source : CheckedDiagram definitions) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId

def relationArgumentWires?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List Sig → Nat → Option (List source.val.WireId)
  | [], _ => some []
  | expected :: rest, position => do
      let wire ← source.val.endpointOwner? ⟨node, .arg position⟩
      if (source.val.wires wire).sig = expected then
        let tail ← relationArgumentWires? source node rest (position + 1)
        pure (wire :: tail)
      else
        none

private def relationEndpointIsApplied
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (endpoint : CEndpoint source.val.nodeCount) : Bool :=
  match endpoint.port, source.val.nodes endpoint.node with
  | .head, .atom _ nodeArgs => decide (nodeArgs = args)
  | _, _ => false

private def relationApplicationNodes
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (
      (⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires wire).endpoints)

private def relationJoinApplicationAt?
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (node : source.val.NodeId) :
    Option (RelationJoinApplication source) := do
  match source.val.nodes node with
  | .atom region nodeArgs =>
      if nodeArgs = args then
        let arguments ← relationArgumentWires? source node args 0
        pure { node := node, region := region, arguments := arguments }
      else
        none
  | _ => none

private def relationJoinApplications?
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (args : List Sig) :
    Option (List (RelationJoinApplication source)) :=
  (relationApplicationNodes source wire).mapM
    (relationJoinApplicationAt? source args)

private theorem relationJoinApplicationAt?_node
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (node : source.val.NodeId)
    (application : RelationJoinApplication source)
    (accepted :
      relationJoinApplicationAt? source args node = some application) :
    application.node = node := by
  unfold relationJoinApplicationAt? at accepted
  split at accepted <;> simp_all
  rename_i region nodeArgs nodeExact
  rcases accepted with ⟨_, accepted⟩
  change
    (relationArgumentWires? source node args 0).bind
        (fun arguments =>
          some
            { node := node
              region := region
              arguments := arguments }) =
      some application at accepted
  rw [Option.bind_eq_some_iff] at accepted
  obtain ⟨arguments, _, accepted⟩ := accepted
  simp only [Option.some.injEq] at accepted
  subst application
  rfl

private theorem relationJoinApplications?_nodes
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (nodes : List source.val.NodeId)
    (applications : List (RelationJoinApplication source))
    (accepted :
      nodes.mapM (relationJoinApplicationAt? source args) =
        some applications) :
    applications.map RelationJoinApplication.node = nodes := by
  induction nodes generalizing applications with
  | nil =>
      simp at accepted
      subst applications
      rfl
  | cons node nodes induction =>
      rw [List.mapM_cons] at accepted
      change
        (relationJoinApplicationAt? source args node).bind
            (fun application =>
              (List.mapM (relationJoinApplicationAt? source args) nodes).bind
                (fun tail => some (application :: tail))) =
          some applications at accepted
      rw [Option.bind_eq_some_iff] at accepted
      obtain ⟨application, applicationAccepted, accepted⟩ := accepted
      rw [Option.bind_eq_some_iff] at accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := accepted
      simp only [Option.some.injEq] at accepted
      subst applications
      simp only [List.map_cons, List.cons.injEq]
      exact
        ⟨relationJoinApplicationAt?_node source args node application
            applicationAccepted,
          induction tail tailAccepted⟩

private def openBoundarySigs
    (content : CheckedOpenDiagram definitions) :
    List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

private def parameterSigs
    (source : CheckedDiagram definitions)
    (parameters : List source.val.WireId) :
    List Sig :=
  parameters.map fun wire => (source.val.wires wire).sig

private structure RelationJoinPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  args : List Sig
  relationSignature : (source.val.wires wire).sig = .rel args
  endpointsApplied :
    (source.val.wires wire).endpoints.all
        (relationEndpointIsApplied source args) = true
  applications : List (RelationJoinApplication source)
  applicationsExact :
    relationJoinApplications? source wire args = some applications
  boundaryExact :
    openBoundarySigs content = args ++ parameterSigs source parameters
  parametersSurvive :
    ∀ position : Fin parameters.length,
      parameters.get position ≠ wire

private def firstBoundaryMismatch
    (actual expected : List Sig) : Nat :=
  ((List.range (max actual.length expected.length)).find? fun position =>
    actual[position]? != expected[position]?).getD 0

private def checkRelationJoinPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except Error (RelationJoinPlan source wire content parameters) := by
  match relationData : (source.val.wires wire).sig with
  | .iota =>
      exact .error (.expectedRelation wire.val)
  | .rel args =>
      if parametersSurvive :
          parameters.all fun parameter => decide (parameter ≠ wire) then
        let expected := args ++ parameterSigs source parameters
        if arity : (openBoundarySigs content).length = expected.length then
          if boundaryExact : openBoundarySigs content = expected then
            if endpointsApplied :
                (source.val.wires wire).endpoints.all
                    (relationEndpointIsApplied source args) = true then
              match applicationsAccepted :
                  relationJoinApplications? source wire args with
              | none =>
                  exact .error (.invalidApplication 0)
              | some applications =>
                  exact .ok
                    { args := args
                      relationSignature := relationData
                      endpointsApplied := endpointsApplied
                      applications := applications
                      applicationsExact := applicationsAccepted
                      boundaryExact := boundaryExact
                      parametersSurvive := by
                        intro position
                        exact of_decide_eq_true
                          ((List.all_eq_true.mp parametersSurvive)
                            (parameters.get position)
                            (List.get_mem _ position)) }
            else
              match (source.val.wires wire).endpoints.find? fun endpoint =>
                  !relationEndpointIsApplied source args endpoint with
              | some endpoint =>
                  exact .error
                    (.nonAppliedEndpoint endpoint.node.val endpoint.port)
              | none =>
                  exact .error .invalidRemoval
          else
            exact .error
              (.boundarySignatureMismatch
                (firstBoundaryMismatch
                  (openBoundarySigs content) expected))
        else
          exact .error .boundaryArityMismatch
      else
        exact .error .dyingWireParameter

structure RelationJoinStep
    (source : CheckedDiagram definitions)
    (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions) : Type where
  private mk ::
  application : source.val.NodeId
  sourceRegion : source.val.RegionId
  sourceArguments : List source.val.WireId
  sourceParameters : List source.val.WireId
  sourceAttachments : List source.val.WireId
  sourceAttachmentsExact :
    sourceAttachments = sourceArguments ++ sourceParameters
  sourceAttachmentArity :
    sourceAttachments.length = content.val.boundary.length
  sourceAttachmentsSurvive :
    ∀ position : Fin sourceAttachments.length,
      sourceAttachments.get position ≠ dying
  relationArgs : List Sig
  prior : CheckedDiagram definitions
  priorApplication : prior.val.NodeId
  priorRegionImage : source.val.RegionId → prior.val.RegionId
  priorRegionImageEncloses :
    ∀ outer inner,
      prior.val.Encloses
          (priorRegionImage outer) (priorRegionImage inner) ↔
        source.val.Encloses outer inner
  priorWireImage : source.val.WireId → prior.val.WireId
  priorWireScopeExact :
    ∀ sourceWire,
      (prior.val.wires (priorWireImage sourceWire)).scope =
        priorRegionImage (source.val.wires sourceWire).scope
  priorNodeExact :
    prior.val.nodes priorApplication =
      .atom (priorRegionImage sourceRegion) relationArgs
  priorSite : SiteCompilation prior (priorRegionImage sourceRegion)
  priorDyingOwner :
    prior.val.endpointOwner? ⟨priorApplication, .head⟩ =
      some (priorWireImage dying)
  priorArguments : List prior.val.WireId
  priorArgumentsAccepted :
    relationArgumentWires? prior priorApplication relationArgs 0 =
      some priorArguments
  priorArgumentsExact :
    priorArguments = sourceArguments.map priorWireImage
  private removal :
    Internal.BatchRemovalPlan prior [] [priorApplication] []
  base : CheckedDiagram definitions
  private baseGenerated :
    base.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        prior priorApplication
  baseRegionImage : source.val.RegionId → base.val.RegionId
  baseRegionImageExact :
    ∀ region,
      baseRegionImage region =
        Internal.checkedRegion baseGenerated
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            prior priorApplication (priorRegionImage region))
  baseWireImage : source.val.WireId → base.val.WireId
  baseWireImageExact :
    ∀ sourceWire,
      baseWireImage sourceWire =
        Internal.checkedWire baseGenerated
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
            prior priorApplication (priorWireImage sourceWire))
  baseWireScopeExact :
    ∀ sourceWire,
      (base.val.wires (baseWireImage sourceWire)).scope =
        baseRegionImage (source.val.wires sourceWire).scope
  site : base.val.RegionId
  siteExact : site = baseRegionImage sourceRegion
  attachment : ConcreteSpliceAttachment base site content
  targetExact :
    ∀ position : Fin content.val.boundary.length,
      attachment.target position =
        baseWireImage
          (sourceAttachments.get
            (Fin.cast sourceAttachmentArity.symm position))
  checked : CheckedDiagram definitions
  private attachmentAccepted :
    checkConcreteSpliceAttachment base site content attachment.target =
      some attachment
  private generated : checked.val = attachment.diagram
  checkedRegionImage : source.val.RegionId → checked.val.RegionId
  checkedRegionImageExact :
    ∀ region,
      checkedRegionImage region =
        Fin.cast
          (congrArg ConcreteDiagram.regionCount generated).symm
          (attachment.hostRegion (baseRegionImage region))
  checkedRegionImageEncloses :
    ∀ outer inner,
      checked.val.Encloses
          (checkedRegionImage outer) (checkedRegionImage inner) ↔
        source.val.Encloses outer inner
  checkedWireImage : source.val.WireId → checked.val.WireId
  checkedWireImageExact :
    ∀ sourceWire,
      checkedWireImage sourceWire =
        Fin.cast
          (congrArg ConcreteDiagram.wireCount generated).symm
          (attachment.hostWire (baseWireImage sourceWire))
  checkedWireScopeExact :
    ∀ sourceWire,
      (checked.val.wires (checkedWireImage sourceWire)).scope =
        checkedRegionImage (source.val.wires sourceWire).scope

namespace RelationJoinStep

theorem attachment_accepted
    (step : RelationJoinStep source dying content) :
    checkConcreteSpliceAttachment step.base step.site content
        step.attachment.target =
      some step.attachment :=
  step.attachmentAccepted

theorem checked_generated
    (step : RelationJoinStep source dying content) :
    step.checked.val = step.attachment.diagram :=
  step.generated

theorem base_generated
    (step : RelationJoinStep source dying content) :
    step.base.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        step.prior step.priorApplication :=
  step.baseGenerated

theorem baseRegionImageEncloses
    (step : RelationJoinStep source dying content)
    (outer inner : source.val.RegionId) :
    step.base.val.Encloses
        (step.baseRegionImage outer) (step.baseRegionImage inner) ↔
      source.val.Encloses outer inner := by
  rw [step.baseRegionImageExact, step.baseRegionImageExact]
  rw [Internal.checkedRegion_encloses]
  rw [
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_encloses_iff]
  exact step.priorRegionImageEncloses outer inner

@[simp] theorem baseWire_signature
    (step : RelationJoinStep source dying content)
    (sourceWire : source.val.WireId) :
    (step.prior.val.wires (step.priorWireImage sourceWire)).sig =
      (step.base.val.wires (step.baseWireImage sourceWire)).sig := by
  rw [step.baseWireImageExact, Internal.checkedWire_signature_transport]
  exact
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire_signature
      step.prior step.priorApplication
        (step.priorWireImage sourceWire)).symm

theorem prior_dying_scope_encloses_site
    (step : RelationJoinStep source dying content) :
    step.prior.val.Encloses
        (step.priorRegionImage (source.val.wires dying).scope)
        (step.priorRegionImage step.sourceRegion) := by
  have occurrence :=
    ConcreteDiagram.endpointOwner?_occurs step.prior.val
      ⟨step.priorApplication, .head⟩ (step.priorWireImage dying)
      step.priorDyingOwner
  have checked :=
    (List.all_eq_true.mp step.prior.property.wire_scopes_enclose)
      (step.priorWireImage dying, ⟨step.priorApplication, .head⟩)
      occurrence
  have encloses :
      step.prior.val.Encloses
        (step.prior.val.wires (step.priorWireImage dying)).scope
        (step.prior.val.nodes step.priorApplication).region :=
    of_decide_eq_true checked
  rw [step.priorWireScopeExact dying, step.priorNodeExact] at encloses
  exact encloses

@[simp] theorem checked_dying_scope
    (step : RelationJoinStep source dying content) :
    (step.checked.val.wires (step.checkedWireImage dying)).scope =
      step.checkedRegionImage (source.val.wires dying).scope :=
  step.checkedWireScopeExact dying

end RelationJoinStep

inductive RelationJoinSemanticTrace
    (source : CheckedDiagram definitions) (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) (args : List Sig) :
    (steps : List (RelationJoinStep source dying content)) →
    (final : CheckedDiagram definitions) →
    (source.val.RegionId → final.val.RegionId) →
    (source.val.WireId → final.val.WireId) →
    final.val.WireId → final.val.RegionId → Prop
  | nil :
      RelationJoinSemanticTrace source dying content parameters args []
        source id id dying (source.val.wires dying).scope
  | snoc
      {steps current currentRegionImage currentWireImage
        currentDying currentScope}
      (trace :
        RelationJoinSemanticTrace source dying content parameters args steps
          current currentRegionImage currentWireImage currentDying currentScope)
      (step : RelationJoinStep source dying content)
      (_ : step.prior = current)
      (_ : HEq step.priorRegionImage currentRegionImage)
      (_ : HEq step.priorWireImage currentWireImage)
      (_ : HEq (step.priorWireImage dying) currentDying)
      (_ : HEq
        (step.priorRegionImage (source.val.wires dying).scope) currentScope)
      (_ : step.relationArgs = args)
      (_ : step.sourceParameters = parameters) :
      RelationJoinSemanticTrace source dying content parameters args
        (steps ++ [step]) step.checked step.checkedRegionImage
        step.checkedWireImage (step.checkedWireImage dying)
        (step.checkedRegionImage (source.val.wires dying).scope)

private theorem checkedWire_injective
    {definitions : List (List Sig)}
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Function.Injective (Internal.checkedWire generated) := by
  intro left right same
  apply Fin.ext
  simpa [Internal.checkedWire] using congrArg Fin.val same

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
  regionImage : source.val.RegionId → checked.val.RegionId
  regionImage_encloses :
    ∀ outer inner,
      checked.val.Encloses (regionImage outer) (regionImage inner) ↔
        source.val.Encloses outer inner
  wireImage : source.val.WireId → checked.val.WireId
  wireImage_injective : Function.Injective wireImage
  wireScopeExact :
    ∀ sourceWire,
      (checked.val.wires (wireImage sourceWire)).scope =
        regionImage (source.val.wires sourceWire).scope
  nodeImage : source.val.NodeId → Option checked.val.NodeId
  processed : List source.val.NodeId
  steps : List (RelationJoinStep source dying content)
  traceExact :
    steps.map RelationJoinStep.application = processed
  semanticTrace :
    RelationJoinSemanticTrace source dying content parameters args steps
      checked regionImage wireImage (wireImage dying)
        (regionImage (source.val.wires dying).scope)

private structure RelationJoinStepResult
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source dying content parameters args)
    (application : RelationJoinApplication source) : Type where
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
      regionImage := id
      regionImage_encloses := fun _ _ => Iff.rfl
      wireImage := id
      wireImage_injective := Function.injective_id
      wireScopeExact := fun _ => rfl
      nodeImage := fun node => some node
      processed := []
      steps := []
      traceExact := rfl
      semanticTrace := .nil }
  exact
    { state := state
      checkedExact := rfl
      processedEmpty := rfl }

private def relationJoinAttachments
    {source : CheckedDiagram definitions}
    (application : RelationJoinApplication source)
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
    (application : RelationJoinApplication source) :
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
                      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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
                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
                                state.checked priorApplication
                                (state.regionImage region))
                        let baseWireImage :
                            source.val.WireId → base.val.WireId :=
                          fun sourceWire =>
                            Internal.checkedWire baseGenerated
                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
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
                                      ConcreteDiagram.IdentityNormalizationCore.retainedNodes
                                        state.checked.val [priorApplication] then
                                  some
                                    (Internal.checkedNode baseGenerated
                                      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
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
                                        ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate]
                                      have sourceExact :
                                          state.checked.val.wiresList.get
                                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
                                                state.checked priorApplication
                                                (state.wireImage sourceWire)) =
                                            state.wireImage sourceWire := by
                                        apply Fin.ext
                                        simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire,
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
                                        prior := state.checked
                                        priorApplication :=
                                          priorApplication
                                        priorRegionImage :=
                                          state.regionImage
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
                                          rw [ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_encloses_iff]
                                          exact
                                            state.regionImage_encloses
                                              outer inner
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
                                    let nextState :
                                        RelationJoinState source wire content
                                          parameters args :=
                                      { checked := next
                                        regionImage :=
                                          step.checkedRegionImage
                                        regionImage_encloses :=
                                          step.checkedRegionImageEncloses
                                        wireImage := step.checkedWireImage
                                        wireImage_injective := by
                                          intro left right same
                                          apply state.wireImage_injective
                                          apply
                                            ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire_injective
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
                                          step.checkedWireScopeExact
                                        nodeImage := fun sourceNode =>
                                          (baseNodeImage sourceNode).map
                                            fun baseNode =>
                                              Internal.checkedNode generated
                                                (attachment.hostNode
                                                  baseNode)
                                        processed :=
                                          state.processed ++
                                            [application.node]
                                        steps := state.steps ++ [step]
                                        traceExact := by
                                          simp [step, state.traceExact]
                                        semanticTrace :=
                                          .snoc state.semanticTrace step
                                            rfl (by simp [step]) (by simp [step])
                                            (by simp [step]) (by simp [step])
                                            rfl rfl }
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
      List (RelationJoinApplication source) →
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
    (applications : List (RelationJoinApplication source))
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

/-- Checked output of grounding every applied endpoint of one relation wire. -/
structure RelationJoinResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  applications : List source.val.NodeId
  wireImage :
    ∀ sourceWire : source.val.WireId,
      sourceWire ≠ wire → checked.val.WireId
  private plan : RelationJoinPlan source wire content parameters
  private initial : RelationJoinInitialResult plan
  private finalState :
    RelationJoinState source wire content parameters plan.args
  private batchAccepted :
    spliceRelationApplications source wire content parameters plan.args
        initial.state plan.applications =
      .ok finalState
  private finalRemoval : RelationJoinFinalRemoval finalState
  private normalization :
    ConcreteDiagram.IdentityNormalization finalRemoval.checked
  private normalizationExact :
    normalization =
      ConcreteDiagram.normalizeIdentities finalRemoval.checked
  private checkedExact : checked = normalization.target
  private applicationsExact :
    applications = finalState.processed

namespace RelationJoinResult

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

/-- Ordered occurrence-removal/splice steps retained by the accepted join. -/
def steps
    (result : RelationJoinResult source wire content parameters) :
    List (RelationJoinStep source wire content) :=
  result.finalState.steps

/-- Exact dense region landing before eager identity normalization. -/
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
      ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.boundFinal result.boundDying := by
  unfold plainFinal; rw [result.finalRemoval.generated]
  unfold boundFinal boundDying Internal.batchRemovalCandidate
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
    Internal.batchRegionTable Internal.batchNodeTable Internal.batchWireTable Internal.batchEndpoint?
  unfold Internal.retainedRegionIndex Internal.retainedNodeIndex
    Internal.sourceRetainedRegion Internal.sourceRetainedNode Internal.sourceRetainedWire
    DenseList.index
  unfold Internal.retainedRegions Internal.retainedNodes Internal.retainedWires
    ConcreteDiagram.IdentityNormalizationCore.retainedWires
  congr 1
  funext target
  split
  · rename_i equation
    simp only [equation]
  · rename_i parent equation
    simp only [equation]

@[simp] theorem bound_dying_scope
    (result : RelationJoinResult source wire content parameters) :
    (result.boundFinal.val.wires result.boundDying).scope =
      result.boundRegionImage (source.val.wires wire).scope :=
  result.finalState.wireScopeExact wire

theorem semantic_trace
    (result : RelationJoinResult source wire content parameters) :
    RelationJoinSemanticTrace source wire content parameters result.args
      result.steps result.boundFinal result.boundRegionImage
        result.boundWireImage result.boundDying
        (result.boundRegionImage (source.val.wires wire).scope) :=
  result.finalState.semanticTrace

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
  calc
    result.applications = result.finalState.processed :=
      result.applicationsExact
    _ =
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
  result.finalState.traceExact.trans result.applicationsExact.symm

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

theorem trace_complete
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    ∃ steps : List (RelationJoinStep source wire content),
      ∃ normalization :
          ConcreteDiagram.IdentityNormalization result.plainFinal,
        RelationJoinSemanticTrace source wire content parameters result.args
            steps result.boundFinal result.boundRegionImage
              result.boundWireImage result.boundDying
              (result.boundRegionImage (source.val.wires wire).scope) ∧
          steps.map RelationJoinStep.application =
            result.applications ∧
          normalization =
            ConcreteDiagram.normalizeIdentities result.plainFinal ∧
          normalization.target = result.checked := by
  refine
    ⟨result.finalState.steps, result.normalization,
      result.finalState.semanticTrace, ?_, result.normalizationExact,
      result.checkedExact.symm⟩
  exact
    result.finalState.traceExact.trans result.applicationsExact.symm

end RelationJoinResult

/--
Ground one relation wire by deleting all of its applied-head atoms, splicing
the supplied checked-open content at every application in source node order,
and deleting the exhausted relation wire.  Identity normalization runs once
after the complete ordered batch.
-/
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
              let normalization :=
                ConcreteDiagram.normalizeIdentities finalRemoval.checked
              exact .ok
                (RelationJoinResult.mk normalization.target
                  finalState.processed
                  (fun sourceWire different =>
                    normalization.wireImage
                      (finalRemoval.wireImage sourceWire different))
                  plan initial finalState batchAccepted finalRemoval
                  normalization rfl rfl rfl)

end ConcreteWireQuantifier

end VisualProof
