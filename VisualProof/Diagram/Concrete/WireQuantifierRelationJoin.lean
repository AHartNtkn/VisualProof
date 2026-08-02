import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

namespace ConcreteWireQuantifier

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

theorem relationArgumentWires?_length
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (args : List Sig)
    (start : Nat)
    (wires : List source.val.WireId)
    (accepted :
      relationArgumentWires? source node args start = some wires) :
    wires.length = args.length := by
  induction args generalizing start wires with
  | nil =>
      simp [relationArgumentWires?] at accepted
      subst wires
      rfl
  | cons expected rest induction =>
      simp only [relationArgumentWires?] at accepted
      change
        (source.val.endpointOwner? ⟨node, .arg start⟩).bind
            (fun wire =>
              if (source.val.wires wire).sig = expected then
                (relationArgumentWires? source node rest (start + 1)).bind
                  (fun tail => some (wire :: tail))
              else none) =
          some wires at accepted
      rw [Option.bind_eq_some_iff] at accepted
      obtain ⟨wire, owner, accepted⟩ := accepted
      split at accepted
      · rw [Option.bind_eq_some_iff] at accepted
        obtain ⟨tail, tailAccepted, accepted⟩ := accepted
        simp only [Option.some.injEq] at accepted
        subst wires
        simp [induction (start := start + 1) tail tailAccepted]
      · contradiction

theorem relationArgumentWires?_owner
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (args : List Sig)
    (start : Nat)
    (wires : List source.val.WireId)
    (accepted :
      relationArgumentWires? source node args start = some wires)
    (position : Fin args.length) :
    source.val.endpointOwner?
        ⟨node, .arg (start + position.val)⟩ =
      some
        (wires.get
          (Fin.cast
            (relationArgumentWires?_length source node args start wires
              accepted).symm
            position)) := by
  induction args generalizing start wires with
  | nil => exact Fin.elim0 position
  | cons expected rest induction =>
      simp only [relationArgumentWires?] at accepted
      change
        (source.val.endpointOwner? ⟨node, .arg start⟩).bind
            (fun wire =>
              if (source.val.wires wire).sig = expected then
                (relationArgumentWires? source node rest (start + 1)).bind
                  (fun tail => some (wire :: tail))
              else none) =
          some wires at accepted
      rw [Option.bind_eq_some_iff] at accepted
      obtain ⟨wire, owner, accepted⟩ := accepted
      split at accepted
      · rw [Option.bind_eq_some_iff] at accepted
        obtain ⟨tail, tailAccepted, accepted⟩ := accepted
        simp only [Option.some.injEq] at accepted
        subst wires
        refine Fin.cases ?_ (fun tailPosition => ?_) position
        · simpa using owner
        · have tailOwner :=
            induction (start := start + 1) tail tailAccepted tailPosition
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            tailOwner
      · simp at accepted

private structure RelationJoinApplication
    (source : CheckedDiagram definitions)
    (args : List Sig) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId
  nodeExact : source.val.nodes node = .atom region args
  argumentsAccepted :
    relationArgumentWires? source node args 0 = some arguments

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
    Option (RelationJoinApplication source args) :=
  match nodeData : source.val.nodes node with
  | .atom region nodeArgs =>
      if argsExact : nodeArgs = args then
        match accepted : relationArgumentWires? source node args 0 with
        | none => none
        | some arguments =>
            some
              { node := node
                region := region
                arguments := arguments
                nodeExact := by simpa [argsExact] using nodeData
                argumentsAccepted := accepted }
      else
        none
  | _ => none

private def relationJoinApplications?
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (args : List Sig) :
    Option (List (RelationJoinApplication source args)) :=
  (relationApplicationNodes source wire).mapM
    (relationJoinApplicationAt? source args)

private theorem relationJoinApplicationAt?_node
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (node : source.val.NodeId)
    (application : RelationJoinApplication source args)
    (accepted :
      relationJoinApplicationAt? source args node = some application) :
    application.node = node := by
  unfold relationJoinApplicationAt? at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · contradiction
      · cases accepted
        rfl
    · contradiction
  · contradiction

private theorem relationJoinApplications?_nodes
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (nodes : List source.val.NodeId)
    (applications : List (RelationJoinApplication source args))
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
  applications : List (RelationJoinApplication source args)
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
  relationArgs : List Sig
  sourceNodeExact : source.val.nodes application = .atom sourceRegion relationArgs
  sourceArguments : List source.val.WireId
  sourceArgumentsAccepted :
    relationArgumentWires? source application relationArgs 0 =
      some sourceArguments
  sourceParameters : List source.val.WireId
  sourceAttachments : List source.val.WireId
  sourceAttachmentsExact :
    sourceAttachments = sourceArguments ++ sourceParameters
  sourceAttachmentArity :
    sourceAttachments.length = content.val.boundary.length
  sourceAttachmentsSurvive :
    ∀ position : Fin sourceAttachments.length,
      sourceAttachments.get position ≠ dying
  prior : CheckedDiagram definitions
  priorApplication : prior.val.NodeId
  priorNodeImage : source.val.NodeId → Option prior.val.NodeId
  priorNodeImage_injective :
    ∀ {left right priorNode},
      priorNodeImage left = some priorNode →
      priorNodeImage right = some priorNode →
      left = right
  priorApplicationImage :
    priorNodeImage application = some priorApplication
  priorRegionImage : source.val.RegionId → prior.val.RegionId
  priorRegionImageVal : ∀ region, (priorRegionImage region).val = region.val
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
  baseNodeImage : source.val.NodeId → Option base.val.NodeId
  baseNodeImageExact :
    ∀ sourceNode,
      baseNodeImage sourceNode =
        match priorNodeImage sourceNode with
        | none => none
        | some priorNode =>
            if retained :
                priorNode ∈
                  ConcreteDiagram.IdentityNormalizationCore.retainedNodes
                    prior.val [priorApplication] then
              some
                (Internal.checkedNode baseGenerated
                  (ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
                    prior priorApplication priorNode retained))
            else
              none
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
  checkedNodeImage : source.val.NodeId → Option checked.val.NodeId
  checkedNodeImageExact :
    ∀ sourceNode,
      checkedNodeImage sourceNode =
        (baseNodeImage sourceNode).map fun baseNode =>
          Internal.checkedNode generated (attachment.hostNode baseNode)
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

/-- Transport any prior region through atom deletion and this splice. -/
def checkedPriorRegion
    (step : RelationJoinStep source dying content)
    (region : step.prior.val.RegionId) :
    step.checked.val.RegionId :=
  Fin.cast
    (congrArg ConcreteDiagram.regionCount step.generated).symm
    (step.attachment.hostRegion
      (Internal.checkedRegion step.baseGenerated
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication region)))

/-- Transport any non-application prior node through deletion and splice. -/
def checkedPriorNode
    (step : RelationJoinStep source dying content)
    (node : step.prior.val.NodeId)
    (different : node ≠ step.priorApplication) :
    step.checked.val.NodeId :=
  Fin.cast
    (congrArg ConcreteDiagram.nodeCount step.generated).symm
    (step.attachment.hostNode
      (Internal.checkedNode step.baseGenerated
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
          step.prior step.priorApplication node (by
            simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
              ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
              different]))))

/-- Transport any prior wire through atom deletion and this splice. -/
def checkedPriorWire
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    step.checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount step.generated).symm
    (step.attachment.hostWire
      (Internal.checkedWire step.baseGenerated
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
          step.prior step.priorApplication wire)))

/-- Allocate one fragment region in the checked splice target. -/
def checkedFragmentRegion
    (step : RelationJoinStep source dying content)
    (region : content.val.diagram.RegionId) :
    step.checked.val.RegionId :=
  Fin.cast
    (congrArg ConcreteDiagram.regionCount step.generated).symm
    (step.attachment.fragmentRegion region)

/-- Allocate one fragment node in the checked splice target. -/
def checkedFragmentNode
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    step.checked.val.NodeId :=
  Fin.cast
    (congrArg ConcreteDiagram.nodeCount step.generated).symm
    (step.attachment.fragmentNode node)

/-- Allocate one fragment wire in the checked splice target. -/
def checkedFragmentWire
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId) :
    step.checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount step.generated).symm
    (step.attachment.fragmentWire wire)

@[simp] theorem checkedPriorRegion_val
    (step : RelationJoinStep source dying content)
    (region : step.prior.val.RegionId) :
    (step.checkedPriorRegion region).val = region.val := by
  rfl

/-- A prior sheet remains a sheet through application deletion and splicing. -/
theorem checkedPriorRegion_sheet
    (step : RelationJoinStep source dying content)
    (region : step.prior.val.RegionId)
    (data : step.prior.val.regions region = .sheet) :
    step.checked.val.regions (step.checkedPriorRegion region) = .sheet := by
  unfold checkedPriorRegion
  apply Internal.checkedRegion_data_transport_sheet step.generated
  rw [ConcreteSpliceAttachment.diagram_region_hostRegion]
  have erased :=
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_sheet
      step.prior step.priorApplication region data
  have baseData := Internal.checkedRegion_data_transport_sheet
    step.baseGenerated _ erased
  rw [baseData]
  rfl

/-- A prior cut and its parent remain exact through application deletion and
splicing. -/
theorem checkedPriorRegion_cut
    (step : RelationJoinStep source dying content)
    (region parent : step.prior.val.RegionId)
    (data : step.prior.val.regions region = .cut parent) :
    step.checked.val.regions (step.checkedPriorRegion region) =
      .cut (step.checkedPriorRegion parent) := by
  unfold checkedPriorRegion
  apply Internal.checkedRegion_data_transport_cut step.generated
  rw [ConcreteSpliceAttachment.diagram_region_hostRegion]
  have erased :=
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_cut
      step.prior step.priorApplication region parent data
  have baseData := Internal.checkedRegion_data_transport_cut
    step.baseGenerated _ _ erased
  rw [baseData]
  rfl

/-- A non-root fragment cut is allocated freshly while retaining its exact
fragment parent, including identification of a root parent with the splice
site. -/
theorem checkedFragmentRegion_cut
    (step : RelationJoinStep source dying content)
    (region parent : content.val.diagram.RegionId)
    (nonroot : region ≠ content.val.diagram.root)
    (data : content.val.diagram.regions region = .cut parent) :
    step.checked.val.regions (step.checkedFragmentRegion region) =
      .cut (step.checkedFragmentRegion parent) := by
  unfold checkedFragmentRegion
  apply Internal.checkedRegion_data_transport_cut step.generated
  let fresh := DenseList.index step.attachment.fragmentRegions region (by
    simp [ConcreteSpliceAttachment.fragmentRegions,
      ConcreteDiagram.regionsList, Data.Finite.mem_allFin, nonroot])
  have regionExact : step.attachment.fragmentRegions.get fresh = region :=
    DenseList.get_index _ _ _
  rw [show step.attachment.fragmentRegion region =
      step.attachment.freshRegion fresh by
    simp [ConcreteSpliceAttachment.fragmentRegion, nonroot, fresh]]
  rw [ConcreteSpliceAttachment.diagram_region_freshRegion, regionExact, data]
  rfl

@[simp] theorem checkedPriorWire_val
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    (step.checkedPriorWire wire).val = wire.val := by
  rfl

theorem checkedPriorRegion_injective
    (step : RelationJoinStep source dying content) :
    Function.Injective step.checkedPriorRegion := by
  intro left right same
  apply Fin.ext
  simpa using congrArg Fin.val same

@[simp] theorem checkedRegionImage_val
    (step : RelationJoinStep source dying content)
    (region : source.val.RegionId) :
    (step.checkedRegionImage region).val = region.val := by
  rw [step.checkedRegionImageExact, step.baseRegionImageExact]
  exact step.priorRegionImageVal region

theorem checkedPriorWire_injective
    (step : RelationJoinStep source dying content) :
    Function.Injective step.checkedPriorWire := by
  intro left right same
  apply Fin.ext
  simpa using congrArg Fin.val same

theorem checkedFragmentNode_injective
    (step : RelationJoinStep source dying content) :
    Function.Injective step.checkedFragmentNode := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  simpa [checkedFragmentNode,
    ConcreteSpliceAttachment.fragmentNode] using values

theorem checkedFragmentRegion_injective_of_nonroot
    (step : RelationJoinStep source dying content)
    {left right : content.val.diagram.RegionId}
    (leftNonroot : left ≠ content.val.diagram.root)
    (rightNonroot : right ≠ content.val.diagram.root)
    (same : step.checkedFragmentRegion left =
      step.checkedFragmentRegion right) :
    left = right := by
  have values := congrArg Fin.val same
  have indices :
      DenseList.index step.attachment.fragmentRegions left (by
        simp [ConcreteSpliceAttachment.fragmentRegions,
          ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
          leftNonroot]) =
        DenseList.index step.attachment.fragmentRegions right (by
          simp [ConcreteSpliceAttachment.fragmentRegions,
            ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
            rightNonroot]) := by
    apply Fin.ext
    simpa [checkedFragmentRegion,
      ConcreteSpliceAttachment.fragmentRegion, leftNonroot, rightNonroot,
      ConcreteSpliceAttachment.freshRegion] using values
  have mapped := congrArg step.attachment.fragmentRegions.get indices
  rw [DenseList.get_index, DenseList.get_index] at mapped
  exact mapped

theorem checkedFragmentWire_injective_of_internal
    (step : RelationJoinStep source dying content)
    {left right : content.val.diagram.WireId}
    (leftInternal : left ∉ content.val.boundary)
    (rightInternal : right ∉ content.val.boundary)
    (same : step.checkedFragmentWire left =
      step.checkedFragmentWire right) :
    left = right := by
  have values := congrArg Fin.val same
  have indices :
      DenseList.index step.attachment.fragmentInternalWires left (by
        simp [ConcreteSpliceAttachment.fragmentInternalWires,
          ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
          leftInternal]) =
        DenseList.index step.attachment.fragmentInternalWires right (by
          simp [ConcreteSpliceAttachment.fragmentInternalWires,
            ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
            rightInternal]) := by
    apply Fin.ext
    simpa [checkedFragmentWire,
      ConcreteSpliceAttachment.fragmentWire, leftInternal, rightInternal,
      ConcreteSpliceAttachment.freshWire] using values
  have mapped :=
    congrArg step.attachment.fragmentInternalWires.get indices
  rw [DenseList.get_index, DenseList.get_index] at mapped
  exact mapped

theorem checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
    (step : RelationJoinStep source dying content)
    (fragment : content.val.diagram.RegionId)
    (nonroot : fragment ≠ content.val.diagram.root)
    (prior : step.prior.val.RegionId) :
    step.checkedFragmentRegion fragment ≠
      step.checkedPriorRegion prior := by
  intro same
  have underlying :
      step.attachment.fragmentRegion fragment =
        step.attachment.hostRegion
          (Internal.checkedRegion step.baseGenerated
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              step.prior step.priorApplication prior)) := by
    apply Fin.ext
    have values := congrArg Fin.val same
    simpa [checkedFragmentRegion, checkedPriorRegion] using values
  rw [ConcreteSpliceAttachment.fragmentRegion, dif_neg nonroot] at underlying
  exact step.attachment.hostRegion_ne_freshRegion _ _ underlying.symm

theorem checkedFragmentWire_ne_checkedPriorWire_of_internal
    (step : RelationJoinStep source dying content)
    (fragment : content.val.diagram.WireId)
    (internal : fragment ∉ content.val.boundary)
    (prior : step.prior.val.WireId) :
    step.checkedFragmentWire fragment ≠
      step.checkedPriorWire prior := by
  intro same
  have underlying :
      step.attachment.fragmentWire fragment =
        step.attachment.hostWire
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
              step.prior step.priorApplication prior)) := by
    apply Fin.ext
    have values := congrArg Fin.val same
    simpa [checkedFragmentWire, checkedPriorWire] using values
  rw [ConcreteSpliceAttachment.fragmentWire, dif_neg internal] at underlying
  exact step.attachment.hostWire_ne_freshWire _ _ underlying.symm

/-- A relation splice whose ordered source attachments respect repeated
boundary-source classes allocates no identity nodes. -/
theorem identityRequests_eq_nil_of_sourceAttachments_coherent
    (step : RelationJoinStep source dying content)
    (coherent :
      ∀ left right : Fin content.val.boundary.length,
        content.val.boundary.get left = content.val.boundary.get right →
          step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm left) =
            step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm right)) :
    step.attachment.identityRequests = [] := by
  apply step.attachment.identityRequests_eq_nil_of_boundary_coherent
  intro left right same
  rw [step.targetExact, step.targetExact]
  exact congrArg step.baseWireImage (coherent left right same)

theorem checked_regionCount
    (step : RelationJoinStep source dying content) :
    step.checked.val.regionCount =
      step.prior.val.regionCount + step.attachment.fragmentRegions.length := by
  rw [step.generated]
  change step.base.val.regionCount + step.attachment.fragmentRegions.length = _
  have baseCount : step.base.val.regionCount = step.prior.val.regionCount := by
    rw [step.baseGenerated]
  rw [baseCount]

theorem checked_nodeCount_add_one
    (step : RelationJoinStep source dying content) :
    step.checked.val.nodeCount + 1 =
      step.prior.val.nodeCount + content.val.diagram.nodeCount +
        step.attachment.identityRequests.length := by
  rw [step.generated]
  change
    step.base.val.nodeCount +
          (content.val.diagram.nodeCount +
            step.attachment.identityRequests.length) + 1 = _
  have baseCount : step.base.val.nodeCount + 1 =
      step.prior.val.nodeCount := by
    rw [step.baseGenerated]
    exact Data.Finite.filter_not_mem_length_add_removed_length
      [step.priorApplication] (by simp)
  omega

theorem checked_wireCount
    (step : RelationJoinStep source dying content) :
    step.checked.val.wireCount =
      step.prior.val.wireCount +
        step.attachment.fragmentInternalWires.length := by
  rw [step.generated]
  change step.base.val.wireCount +
    step.attachment.fragmentInternalWires.length = _
  have baseCount : step.base.val.wireCount = step.prior.val.wireCount := by
    rw [step.baseGenerated]
    simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate,
      Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  rw [baseCount]

theorem checkedPriorNode_injective
    (step : RelationJoinStep source dying content)
    {left right : step.prior.val.NodeId}
    (leftDifferent : left ≠ step.priorApplication)
    (rightDifferent : right ≠ step.priorApplication)
    (same :
      step.checkedPriorNode left leftDifferent =
        step.checkedPriorNode right rightDifferent) :
    left = right := by
  have leftRetained :
      left ∈ ConcreteDiagram.IdentityNormalizationCore.retainedNodes
        step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, leftDifferent]
  have rightRetained :
      right ∈ ConcreteDiagram.IdentityNormalizationCore.retainedNodes
        step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, rightDifferent]
  have indexed :
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
          step.prior step.priorApplication left leftRetained =
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
          step.prior step.priorApplication right rightRetained := by
    apply Fin.ext
    simpa [checkedPriorNode, Internal.checkedNode,
      ConcreteSpliceAttachment.hostNode] using congrArg Fin.val same
  change
    DenseList.index
        (ConcreteDiagram.IdentityNormalizationCore.retainedNodes
          step.prior.val [step.priorApplication]) left leftRetained =
      DenseList.index
        (ConcreteDiagram.IdentityNormalizationCore.retainedNodes
          step.prior.val [step.priorApplication]) right rightRetained at indexed
  have values :=
    congrArg
      (ConcreteDiagram.IdentityNormalizationCore.retainedNodes
        step.prior.val [step.priorApplication]).get indexed
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

theorem checkedFragmentNode_ne_checkedPriorNode
    (step : RelationJoinStep source dying content)
    (fragment : content.val.diagram.NodeId)
    (prior : step.prior.val.NodeId)
    (different : prior ≠ step.priorApplication) :
    step.checkedFragmentNode fragment ≠
      step.checkedPriorNode prior different := by
  intro same
  have values := congrArg Fin.val same
  have baseCount :
      step.base.val.nodeCount =
        (ConcreteDiagram.IdentityNormalizationCore.retainedNodes
          step.prior.val [step.priorApplication]).length := by
    rw [step.baseGenerated]
  have priorBound :=
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
      step.prior step.priorApplication prior (by
        simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
          ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
          different])).isLt
  simp [checkedFragmentNode, checkedPriorNode, Internal.checkedNode,
    ConcreteSpliceAttachment.fragmentNode,
    ConcreteSpliceAttachment.hostNode] at values
  omega

/-- Transport every still-generated application except the atom consumed by
this step into the checked splice target. -/
def checkedRemainingNodes
    (step : RelationJoinStep source dying content)
    (nodes : List step.prior.val.NodeId) :
    List step.checked.val.NodeId :=
  nodes.filterMap fun node =>
    if different : node ≠ step.priorApplication then
      some (step.checkedPriorNode node different)
    else
      none

/-- The indexed post-step node image is exactly the prior image with the
consumed application removed and every survivor transported through the
checked splice.  This is the authoritative snoc-tail equation used by inverse
reconstruction. -/
theorem checkedNodeImages_eq_checkedRemainingNodes
    (step : RelationJoinStep source dying content)
    (nodes : List source.val.NodeId) :
    nodes.filterMap step.checkedNodeImage =
      step.checkedRemainingNodes
        (nodes.filterMap step.priorNodeImage) := by
  induction nodes with
  | nil => rfl
  | cons sourceNode nodes induction =>
      rw [List.filterMap_cons, List.filterMap_cons,
        step.checkedNodeImageExact, step.baseNodeImageExact]
      cases priorExact : step.priorNodeImage sourceNode with
      | none =>
          simp only [Option.map_none]
          exact induction
      | some priorNode =>
          by_cases different : priorNode ≠ step.priorApplication
          · have retained :
                priorNode ∈
                  ConcreteDiagram.IdentityNormalizationCore.retainedNodes
                    step.prior.val [step.priorApplication] := by
              simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
                ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
                different]
            simp only [retained, dif_pos, Option.map_some]
            change
              step.checkedPriorNode priorNode different ::
                    nodes.filterMap step.checkedNodeImage =
                step.checkedRemainingNodes
                  (priorNode :: nodes.filterMap step.priorNodeImage)
            simpa [checkedRemainingNodes, different] using
              congrArg (fun tail =>
                step.checkedPriorNode priorNode different :: tail) induction
          · have same : priorNode = step.priorApplication :=
              Classical.byContradiction different
            subst priorNode
            have notRetained :
                step.priorApplication ∉
                  ConcreteDiagram.IdentityNormalizationCore.retainedNodes
                    step.prior.val [step.priorApplication] := by
              simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
                ConcreteDiagram.nodesList, Data.Finite.mem_allFin]
            simp only [notRetained, dif_neg, Option.map_none]
            change
              nodes.filterMap step.checkedNodeImage =
                step.checkedRemainingNodes
                  (step.priorApplication ::
                    nodes.filterMap step.priorNodeImage)
            simpa [checkedRemainingNodes] using induction

/-- The consumed source application has no post-step representative. -/
@[simp] theorem checkedNodeImage_application
    (step : RelationJoinStep source dying content) :
    step.checkedNodeImage step.application = none := by
  rw [step.checkedNodeImageExact, step.baseNodeImageExact,
    step.priorApplicationImage]
  have notRetained :
      step.priorApplication ∉
        ConcreteDiagram.IdentityNormalizationCore.retainedNodes
          step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin]
  simp [notRetained]

/-- Every non-consumed prior source-node image lands at the exact checked
prior-node transport used by the carrier reconstruction fold. -/
theorem checkedNodeImage_of_prior
    (step : RelationJoinStep source dying content)
    {sourceNode : source.val.NodeId}
    {priorNode : step.prior.val.NodeId}
    (priorExact : step.priorNodeImage sourceNode = some priorNode)
    (different : priorNode ≠ step.priorApplication) :
    step.checkedNodeImage sourceNode =
      some (step.checkedPriorNode priorNode different) := by
  rw [step.checkedNodeImageExact, step.baseNodeImageExact, priorExact]
  have retained :
      priorNode ∈
        ConcreteDiagram.IdentityNormalizationCore.retainedNodes
          step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, different]
  simp only [retained, dif_pos, Option.map_some]
  rfl

/-- The post-step partial source-node landing has unique preimages. -/
theorem checkedNodeImage_injective
    (step : RelationJoinStep source dying content)
    {left right : source.val.NodeId}
    {checkedNode : step.checked.val.NodeId}
    (leftExact : step.checkedNodeImage left = some checkedNode)
    (rightExact : step.checkedNodeImage right = some checkedNode) :
    left = right := by
  classical
  cases leftPriorExact : step.priorNodeImage left with
  | none =>
      rw [step.checkedNodeImageExact, step.baseNodeImageExact,
        leftPriorExact] at leftExact
      contradiction
  | some leftPrior =>
      cases rightPriorExact : step.priorNodeImage right with
      | none =>
          rw [step.checkedNodeImageExact, step.baseNodeImageExact,
            rightPriorExact] at rightExact
          contradiction
      | some rightPrior =>
          have leftDifferent : leftPrior ≠ step.priorApplication := by
            intro same
            subst leftPrior
            have sourceExact : left = step.application :=
              step.priorNodeImage_injective leftPriorExact
                step.priorApplicationImage
            subst left
            rw [step.checkedNodeImage_application] at leftExact
            contradiction
          have rightDifferent : rightPrior ≠ step.priorApplication := by
            intro same
            subst rightPrior
            have sourceExact : right = step.application :=
              step.priorNodeImage_injective rightPriorExact
                step.priorApplicationImage
            subst right
            rw [step.checkedNodeImage_application] at rightExact
            contradiction
          rw [step.checkedNodeImage_of_prior leftPriorExact leftDifferent]
            at leftExact
          rw [step.checkedNodeImage_of_prior rightPriorExact rightDifferent]
            at rightExact
          have transportedExact :
              step.checkedPriorNode leftPrior leftDifferent =
                step.checkedPriorNode rightPrior rightDifferent :=
            Option.some.inj (leftExact.trans rightExact.symm)
          have priorExact : leftPrior = rightPrior :=
            step.checkedPriorNode_injective leftDifferent rightDifferent
              transportedExact
          subst rightPrior
          exact step.priorNodeImage_injective leftPriorExact rightPriorExact

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

/-- Exact node-domain characterization of the construction trace: a source
node lacks a final representative precisely when it is one of the consumed
relation applications, in the trace's ordered step list. -/
theorem RelationJoinSemanticTrace.nodeImage_eq_none_iff
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope)
    (sourceNode : source.val.NodeId) :
    finalNodeImage sourceNode = none ↔
      sourceNode ∈ steps.map RelationJoinStep.application := by
  induction trace with
  | nil => simp
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      have nodeImageExact := eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      rw [List.map_append]
      simp only [List.map_singleton, List.mem_append, List.mem_singleton]
      cases priorExact : step.priorNodeImage sourceNode with
      | none =>
          have checkedExact : step.checkedNodeImage sourceNode = none := by
            simp [step.checkedNodeImageExact, step.baseNodeImageExact,
              priorExact]
          rw [checkedExact]
          simp only [true_iff]
          exact Or.inl (induction.mp (nodeImageExact ▸ priorExact))
      | some priorNode =>
          by_cases applicationExact : sourceNode = step.application
          · subst sourceNode
            simp [step.checkedNodeImage_application]
          · have priorDifferent :
                priorNode ≠ step.priorApplication := by
              intro same
              subst priorNode
              exact applicationExact
                (step.priorNodeImage_injective priorExact
                  step.priorApplicationImage)
            have checkedExact :=
              step.checkedNodeImage_of_prior priorExact priorDifferent
            rw [checkedExact]
            simp only [Option.some_ne_none, false_iff]
            intro present
            rcases present with member | same
            · have noneCurrent := induction.mpr member
              rw [← nodeImageExact, priorExact] at noneCurrent
              contradiction
            · exact applicationExact same

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
  regionImage : source.val.RegionId → checked.val.RegionId
  regionImage_val : ∀ region, (regionImage region).val = region.val
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
  nodeImage_injective :
    ∀ {left right checkedNode},
      nodeImage left = some checkedNode →
      nodeImage right = some checkedNode →
      left = right
  processed : List source.val.NodeId
  steps : List (RelationJoinStep source dying content)
  traceExact :
    steps.map RelationJoinStep.application = processed
  semanticTrace :
    RelationJoinSemanticTrace source dying content parameters args steps
      checked regionImage nodeImage wireImage (wireImage dying)
        (regionImage (source.val.wires dying).scope)

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
      regionImage := id
      regionImage_val := fun _ => rfl
      regionImage_encloses := fun _ _ => Iff.rfl
      wireImage := id
      wireImage_injective := Function.injective_id
      wireScopeExact := fun _ => rfl
      nodeImage := fun node => some node
      nodeImage_injective := by
        intro left right checkedNode leftExact rightExact
        exact Option.some.inj (leftExact.trans rightExact.symm)
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
                                                    ConcreteDiagram.IdentityNormalizationCore.retainedNodes
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
                                          rw [ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_encloses_iff]
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
                                    let nextState :
                                        RelationJoinState source wire content
                                          parameters args :=
                                      { checked := next
                                        regionImage :=
                                          step.checkedRegionImage
                                        regionImage_val :=
                                          step.checkedRegionImage_val
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
                                        nodeImage := step.checkedNodeImage
                                        nodeImage_injective :=
                                          step.checkedNodeImage_injective
                                        processed :=
                                          state.processed ++
                                            [application.node]
                                        steps := state.steps ++ [step]
                                        traceExact := by
                                          simp [step, state.traceExact]
                                        semanticTrace :=
                                          .snoc state.semanticTrace step
                                            rfl (by simp [step]) (by simp [step])
                                            (by simp [step])
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
  allRegionImage_injective : Function.Injective allRegionImage
  allNodeImage : state.checked.val.NodeId → checked.val.NodeId
  allNodeImage_injective : Function.Injective allNodeImage
  allWireImage :
    ∀ boundWire : state.checked.val.WireId,
      boundWire ≠ state.wireImage wire → checked.val.WireId
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

theorem boundNodeImage_eq_none_iff
    (result : RelationJoinResult source wire content parameters)
    (sourceNode : source.val.NodeId) :
    result.boundNodeImage sourceNode = none ↔
      sourceNode ∈ result.applications := by
  change result.finalState.nodeImage sourceNode = none ↔ _
  rw [result.finalState.semanticTrace.nodeImage_eq_none_iff]
  rw [result.finalState.traceExact, result.applicationsExact]

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

theorem plainBoundRegionImage_injective
    (result : RelationJoinResult source wire content parameters) :
    Function.Injective result.plainBoundRegionImage :=
  result.finalRemoval.allRegionImage_injective

/-- Exact final-deletion landing for every node present after all splices. -/
def plainBoundNodeImage
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.NodeId → result.plainFinal.val.NodeId :=
  result.finalRemoval.allNodeImage

theorem plainBoundNodeImage_injective
    (result : RelationJoinResult source wire content parameters) :
    Function.Injective result.plainBoundNodeImage :=
  result.finalRemoval.allNodeImage_injective

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

theorem plainFinal_regionCount
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.regionCount = result.boundFinal.val.regionCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  exact Data.Finite.filter_not_mem_length_add_removed_length [] (by simp)

theorem plainFinal_nodeCount
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.nodeCount = result.boundFinal.val.nodeCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  exact Data.Finite.filter_not_mem_length_add_removed_length [] (by simp)

theorem plainFinal_wireCount_add_one
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.wireCount + 1 =
      result.boundFinal.val.wireCount := by
  unfold plainFinal boundFinal
  rw [result.finalRemoval.generated]
  exact Data.Finite.filter_not_mem_length_add_removed_length
    [result.finalState.wireImage wire] (by simp)

@[simp] theorem bound_dying_scope
    (result : RelationJoinResult source wire content parameters) :
    (result.boundFinal.val.wires result.boundDying).scope =
      result.boundRegionImage (source.val.wires wire).scope :=
  result.finalState.wireScopeExact wire

theorem semantic_trace
    (result : RelationJoinResult source wire content parameters) :
    RelationJoinSemanticTrace source wire content parameters result.args
      result.steps result.boundFinal result.boundRegionImage
        result.boundNodeImage result.boundWireImage result.boundDying
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
              result.boundNodeImage result.boundWireImage
              result.boundDying
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
