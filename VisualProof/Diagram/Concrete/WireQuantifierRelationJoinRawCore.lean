import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.DenseErasure
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw

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

structure RelationJoinApplication
    (source : CheckedDiagram definitions)
    (args : List Sig) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId
  nodeExact : source.val.nodes node = .atom region args
  argumentsAccepted :
    relationArgumentWires? source node args 0 = some arguments

def relationEndpointIsApplied
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (endpoint : CEndpoint source.val.nodeCount) : Bool :=
  match endpoint.port, source.val.nodes endpoint.node with
  | .head, .atom _ nodeArgs => decide (nodeArgs = args)
  | _, _ => false

def relationApplicationNodes
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

def relationJoinApplications?
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

theorem relationJoinApplications?_nodes
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

def openBoundarySigs
    (content : CheckedOpenDiagram definitions) :
    List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

def parameterSigs
    (source : CheckedDiagram definitions)
    (parameters : List source.val.WireId) :
    List Sig :=
  parameters.map fun wire => (source.val.wires wire).sig

structure RelationJoinPlan
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

def checkRelationJoinPlan
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
  mk ::
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
  removal :
    Internal.BatchRemovalPlan prior [] [priorApplication] []
  base : CheckedDiagram definitions
  baseGenerated :
    base.val =
      ConcreteDiagram.DenseErasure.eraseNodeCandidate
        prior priorApplication
  baseRegionImage : source.val.RegionId → base.val.RegionId
  baseRegionImageExact :
    ∀ region,
      baseRegionImage region =
        Internal.checkedRegion baseGenerated
          (ConcreteDiagram.DenseErasure.eraseNodeRegion
            prior priorApplication (priorRegionImage region))
  baseWireImage : source.val.WireId → base.val.WireId
  baseWireImageExact :
    ∀ sourceWire,
      baseWireImage sourceWire =
        Internal.checkedWire baseGenerated
          (ConcreteDiagram.DenseErasure.eraseNodeWire
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
                  ConcreteDiagram.DenseErasure.retainedNodes
                    prior.val [priorApplication] then
              some
                (Internal.checkedNode baseGenerated
                  (ConcreteDiagram.DenseErasure.eraseNodeIndex
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
  attachmentAccepted :
    checkConcreteSpliceAttachment base site content attachment.target =
      some attachment
  generated : checked.val = attachment.diagram
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

/-- Removing one known member from a duplicate-free list decreases its
length by exactly one, without invoking a finite-enumeration inverse. -/
private theorem relationJoin_filter_ne_length_add_one_of_nodup_mem
    [DecidableEq α]
    {values : List α} (nodup : values.Nodup) (removed : α)
    (member : removed ∈ values) :
    (values.filter fun value => decide (value ≠ removed)).length + 1 =
      values.length := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      by_cases same : head = removed
      · subst head
        have retained :
            tail.filter (fun value => decide (value ≠ removed)) = tail :=
          List.filter_eq_self.mpr fun value valueMember => by
            apply decide_eq_true
            intro equality
            subst value
            exact headFresh valueMember
        rw [List.filter_cons_of_neg (by simp), retained]
        simp
      · have tailMember : removed ∈ tail := by
          rcases List.mem_cons.mp member with equality | tailMember
          · exact False.elim (same equality.symm)
          · exact tailMember
        rw [List.filter_cons_of_pos (by simp [same])]
        simp only [List.length_cons]
        have tailExact := induction tailNodup tailMember
        omega

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
        (ConcreteDiagram.DenseErasure.eraseNodeRegion
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
        (ConcreteDiagram.DenseErasure.eraseNodeIndex
          step.prior step.priorApplication node (by
            simp [ConcreteDiagram.DenseErasure.retainedNodes,
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
      (ConcreteDiagram.DenseErasure.eraseNodeWire
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

/-- Allocate one attachment-generated request identity node in the checked
splice target. -/
def checkedIdentityNode
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    step.checked.val.NodeId :=
  Internal.checkedNode step.generated
    (step.attachment.identityNode request)

/-- Allocate one fragment wire in the checked splice target. -/
def checkedFragmentWire
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId) :
    step.checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount step.generated).symm
    (step.attachment.fragmentWire wire)

theorem checkedRegionImage_eq_checkedPriorRegion
    (step : RelationJoinStep source dying content)
    (region : source.val.RegionId) :
    step.checkedRegionImage region =
      step.checkedPriorRegion (step.priorRegionImage region) := by
  rw [step.checkedRegionImageExact, step.baseRegionImageExact]
  rfl

theorem checkedWireImage_eq_checkedPriorWire
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    step.checkedWireImage wire =
      step.checkedPriorWire (step.priorWireImage wire) := by
  rw [step.checkedWireImageExact, step.baseWireImageExact]
  rfl

/-- One checked splice preserves the prior root's dense position. -/
@[simp] theorem checked_root_val
    (step : RelationJoinStep source dying content) :
    step.checked.val.root.val = step.prior.val.root.val := by
  rw [Internal.checkedRoot_transport step.generated]
  unfold Internal.checkedRegion
  change step.attachment.diagram.root.val = step.prior.val.root.val
  change (step.attachment.hostRegion step.base.val.root).val =
    step.prior.val.root.val
  simp only [ConcreteSpliceAttachment.hostRegion]
  rw [Internal.checkedRoot_transport step.baseGenerated]
  unfold Internal.checkedRegion
  change
    (ConcreteDiagram.DenseErasure.eraseNodeCandidate
      step.prior step.priorApplication).root.val = step.prior.val.root.val
  rfl

/-- Transport one endpoint whose prior node is not the consumed application. -/
def checkedPriorEndpoint
    (step : RelationJoinStep source dying content)
    (endpoint : CEndpoint step.prior.val.nodeCount)
    (different : endpoint.node ≠ step.priorApplication) :
    CEndpoint step.checked.val.nodeCount :=
  ⟨step.checkedPriorNode endpoint.node different, endpoint.port⟩

/-- Transport one copied fragment endpoint into the checked splice target. -/
def checkedFragmentEndpoint
    (step : RelationJoinStep source dying content)
    (endpoint : CEndpoint content.val.diagram.nodeCount) :
    CEndpoint step.checked.val.nodeCount :=
  ⟨step.checkedFragmentNode endpoint.node, endpoint.port⟩

/-- Every checked splice wire has exactly the attachment-owned ordered
endpoint table, transported only across the checked carrier cast. -/
theorem checkedAttachmentWire_endpoints
    (step : RelationJoinStep source dying content)
    (wire : step.attachment.diagram.WireId) :
    (step.checked.val.wires
      (Internal.checkedWire step.generated wire)).endpoints =
        (step.attachment.diagram.wires wire).endpoints.map
          (Internal.checkedEndpoint step.generated) := by
  exact Internal.checkedWire_endpoints_transport step.generated wire

/-- A surviving prior incidence remains incident to the transported prior
wire after deletion and splice. -/
theorem checkedPriorEndpoint_mem
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId)
    (endpoint : CEndpoint step.prior.val.nodeCount)
    (different : endpoint.node ≠ step.priorApplication)
    (incident : endpoint ∈ (step.prior.val.wires wire).endpoints) :
    step.checkedPriorEndpoint endpoint different ∈
      (step.checked.val.wires (step.checkedPriorWire wire)).endpoints := by
  have erased :=
    ConcreteDiagram.DenseErasure.eraseNodeEndpoint_mem
      step.prior step.priorApplication wire endpoint different incident
  have baseIncident :
      Internal.checkedEndpoint step.baseGenerated
          (ConcreteDiagram.DenseErasure.eraseNodeEndpoint
            step.prior step.priorApplication endpoint different) ∈
        (step.base.val.wires
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeWire
              step.prior step.priorApplication wire))).endpoints := by
    rw [Internal.checkedWire_endpoints_transport]
    exact List.mem_map.mpr ⟨_, erased, rfl⟩
  have attached := step.attachment.hostEndpoint_mem_diagram _ _ baseIncident
  have checkedIncident :
      Internal.checkedEndpoint step.generated
          (step.attachment.hostEndpoint
            (Internal.checkedEndpoint step.baseGenerated
              (ConcreteDiagram.DenseErasure.eraseNodeEndpoint
                step.prior step.priorApplication endpoint different))) ∈
        (step.checked.val.wires
          (Internal.checkedWire step.generated
            (step.attachment.hostWire
              (Internal.checkedWire step.baseGenerated
                (ConcreteDiagram.DenseErasure.eraseNodeWire
                  step.prior step.priorApplication wire))))).endpoints := by
    rw [Internal.checkedWire_endpoints_transport]
    exact List.mem_map.mpr ⟨_, attached, rfl⟩
  simpa [checkedPriorEndpoint, checkedPriorNode, checkedPriorWire,
    ConcreteDiagram.DenseErasure.eraseNodeEndpoint] using
    checkedIncident

/-- Every copied fragment incidence remains incident to the transported
fragment wire in the checked splice target. -/
theorem checkedFragmentEndpoint_mem
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId)
    (endpoint : CEndpoint content.val.diagram.nodeCount)
    (incident : endpoint ∈ (content.val.diagram.wires wire).endpoints) :
    step.checkedFragmentEndpoint endpoint ∈
      (step.checked.val.wires (step.checkedFragmentWire wire)).endpoints := by
  have attached :=
    step.attachment.fragmentEndpoint_mem_diagram wire endpoint incident
  have checkedIncident :
      Internal.checkedEndpoint step.generated
          (step.attachment.fragmentEndpoint endpoint) ∈
        (step.checked.val.wires
          (Internal.checkedWire step.generated
            (step.attachment.fragmentWire wire))).endpoints := by
    rw [Internal.checkedWire_endpoints_transport]
    exact List.mem_map.mpr ⟨_, attached, rfl⟩
  simpa [checkedFragmentEndpoint, checkedFragmentNode,
    checkedFragmentWire] using checkedIncident

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
    ConcreteDiagram.DenseErasure.eraseNodeRegion_sheet
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
    ConcreteDiagram.DenseErasure.eraseNodeRegion_cut
      step.prior step.priorApplication region parent data
  have baseData := Internal.checkedRegion_data_transport_cut
    step.baseGenerated _ _ erased
  rw [baseData]
  rfl

/-- A surviving prior node keeps its constructor and intrinsic payload; its
sole region carrier follows `checkedPriorRegion`. -/
theorem checkedPriorNode_data
    (step : RelationJoinStep source dying content)
    (node : step.prior.val.NodeId)
    (different : node ≠ step.priorApplication) :
    step.checked.val.nodes (step.checkedPriorNode node different) =
      (step.prior.val.nodes node).relocate
        (step.checkedPriorRegion (step.prior.val.nodes node).region) := by
  unfold checkedPriorNode checkedPriorRegion
  change step.checked.val.nodes
      (Internal.checkedNode step.generated _) = _
  rw [Internal.checkedNode_data_transport]
  rw [ConcreteSpliceAttachment.diagram_node_hostNode]
  have retained :
      node ∈ ConcreteDiagram.DenseErasure.retainedNodes
        step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, different]
  have erased :=
    ConcreteDiagram.DenseErasure.eraseNodeIndex_data
      step.prior step.priorApplication node retained
  have baseData := Internal.checkedNode_data_transport step.baseGenerated
    (ConcreteDiagram.DenseErasure.eraseNodeIndex
      step.prior step.priorApplication node retained)
  unfold ConcreteSpliceAttachment.renameHostNode
  rw [baseData, erased]
  cases data : step.prior.val.nodes node <;>
    simp [ConcreteSpliceAttachment.renameHostNode, CNode.relocate,
      CNode.region, Internal.checkedNodeData, Internal.checkedRegion]

/-- A fragment node keeps its exact constructor and payload under splice;
its region carrier is the fragment region image. -/
theorem checkedFragmentNode_data
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    step.checked.val.nodes (step.checkedFragmentNode node) =
      (content.val.diagram.nodes node).relocate
        (step.checkedFragmentRegion
          (content.val.diagram.nodes node).region) := by
  unfold checkedFragmentNode checkedFragmentRegion
  change step.checked.val.nodes
      (Internal.checkedNode step.generated _) = _
  rw [Internal.checkedNode_data_transport]
  rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
  unfold ConcreteSpliceAttachment.renameFragmentNode
  cases data : content.val.diagram.nodes node <;>
    simp [ConcreteSpliceAttachment.renameFragmentNode, CNode.relocate,
      CNode.region, Internal.checkedNodeData, Internal.checkedRegion]

/-- A generated request node has exactly the attachment request's identity
payload at the checked splice site. -/
theorem checkedIdentityNode_data
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    step.checked.val.nodes (step.checkedIdentityNode request) =
      .identity
        (Internal.checkedRegion step.generated
          (step.attachment.hostRegion step.site))
        (step.attachment.identityRequests.get request).sig
        (step.attachment.identityRequests.get request).attachments.length := by
  unfold checkedIdentityNode
  rw [Internal.checkedNode_data_transport,
    step.attachment.diagram_node_identityNode]
  rfl

/-- Every generated request attachment is one of the splice's checked
positional targets.  This is the construction-owned range fact used to
recover the corresponding source-wire origin without inspecting a result
diagram. -/
theorem identityRequestAttachment_mem_targets
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    (step.attachment.identityRequests.get request).attachments.get port ∈
      (Data.Finite.allFin content.val.boundary.length).map
        step.attachment.target := by
  have requestMember :=
    List.get_mem step.attachment.identityRequests request
  unfold ConcreteSpliceAttachment.identityRequests
    computedIdentityRequests at requestMember
  rw [List.mem_eraseDups, List.mem_filterMap] at requestMember
  rcases requestMember with ⟨sourceWire, _sourceMember, emitted⟩
  change
    (if 2 ≤ (concreteAttachmentTargets step.base content
        step.attachment.target sourceWire).length then
      some
        ({ source := sourceWire
           attachments := concreteAttachmentTargets step.base content
             step.attachment.target sourceWire } :
          ConcreteIdentityRequest step.base.val content.val.diagram)
    else none) = some _ at emitted
  split at emitted
  · rename_i generated
    have requestExact := Option.some.inj emitted
    change
      ({ source := sourceWire
         attachments := concreteAttachmentTargets step.base content
           step.attachment.target sourceWire } :
        ConcreteIdentityRequest step.base.val content.val.diagram) =
          step.attachment.identityRequests.get request at requestExact
    have attachmentsExact :=
      congrArg ConcreteIdentityRequest.attachments requestExact
    change concreteAttachmentTargets step.base content
        step.attachment.target sourceWire =
      (step.attachment.identityRequests.get request).attachments at attachmentsExact
    have attachmentMember :
        (step.attachment.identityRequests.get request).attachments.get port ∈
          concreteAttachmentTargets step.base content
            step.attachment.target sourceWire := by
      simpa only [attachmentsExact] using
        List.get_mem
          (step.attachment.identityRequests.get request).attachments port
    unfold concreteAttachmentTargets at attachmentMember
    rw [List.mem_eraseDups, List.mem_filterMap] at attachmentMember
    rcases attachmentMember with ⟨position, positionMember, targetEmitted⟩
    split at targetEmitted
    · have targetExact := Option.some.inj targetEmitted
      exact List.mem_map.mpr
        ⟨position, positionMember, targetExact⟩
    · contradiction
  · contradiction

/-- Every generated request attachment is the checked base image of one of
the source attachment wires. -/
theorem identityRequestAttachment_mem_baseWireImages
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    (step.attachment.identityRequests.get request).attachments.get port ∈
      step.sourceAttachments.map step.baseWireImage := by
  rcases List.mem_map.mp
      (step.identityRequestAttachment_mem_targets request port) with
    ⟨position, _positionMember, targetExact⟩
  let sourcePosition : Fin step.sourceAttachments.length :=
    Fin.cast step.sourceAttachmentArity.symm position
  refine List.mem_map.mpr
    ⟨step.sourceAttachments.get sourcePosition,
      List.get_mem _ sourcePosition, ?_⟩
  exact (step.targetExact position).symm.trans targetExact

/-- Deterministic first source-attachment position represented by one
generated request port. -/
def identityRequestSourcePosition
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    Fin step.sourceAttachments.length :=
  Fin.cast (by simp)
    (DenseList.index (step.sourceAttachments.map step.baseWireImage)
      ((step.attachment.identityRequests.get request).attachments.get port)
      (step.identityRequestAttachment_mem_baseWireImages request port))

/-- Source wire represented by one generated request port. -/
def identityRequestSourceWire
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    source.val.WireId :=
  step.sourceAttachments.get
    (step.identityRequestSourcePosition request port)

theorem identityRequestSourceWire_survives
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    step.identityRequestSourceWire request port ≠ dying :=
  step.sourceAttachmentsSurvive
    (step.identityRequestSourcePosition request port)

theorem identityRequestSourceWire_baseImage
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    step.baseWireImage (step.identityRequestSourceWire request port) =
      (step.attachment.identityRequests.get request).attachments.get port := by
  unfold identityRequestSourceWire identityRequestSourcePosition
  have indexed := DenseList.get_index
    (step.sourceAttachments.map step.baseWireImage)
    ((step.attachment.identityRequests.get request).attachments.get port)
    (step.identityRequestAttachment_mem_baseWireImages request port)
  simpa only [List.get_eq_getElem, List.getElem_map] using indexed

/-- A copied boundary wire lands on the checked image of the source
attachment selected by the boundary class's canonical representative. -/
theorem checkedFragmentWire_eq_checkedWireImage_of_boundary
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId)
    (boundary : wire ∈ content.val.boundary) :
    step.checkedFragmentWire wire =
      step.checkedWireImage
        (step.sourceAttachments.get
          (Fin.cast step.sourceAttachmentArity.symm
            (step.attachment.representativePosition wire boundary))) := by
  rw [step.checkedWireImageExact]
  unfold checkedFragmentWire ConcreteSpliceAttachment.fragmentWire
    ConcreteSpliceAttachment.representativeTarget
  simp only [boundary, dite_true]
  rw [step.targetExact]

/-- Every generated request incidence lands on the checked image of its
construction-derived source wire representative. -/
theorem checkedIdentityAttachmentWire_eq_checkedWireImage
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length)
    (port : Fin
      (step.attachment.identityRequests.get request).attachments.length) :
    Internal.checkedWire step.generated
        (step.attachment.hostWire
          ((step.attachment.identityRequests.get request).attachments.get port)) =
      step.checkedWireImage
        (step.identityRequestSourceWire request port) := by
  rw [step.checkedWireImageExact,
    step.identityRequestSourceWire_baseImage]
  apply Fin.ext
  rfl

/-- A prior wire preserves its signature through application deletion and
splice. -/
theorem checkedPriorWire_signature
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    (step.checked.val.wires (step.checkedPriorWire wire)).sig =
      (step.prior.val.wires wire).sig := by
  unfold checkedPriorWire
  change (step.checked.val.wires
    (Internal.checkedWire step.generated _)).sig = _
  rw [Internal.checkedWire_signature_transport,
    ConcreteSpliceAttachment.diagram_wire_hostWire,
    Internal.checkedWire_signature_transport,
    ConcreteDiagram.DenseErasure.eraseNodeWire_signature]

/-- A prior wire's scope follows the exact prior region transport. -/
theorem checkedPriorWire_scope
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    (step.checked.val.wires (step.checkedPriorWire wire)).scope =
      step.checkedPriorRegion (step.prior.val.wires wire).scope := by
  unfold checkedPriorWire checkedPriorRegion
  change (step.checked.val.wires
    (Internal.checkedWire step.generated _)).scope = _
  rw [Internal.checkedWire_scope_transport,
    ConcreteSpliceAttachment.diagram_wire_hostWire_scope,
    Internal.checkedWire_scope_transport,
    ConcreteDiagram.DenseErasure.eraseNodeWire_scope]
  rfl

/-- A freshly allocated internal fragment wire preserves its signature. -/
theorem checkedFragmentWire_signature_of_internal
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId)
    (internal : wire ∉ content.val.boundary) :
    (step.checked.val.wires (step.checkedFragmentWire wire)).sig =
      (content.val.diagram.wires wire).sig := by
  unfold checkedFragmentWire
  change (step.checked.val.wires
    (Internal.checkedWire step.generated _)).sig = _
  rw [Internal.checkedWire_signature_transport]
  exact step.attachment.diagram_wire_fragmentWire_signature_of_internal
    wire internal

/-- A freshly allocated internal fragment wire's scope follows the fragment
region transport. -/
theorem checkedFragmentWire_scope_of_internal
    (step : RelationJoinStep source dying content)
    (wire : content.val.diagram.WireId)
    (internal : wire ∉ content.val.boundary) :
    (step.checked.val.wires (step.checkedFragmentWire wire)).scope =
      step.checkedFragmentRegion (content.val.diagram.wires wire).scope := by
  unfold checkedFragmentWire checkedFragmentRegion
  change (step.checked.val.wires
    (Internal.checkedWire step.generated _)).scope = _
  rw [Internal.checkedWire_scope_transport]
  rw [step.attachment.diagram_wire_fragmentWire_scope_of_internal
    wire internal]
  rfl

/-- A non-root fragment sheet is allocated freshly without changing its row. -/
theorem checkedFragmentRegion_sheet
    (step : RelationJoinStep source dying content)
    (region : content.val.diagram.RegionId)
    (nonroot : region ≠ content.val.diagram.root)
    (data : content.val.diagram.regions region = .sheet) :
    step.checked.val.regions (step.checkedFragmentRegion region) = .sheet := by
  unfold checkedFragmentRegion
  apply Internal.checkedRegion_data_transport_sheet step.generated
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
            (ConcreteDiagram.DenseErasure.eraseNodeRegion
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
            (ConcreteDiagram.DenseErasure.eraseNodeWire
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

/-- Deleting one application node leaves the prior region carrier size
unchanged before the fragment's fresh regions are appended. -/
theorem base_regionCount
    (step : RelationJoinStep source dying content) :
    step.base.val.regionCount = step.prior.val.regionCount := by
  rw [step.baseGenerated]

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
    have countExact :=
      relationJoin_filter_ne_length_add_one_of_nodup_mem
        (by simpa [ConcreteDiagram.nodesList] using
          Data.Finite.allFin_nodup step.prior.val.nodeCount)
        step.priorApplication
        (by simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin])
    have fullLength :
        (Data.Finite.allFin step.prior.val.nodeCount).length =
          step.prior.val.nodeCount := by
      simp [Data.Finite.allFin_eq_finRange]
    rw [fullLength] at countExact
    simpa [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
      ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList] using countExact
  omega

/-- Deleting the consumed application leaves exactly the ordered retained
prior-node carrier before splice allocation appends fresh node blocks. -/
theorem base_nodeCount_add_one
    (step : RelationJoinStep source dying content) :
    step.base.val.nodeCount + 1 = step.prior.val.nodeCount := by
  rw [step.baseGenerated]
  have countExact :=
    relationJoin_filter_ne_length_add_one_of_nodup_mem
      (by simpa [ConcreteDiagram.nodesList] using
        Data.Finite.allFin_nodup step.prior.val.nodeCount)
      step.priorApplication
      (by simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin])
  have fullLength :
      (Data.Finite.allFin step.prior.val.nodeCount).length =
        step.prior.val.nodeCount := by
    simp [Data.Finite.allFin_eq_finRange]
  rw [fullLength] at countExact
  simpa [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
    ConcreteDiagram.DenseErasure.retainedNodes,
    ConcreteDiagram.nodesList] using countExact

@[simp] theorem checkedPriorNode_val
    (step : RelationJoinStep source dying content)
    (node : step.prior.val.NodeId)
    (different : node ≠ step.priorApplication) :
    (step.checkedPriorNode node different).val =
      (ConcreteDiagram.DenseErasure.eraseNodeIndex step.prior
        step.priorApplication node (by
          simp [ConcreteDiagram.DenseErasure.retainedNodes,
            ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
            different])).val := by
  simp [checkedPriorNode, ConcreteSpliceAttachment.hostNode,
    Internal.checkedNode]

@[simp] theorem checkedFragmentNode_val
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    (step.checkedFragmentNode node).val = step.base.val.nodeCount + node.val := by
  simp [checkedFragmentNode, ConcreteSpliceAttachment.fragmentNode]

@[simp] theorem checkedIdentityNode_val
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    (step.checkedIdentityNode request).val =
      step.base.val.nodeCount + content.val.diagram.nodeCount + request.val := by
  simp [checkedIdentityNode, ConcreteSpliceAttachment.identityNode,
    Internal.checkedNode]

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
    simp [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
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
      left ∈ ConcreteDiagram.DenseErasure.retainedNodes
        step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, leftDifferent]
  have rightRetained :
      right ∈ ConcreteDiagram.DenseErasure.retainedNodes
        step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, rightDifferent]
  have indexed :
      ConcreteDiagram.DenseErasure.eraseNodeIndex
          step.prior step.priorApplication left leftRetained =
        ConcreteDiagram.DenseErasure.eraseNodeIndex
          step.prior step.priorApplication right rightRetained := by
    apply Fin.ext
    simpa [checkedPriorNode, Internal.checkedNode,
      ConcreteSpliceAttachment.hostNode] using congrArg Fin.val same
  change
    DenseList.index
        (ConcreteDiagram.DenseErasure.retainedNodes
          step.prior.val [step.priorApplication]) left leftRetained =
      DenseList.index
        (ConcreteDiagram.DenseErasure.retainedNodes
          step.prior.val [step.priorApplication]) right rightRetained at indexed
  have values :=
    congrArg
      (ConcreteDiagram.DenseErasure.retainedNodes
        step.prior.val [step.priorApplication]).get indexed
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

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
                  ConcreteDiagram.DenseErasure.retainedNodes
                    step.prior.val [step.priorApplication] := by
              simp [ConcreteDiagram.DenseErasure.retainedNodes,
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
                  ConcreteDiagram.DenseErasure.retainedNodes
                    step.prior.val [step.priorApplication] := by
              simp [ConcreteDiagram.DenseErasure.retainedNodes,
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
        ConcreteDiagram.DenseErasure.retainedNodes
          step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
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
        ConcreteDiagram.DenseErasure.retainedNodes
          step.prior.val [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
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
      ConcreteDiagram.DenseErasure.eraseNodeCandidate
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
    ConcreteDiagram.DenseErasure.eraseNodeRegion_encloses_iff]
  exact step.priorRegionImageEncloses outer inner

@[simp] theorem baseWire_signature
    (step : RelationJoinStep source dying content)
    (sourceWire : source.val.WireId) :
    (step.prior.val.wires (step.priorWireImage sourceWire)).sig =
      (step.base.val.wires (step.baseWireImage sourceWire)).sig := by
  rw [step.baseWireImageExact, Internal.checkedWire_signature_transport]
  exact
    (ConcreteDiagram.DenseErasure.eraseNodeWire_signature
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

end ConcreteWireQuantifier

end VisualProof
