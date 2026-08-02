import VisualProof.Rule.WirePrimitive.ArgumentsCore

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

structure AppliedArgDrop
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private attachments : List source.val.WireId
  private gate : Internal.DropGate source orientation wire attachments
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact : result.spec.localCount = 0
  private target_arguments_exact :
    result.targetArguments =
      ConcreteWirePrimitive.eraseAt sourceArguments position
  private arguments_exact :
    ∀ site : Fin result.sites.sites.length,
      result.spec.arguments site =
        existingReferences
          (ConcreteWirePrimitive.eraseAt
            (result.sites.sites.get site).arguments position)
  private ledger :
    ArgumentsSemantics.DropLedger result sourceArguments
  private semantics :
    Internal.DropSemanticReceipt (orientation := orientation) (position := position)
      ledger

structure AppliedArgExtend
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId) where
  private mk ::
  private gate : Internal.ExtendGate source orientation wire attachments
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact : result.spec.localCount = 0
  private target_arguments_exact :
    result.targetArguments =
      ConcreteWirePrimitive.insertAt sourceArguments position newArgument
  private position_valid : position ≤ sourceArguments.length
  private arguments_exact :
    ∀ site : Fin result.sites.sites.length,
      result.spec.arguments site =
        existingReferences
          (ConcreteWirePrimitive.insertAt
            (result.sites.sites.get site).arguments position
            ((attachments[site.val]?).getD wire))
  private ledger :
    ArgumentsSemantics.ExtendLedger result sourceArguments
  private semantics :
    Internal.ExtendSemanticReceipt (orientation := orientation) (position := position)
      ledger


namespace AppliedArgDrop

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDrop source orientation wire position) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :=
  applied.result

/-- Argument drop removes only its acted source head. -/
theorem sourceRemovedWires_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.argumentResult.sourceRemovedWires = [wire] :=
  applied.source_removed_exact

/-- Argument drop allocates no construction-local wires. -/
theorem localCount_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.argumentResult.spec.localCount = 0 :=
  applied.local_count_exact

def sourceArgumentList
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) : List Sig :=
  applied.sourceArguments

/-- Checker-owned source sites rebuilt by argument drop. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    AllAppliedSites source wire :=
  applied.result.sites

def targetNode
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.result.target.val.NodeId :=
  applied.result.targetNode site

theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def nodeEquiv
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    Data.Finite.FiniteEquiv source.val.NodeId applied.target.val.NodeId :=
  applied.result.nodeEquiv applied.targetSites

def wireEquiv
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    Data.Finite.FiniteEquiv source.val.WireId applied.target.val.WireId :=
  applied.result.wireEquivHeadOnly applied.source_removed_exact
    applied.local_count_exact

@[simp] theorem wireEquiv_head
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.wireEquiv wire = applied.targetWire := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  simp
  rfl

theorem nodeEquiv_generated
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.nodeEquiv (applied.result.sites.sites.get site).node =
      applied.result.targetNode site := by
  have generated : (applied.result.sites.sites.get site).node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨applied.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage
      (applied.result.sites.sites.get site).node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_pos generated]
  rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get
    applied.result.sites site generated]

theorem nodeEquiv_generated_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (node : source.val.NodeId)
    (generated : node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    applied.nodeEquiv node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.targetSites := by
  let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
    applied.sourceSites node generated
  have sourceExact : (applied.sourceSites.sites.get site).node = node :=
    ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
      applied.sourceSites node generated
  rw [← sourceExact]
  change applied.nodeEquiv (applied.result.sites.sites.get site).node ∈ _
  rw [applied.nodeEquiv_generated site]
  exact applied.result.generatedNode_targetSiteNode applied.targetSites site

theorem nodeEquiv_retained
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (node : source.val.NodeId)
    (retained : node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites) :
    applied.nodeEquiv node =
      applied.result.retainedNodeImage node retained := by
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]

theorem wireEquiv_retained
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.wireEquiv sourceWire =
      applied.result.retainedWireImage sourceWire (by
        rw [applied.source_removed_exact]
        simpa [different]) := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
  change (if same : sourceWire = wire then applied.result.targetWire
    else applied.result.retainedWireImage sourceWire _) = _
  rw [dif_neg different]

theorem wireEquiv_retained_signature
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [applied.wireEquiv_retained sourceWire different]
  exact applied.result.retainedWireImage_signature sourceWire _

theorem wireEquiv_retained_scope
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).scope =
      applied.result.regionEquiv (source.val.wires sourceWire).scope := by
  rw [applied.wireEquiv_retained sourceWire different,
    show
      (applied.target.val.wires
          (applied.result.retainedWireImage sourceWire _)).scope =
        applied.result.regionImage (source.val.wires sourceWire).scope by
      exact applied.result.retainedWireImage_scope sourceWire _]
  exact applied.result.regionImage_exact _

theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.result.targetArguments =
      ConcreteWirePrimitive.eraseAt applied.sourceArgumentList position :=
  applied.target_arguments_exact

def targetArgumentList
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) : List Sig :=
  applied.result.targetArguments

/-- Every generated drop application uses the exact checker-owned attachment
vector at its source-site position. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.result.spec.arguments site =
      existingReferences
        (ConcreteWirePrimitive.eraseAt
          (applied.result.sites.sites.get site).arguments position) :=
  applied.arguments_exact site

/-- A generated drop argument endpoint is owned by the checked image of the
exact attachment selected at that output position. -/
theorem generatedArgument_endpointOwner
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.result.sites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.result.targetArguments.length)
    (sourceWire : source.val.WireId)
    (selected : (applied.result.spec.arguments site)[targetPosition]? =
      some (.existing sourceWire)) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  by_cases different : sourceWire ≠ wire
  · have retained : sourceWire ∉ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simpa [different]
    have owner := applied.result.generatedArgument_endpointOwner site
      targetPosition targetBound sourceWire selected retained
    simpa [AppliedArgDrop.wireEquiv,
      ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
      ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
      using owner
  · have same : sourceWire = wire := Classical.not_not.mp different
    subst sourceWire
    rw [applied.wireEquiv_head]
    change applied.result.checked.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some applied.result.targetWire
    rw [applied.result.targetNode_argument_owner site targetPosition
      targetBound]
    congr 1
    unfold ConcreteWirePrimitive.replacementOwner
      ConcreteWirePrimitive.replacementNode
    simp only [Fin.addCases_right]
    rw [selected]
    simp only
    rw [ConcreteWirePrimitive.retainedReplacementWire?_head_none]
    exact applied.result.targetWire_exact.symm

/-- Public list-indexed form of generated drop endpoint ownership. -/
theorem generatedArgument_endpointOwner_of_selected
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.sourceSites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.targetArgumentList.length)
    (sourceWire : source.val.WireId)
    (selected :
      (ConcreteWirePrimitive.eraseAt
        (applied.sourceSites.sites.get site).arguments position)[
          targetPosition]? = some sourceWire) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  apply applied.generatedArgument_endpointOwner site targetPosition
    targetBound sourceWire
  rw [applied.siteArguments_exact site]
  unfold existingReferences
  rw [List.getElem?_map, show
    (ConcreteWirePrimitive.eraseAt
      (applied.result.sites.sites.get site).arguments position)[
        targetPosition]? = some sourceWire by
      simpa [sourceSites] using selected]
  rfl

/-- Exact target image of any source wire through argument drop.  The acted
head is replaced by the checked target head; every other wire is transported
by the replacement receipt's retained-wire map. -/
def transportWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId) :
    applied.target.val.WireId :=
  if same : sourceWire = wire then
    applied.targetWire
  else
    applied.result.retainedWireImage sourceWire (by
      rw [applied.source_removed_exact]
      simpa [same])

theorem transportWire_eq_wireEquiv
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId) :
    applied.transportWire sourceWire = applied.wireEquiv sourceWire := by
  unfold transportWire wireEquiv
    ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  rfl

/-- Pushing an endpoint of a retained node through argument drop preserves
its port and incidence on the exact transported wire. -/
theorem retainedEndpointImage_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints)
    (retained : endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv endpoint.node, endpoint.port⟩ :
      CEndpoint applied.target.val.nodeCount) ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints := by
  have sourceWireDifferent : sourceWire ≠ wire := by
    intro same
    subst sourceWire
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      endpoint incident)
  have sourceRetained : sourceWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [sourceWireDifferent]
  have targetIncident := applied.result.retainedNode_forwardIncident
    endpoint.node retained endpoint.port sourceWire incident
  have nodeImage := applied.nodeEquiv_retained endpoint.node retained
  have wireImage := applied.wireEquiv_retained sourceWire sourceWireDifferent
  have contextImage := applied.result.contextWireMap_retained sourceWire
    sourceRetained
  rw [contextImage, ← wireImage] at targetIncident
  simpa [nodeImage] using targetIncident

/-- Pulling an endpoint of a retained rebuilt node through argument drop
preserves its port and recovers incidence on the exact source wire. -/
theorem retainedEndpointInverse_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId)
    (candidate : CEndpoint applied.target.val.nodeCount)
    (incident : candidate ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints)
    (retained : applied.nodeEquiv.symm candidate.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv.symm candidate.node, candidate.port⟩ :
      CEndpoint source.val.nodeCount) ∈
      (source.val.wires sourceWire).endpoints := by
  let sourceNode := applied.nodeEquiv.symm candidate.node
  have nodeRecover : applied.nodeEquiv sourceNode = candidate.node :=
    applied.nodeEquiv.right_inv candidate.node
  have targetRequired : candidate.port ∈
      applied.target.val.requiredPorts candidate.node :=
    ConcreteDiagram.incident_port_required definitions applied.target.val
      applied.target.property (applied.wireEquiv sourceWire) candidate incident
  have targetNodeImage : applied.result.retainedNodeImage sourceNode retained =
      candidate.node := by
    rw [← applied.nodeEquiv_retained sourceNode retained]
    exact nodeRecover
  have sourceRequired : candidate.port ∈
      source.val.requiredPorts sourceNode := by
    have retainedData : applied.target.val.nodes
        (applied.result.retainedNodeImage sourceNode retained) =
          (source.val.nodes sourceNode).rename applied.result.regionEquiv :=
      applied.result.retainedNodeImage_data sourceNode retained
    rw [ConcreteDiagram.requiredPorts] at targetRequired ⊢
    rw [← targetNodeImage, retainedData] at targetRequired
    cases sourceData : source.val.nodes sourceNode <;>
      simp [sourceData, CNode.rename] at targetRequired ⊢
    all_goals exact targetRequired
  obtain ⟨actualWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode candidate.port sourceRequired
  have actualDifferent : actualWire ≠ wire := by
    intro same
    subst actualWire
    have actualIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, candidate.port⟩ wire sourceOwner
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      ⟨sourceNode, candidate.port⟩ actualIncident)
  have actualRetained : actualWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [actualDifferent]
  have forwardOwner := applied.result.retainedNodeImage_endpointOwner
    sourceNode retained candidate.port sourceRequired actualWire sourceOwner
  change applied.target.val.endpointOwner?
      ⟨applied.result.retainedNodeImage sourceNode retained,
        candidate.port⟩ =
    some (applied.result.retainedWireImage actualWire actualRetained)
    at forwardOwner
  have targetOwner : applied.target.val.endpointOwner? candidate =
      some (applied.wireEquiv sourceWire) :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      applied.target.val applied.target.property candidate.node candidate.port
      targetRequired (applied.wireEquiv sourceWire) incident
  rw [targetNodeImage, targetOwner,
    ← applied.wireEquiv_retained actualWire actualDifferent]
    at forwardOwner
  have actualExact : actualWire = sourceWire :=
    applied.wireEquiv.injective (Option.some.inj forwardOwner).symm
  subst actualWire
  exact ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceNode, candidate.port⟩ sourceWire sourceOwner

/-- The exact ordered attachment tuple erased by drop, transported into the
checked target.  Positions and repeated aliases are preserved. -/
def targetAttachments
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    List applied.target.val.WireId :=
  applied.attachments.map applied.transportWire

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDrop source orientation wire position) : StepTag :=
  .argDrop

end AppliedArgDrop

namespace AppliedArgExtend

private theorem eraseAt_insertAt_of_le
    (values : List α) (position : Nat) (value : α)
    (valid : position ≤ values.length) :
    ConcreteWirePrimitive.eraseAt
        (ConcreteWirePrimitive.insertAt values position value) position =
      values := by
  induction values generalizing position with
  | nil =>
      simp only [List.length_nil] at valid
      have positionZero : position = 0 := by omega
      subst position
      rfl
  | cons head tail induction =>
      cases position with
      | zero => rfl
      | succ position =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at valid
          simp [ConcreteWirePrimitive.insertAt,
            ConcreteWirePrimitive.eraseAt, induction position valid]

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (_ :
      AppliedArgExtend source orientation wire position newArgument
        attachments) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :=
  applied.result

/-- Argument extension removes only its acted source head. -/
theorem sourceRemovedWires_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    applied.argumentResult.sourceRemovedWires = [wire] :=
  applied.source_removed_exact

/-- Argument extension allocates no construction-local wires. -/
theorem localCount_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    applied.argumentResult.spec.localCount = 0 :=
  applied.local_count_exact

def sourceArgumentList
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : List Sig :=
  applied.sourceArguments

/-- Checker-owned source sites rebuilt by argument extension. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : AllAppliedSites source wire :=
  applied.result.sites

def targetNode
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.sourceSites.sites.length) :
    applied.result.target.val.NodeId :=
  applied.result.targetNode site

theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def nodeEquiv
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    Data.Finite.FiniteEquiv source.val.NodeId applied.target.val.NodeId :=
  applied.result.nodeEquiv applied.targetSites

def wireEquiv
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    Data.Finite.FiniteEquiv source.val.WireId applied.target.val.WireId :=
  applied.result.wireEquivHeadOnly applied.source_removed_exact
    applied.local_count_exact

@[simp] theorem wireEquiv_head
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    applied.wireEquiv wire = applied.targetWire := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  simp
  rfl

theorem nodeEquiv_generated
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.result.sites.sites.length) :
    applied.nodeEquiv (applied.result.sites.sites.get site).node =
      applied.result.targetNode site := by
  have generated : (applied.result.sites.sites.get site).node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨applied.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage
      (applied.result.sites.sites.get site).node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_pos generated]
  rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get
    applied.result.sites site generated]

theorem nodeEquiv_retained
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (node : source.val.NodeId)
    (retained : node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites) :
    applied.nodeEquiv node =
      applied.result.retainedNodeImage node retained := by
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]

theorem wireEquiv_retained
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.wireEquiv sourceWire =
      applied.result.retainedWireImage sourceWire (by
        rw [applied.source_removed_exact]
        simpa [different]) := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
  change (if same : sourceWire = wire then applied.result.targetWire
    else applied.result.retainedWireImage sourceWire _) = _
  rw [dif_neg different]

theorem wireEquiv_retained_signature
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [applied.wireEquiv_retained sourceWire different]
  exact applied.result.retainedWireImage_signature sourceWire _

theorem wireEquiv_retained_scope
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).scope =
      applied.result.regionEquiv (source.val.wires sourceWire).scope := by
  rw [applied.wireEquiv_retained sourceWire different,
    show
      (applied.target.val.wires
          (applied.result.retainedWireImage sourceWire _)).scope =
        applied.result.regionImage (source.val.wires sourceWire).scope by
      exact applied.result.retainedWireImage_scope sourceWire _]
  exact applied.result.regionImage_exact _

theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    applied.result.targetArguments =
      ConcreteWirePrimitive.insertAt applied.sourceArgumentList position
        newArgument :=
  applied.target_arguments_exact

def targetArgumentList
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments) : List Sig :=
  applied.result.targetArguments

/-- Exact relation signature of the rebuilt extension head. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments) :
    (applied.target.val.wires applied.targetWire).sig =
      .rel applied.targetArgumentList := by
  exact applied.argumentResult.targetWire_signature

/-- The checker-owned semantic deletion removes precisely the coordinate
introduced by extension and recovers the complete source argument vector. -/
theorem eraseTargetArguments_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments) :
    ConcreteWirePrimitive.eraseAt applied.targetArgumentList position =
      applied.sourceArgumentList := by
  rw [targetArgumentList, applied.targetArguments_exact]
  exact eraseAt_insertAt_of_le applied.sourceArgumentList
    position newArgument applied.position_valid

/-- The accepted extension coordinate is in range of its source vector. -/
theorem positionValid
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments) : position ≤ applied.sourceArgumentList.length :=
  applied.position_valid

/-- Every generated extension application uses the exact checker-owned
attachment vector at its source-site position. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.result.sites.sites.length) :
    applied.result.spec.arguments site =
      existingReferences
        (ConcreteWirePrimitive.insertAt
          (applied.result.sites.sites.get site).arguments position
          ((attachments[site.val]?).getD wire)) :=
  applied.arguments_exact site

/-- A generated extension argument endpoint is owned by the checked image of
the exact attachment selected at that output position. -/
theorem generatedArgument_endpointOwner
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.result.sites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.result.targetArguments.length)
    (sourceWire : source.val.WireId)
    (selected : (applied.result.spec.arguments site)[targetPosition]? =
      some (.existing sourceWire)) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  by_cases different : sourceWire ≠ wire
  · have retained : sourceWire ∉ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simpa [different]
    have owner := applied.result.generatedArgument_endpointOwner site
      targetPosition targetBound sourceWire selected retained
    simpa [AppliedArgExtend.wireEquiv,
      ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
      ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
      using owner
  · have same : sourceWire = wire := Classical.not_not.mp different
    subst sourceWire
    rw [applied.wireEquiv_head]
    change applied.result.checked.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some applied.result.targetWire
    rw [applied.result.targetNode_argument_owner site targetPosition
      targetBound]
    congr 1
    unfold ConcreteWirePrimitive.replacementOwner
      ConcreteWirePrimitive.replacementNode
    simp only [Fin.addCases_right]
    rw [selected]
    simp only
    rw [ConcreteWirePrimitive.retainedReplacementWire?_head_none]
    exact applied.result.targetWire_exact.symm

/-- Public list-indexed form of generated extension endpoint ownership. -/
theorem generatedArgument_endpointOwner_of_selected
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.sourceSites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.targetArgumentList.length)
    (sourceWire : source.val.WireId)
    (selected :
      (ConcreteWirePrimitive.insertAt
        (applied.sourceSites.sites.get site).arguments position
        ((attachments[site.val]?).getD wire))[targetPosition]? =
          some sourceWire) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  apply applied.generatedArgument_endpointOwner site targetPosition
    targetBound sourceWire
  rw [applied.siteArguments_exact site]
  unfold existingReferences
  rw [List.getElem?_map, show
    (ConcreteWirePrimitive.insertAt
      (applied.result.sites.sites.get site).arguments position
        ((attachments[site.val]?).getD wire))[targetPosition]? =
      some sourceWire by
        simpa [sourceSites] using selected]
  rfl

/-- The head of every generated extension node is owned by the rebuilt head
wire. -/
theorem generatedHead_endpointOwner
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .head⟩ = some applied.targetWire := by
  have generatedTarget :=
    applied.result.generatedNode_targetSiteNode applied.targetSites site
  unfold ConcreteWirePrimitive.argumentSiteNodes at generatedTarget
  rcases List.mem_map.mp generatedTarget with
    ⟨targetSite, _targetMember, targetNodeExact⟩
  have owner := targetSite.endpoint_owner
  change applied.target.val.endpointOwner?
      ⟨targetSite.node, .head⟩ = some applied.targetWire at owner
  rw [targetNodeExact] at owner
  exact owner

/-- A required argument port of a generated extension node is in the exact
checked target argument vector. -/
theorem generatedArgument_bound
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.sourceSites.sites.length)
    (index : Nat)
    (required : .arg index ∈
      applied.target.val.requiredPorts (applied.targetNode site)) :
    index < applied.targetArgumentList.length := by
  change .arg index ∈ applied.result.checked.val.requiredPorts
    (applied.result.targetNode site) at required
  rw [ConcreteDiagram.requiredPorts,
    applied.result.targetNode_data site] at required
  simpa [targetArgumentList] using required

/-- Generated extension nodes are atoms and therefore have no identity
ports. -/
theorem generatedIdentity_not_required
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (site : Fin applied.sourceSites.sites.length)
    (index : Nat) :
    .identity index ∉
      applied.target.val.requiredPorts (applied.targetNode site) := by
  change .identity index ∉ applied.result.checked.val.requiredPorts
    (applied.result.targetNode site)
  rw [ConcreteDiagram.requiredPorts,
    applied.result.targetNode_data site]
  simp

/-- The inserted argument port at a generated node is owned by the exact
site-indexed attachment selected by the accepted extension. -/
theorem generatedInserted_endpointOwner
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (positionValid : position ≤ applied.sourceArgumentList.length)
    (site : Fin applied.result.sites.sites.length) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg position⟩ =
      some (applied.wireEquiv ((attachments[site.val]?).getD wire)) := by
  let sourceSite := applied.result.sites.sites.get site
  have siteLength : sourceSite.arguments.length =
      applied.sourceArgumentList.length :=
    sourceSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          applied.sourceArgumentList applied.sourceWire_signature sourceSite))
  have siteValid : position ≤ sourceSite.arguments.length := by
    rw [siteLength]
    exact positionValid
  have inserted := ConcreteWirePrimitive.insertAt_getElem?_self
    sourceSite.arguments position ((attachments[site.val]?).getD wire)
    siteValid
  have targetInserted := ConcreteWirePrimitive.insertAt_getElem?_self
    applied.sourceArgumentList position newArgument positionValid
  have targetGet : applied.result.targetArguments[position]? =
      some newArgument := by
    rw [applied.targetArguments_exact]
    exact targetInserted
  have targetBound : position < applied.result.targetArguments.length := by
    exact (List.getElem?_eq_some_iff.mp targetGet).choose
  have selected : (applied.result.spec.arguments site)[position]? =
      some (.existing ((attachments[site.val]?).getD wire)) := by
    rw [applied.arguments_exact site]
    unfold existingReferences
    rw [List.getElem?_map, inserted]
    rfl
  by_cases different : ((attachments[site.val]?).getD wire) ≠ wire
  · have retained : ((attachments[site.val]?).getD wire) ∉
        applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simpa [different]
    have owner := applied.result.generatedArgument_endpointOwner site
      position targetBound ((attachments[site.val]?).getD wire) selected
      retained
    simpa [AppliedArgExtend.wireEquiv,
      ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
      ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
      using owner
  · have same : (attachments[site.val]?).getD wire = wire :=
      Classical.not_not.mp different
    rw [same]
    rw [applied.wireEquiv_head]
    change applied.result.checked.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg position⟩ =
      some applied.result.targetWire
    rw [applied.result.targetNode_argument_owner site position targetBound]
    congr 1
    unfold ConcreteWirePrimitive.replacementOwner
      ConcreteWirePrimitive.replacementNode
    simp only [Fin.addCases_right]
    rw [selected]
    simp only [same]
    rw [ConcreteWirePrimitive.retainedReplacementWire?_head_none]
    exact applied.result.targetWire_exact.symm

/-- Pushing an endpoint of a retained node through argument extension
preserves its port and incidence on the exact transported wire. -/
theorem retainedEndpointImage_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints)
    (retained : endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv endpoint.node, endpoint.port⟩ :
      CEndpoint applied.target.val.nodeCount) ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints := by
  have sourceWireDifferent : sourceWire ≠ wire := by
    intro same
    subst sourceWire
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      endpoint incident)
  have sourceRetained : sourceWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [sourceWireDifferent]
  have targetIncident := applied.result.retainedNode_forwardIncident
    endpoint.node retained endpoint.port sourceWire incident
  have nodeImage := applied.nodeEquiv_retained endpoint.node retained
  have wireImage := applied.wireEquiv_retained sourceWire sourceWireDifferent
  have contextImage := applied.result.contextWireMap_retained sourceWire
    sourceRetained
  rw [contextImage, ← wireImage] at targetIncident
  simpa [nodeImage] using targetIncident

/-- Pulling an endpoint of a retained rebuilt node through argument extension
preserves its port and recovers incidence on the exact source wire. -/
theorem retainedEndpointInverse_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (sourceWire : source.val.WireId)
    (candidate : CEndpoint applied.target.val.nodeCount)
    (incident : candidate ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints)
    (retained : applied.nodeEquiv.symm candidate.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv.symm candidate.node, candidate.port⟩ :
      CEndpoint source.val.nodeCount) ∈
      (source.val.wires sourceWire).endpoints := by
  let sourceNode := applied.nodeEquiv.symm candidate.node
  have nodeRecover : applied.nodeEquiv sourceNode = candidate.node :=
    applied.nodeEquiv.right_inv candidate.node
  have targetRequired : candidate.port ∈
      applied.target.val.requiredPorts candidate.node :=
    ConcreteDiagram.incident_port_required definitions applied.target.val
      applied.target.property (applied.wireEquiv sourceWire) candidate incident
  have targetNodeImage : applied.result.retainedNodeImage sourceNode retained =
      candidate.node := by
    rw [← applied.nodeEquiv_retained sourceNode retained]
    exact nodeRecover
  have sourceRequired : candidate.port ∈
      source.val.requiredPorts sourceNode := by
    have retainedData : applied.target.val.nodes
        (applied.result.retainedNodeImage sourceNode retained) =
          (source.val.nodes sourceNode).rename applied.result.regionEquiv :=
      applied.result.retainedNodeImage_data sourceNode retained
    rw [ConcreteDiagram.requiredPorts] at targetRequired ⊢
    rw [← targetNodeImage, retainedData] at targetRequired
    cases sourceData : source.val.nodes sourceNode <;>
      simp [sourceData, CNode.rename] at targetRequired ⊢
    all_goals exact targetRequired
  obtain ⟨actualWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode candidate.port sourceRequired
  have actualDifferent : actualWire ≠ wire := by
    intro same
    subst actualWire
    have actualIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, candidate.port⟩ wire sourceOwner
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      ⟨sourceNode, candidate.port⟩ actualIncident)
  have actualRetained : actualWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [actualDifferent]
  have forwardOwner := applied.result.retainedNodeImage_endpointOwner
    sourceNode retained candidate.port sourceRequired actualWire sourceOwner
  change applied.target.val.endpointOwner?
      ⟨applied.result.retainedNodeImage sourceNode retained,
        candidate.port⟩ =
    some (applied.result.retainedWireImage actualWire actualRetained)
    at forwardOwner
  have targetOwner : applied.target.val.endpointOwner? candidate =
      some (applied.wireEquiv sourceWire) :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      applied.target.val applied.target.property candidate.node candidate.port
      targetRequired (applied.wireEquiv sourceWire) incident
  rw [targetNodeImage, targetOwner,
    ← applied.wireEquiv_retained actualWire actualDifferent]
    at forwardOwner
  have actualExact : actualWire = sourceWire :=
    applied.wireEquiv.injective (Option.some.inj forwardOwner).symm
  subst actualWire
  exact ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceNode, candidate.port⟩ sourceWire sourceOwner

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (_ :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : StepTag :=
  .argExtend

end AppliedArgExtend

namespace AppliedArgDrop

/-- The supplied suffix isomorphism identifies the inverse extension's
source argument vector with the checked drop target vector. -/
theorem inverseSourceArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.sourceArgumentList = forward.result.targetArguments := by
  have signatureExact := targetIso.wire_signature backwardWire
  have forwardSignature :
      (forward.target.val.wires forward.targetWire).sig =
        .rel forward.result.targetArguments :=
    forward.result.targetWire_signature
  have backwardSignature :
      (real.val.wires backwardWire).sig =
        .rel backward.sourceArgumentList :=
    backward.sourceWire_signature
  rw [wireExact, forwardSignature, backwardSignature] at signatureExact
  exact Sig.rel.inj signatureExact.symm

/-- Drop followed by the checked inverse extension restores the complete
planned argument vector. -/
theorem inverseTargetArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument) :
    backward.result.targetArguments = forward.sourceArgumentList := by
  calc
    backward.result.targetArguments =
        ConcreteWirePrimitive.insertAt backward.sourceArgumentList position
          newArgument := backward.targetArguments_exact
    _ = ConcreteWirePrimitive.insertAt forward.result.targetArguments
          position newArgument := by
      rw [forward.inverseSourceArguments_exact backward targetIso wireExact]
    _ = ConcreteWirePrimitive.insertAt
          (ConcreteWirePrimitive.eraseAt forward.sourceArgumentList position)
          position newArgument := by
      rw [forward.targetArguments_exact]
    _ = forward.sourceArgumentList :=
      ConcreteWirePrimitive.insertAt_eraseAt_of_getElem?_eq_some
        forward.sourceArgumentList position newArgument argumentExact

/-- Region carrier of a transported inverse drop/extension pair. -/
def inverseTransportRegionEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.RegionId
      planned.val.RegionId :=
  forward.result.inverseTransportRegionEquiv backward.result targetIso

/-- Node carrier of a transported inverse drop/extension pair. -/
def inverseTransportNodeEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.NodeId planned.val.NodeId :=
  forward.result.inverseTransportNodeEquiv backward.result
    forward.targetSites backward.targetSites targetIso

/-- Wire carrier of a transported inverse drop/extension pair. -/
def inverseTransportWireEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.WireId planned.val.WireId :=
  forward.result.inverseTransportWireEquivHeadOnly backward.result
    forward.source_removed_exact forward.local_count_exact
    backward.source_removed_exact backward.local_count_exact targetIso

/-- The composed wire carrier sends the inverse extension's rebuilt head
back to the original planned head. -/
@[simp] theorem inverseTransportWireEquiv_head
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    forward.inverseTransportWireEquiv backward targetIso
        backward.targetWire = forwardWire := by
  unfold inverseTransportWireEquiv
  change forward.wireEquiv.symm
    (targetIso.wires (backward.wireEquiv.symm backward.targetWire)) = _
  calc
    forward.wireEquiv.symm
        (targetIso.wires (backward.wireEquiv.symm backward.targetWire)) =
      forward.wireEquiv.symm (targetIso.wires backwardWire) := by
        congr 2
        rw [← backward.wireEquiv_head]
        exact backward.wireEquiv.left_inv backwardWire
    _ = forward.wireEquiv.symm forward.targetWire :=
      congrArg forward.wireEquiv.symm wireExact
    _ = forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire

/-- The transported inverse region carrier sends the rebuilt root exactly
back to the planned root. -/
theorem inverseTransport_root
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val) :
    forward.inverseTransportRegionEquiv backward targetIso
        backward.target.val.root = planned.val.root := by
  unfold inverseTransportRegionEquiv
  change forward.result.regionEquiv.symm
    (targetIso.regions
      (backward.result.regionEquiv.symm backward.target.val.root)) = _
  have backwardRoot : backward.target.val.root =
      backward.result.regionEquiv real.val.root := by
    exact backward.result.targetRoot_exact.trans
      (backward.result.regionImage_exact real.val.root)
  rw [backwardRoot]
  have backwardCancel :=
    backward.result.regionEquiv.left_inv real.val.root
  change backward.result.regionEquiv.invFun
      (backward.result.regionEquiv real.val.root) = real.val.root
    at backwardCancel
  calc
    forward.result.regionEquiv.symm
        (targetIso.regions
          (backward.result.regionEquiv.symm
            (backward.result.regionEquiv real.val.root))) =
        forward.result.regionEquiv.symm
          (targetIso.regions real.val.root) :=
      congrArg (fun value => forward.result.regionEquiv.symm
        (targetIso.regions value)) backwardCancel
    _ = forward.result.regionEquiv.symm forward.target.val.root := by
      rw [targetIso.root]
    _ = forward.result.regionEquiv.symm
        (forward.result.regionEquiv planned.val.root) := by
      congr 1
      exact forward.result.targetRoot_exact.trans
        (forward.result.regionImage_exact planned.val.root)
    _ = planned.val.root := forward.result.regionEquiv.left_inv _

/-- Region tables commute with the transported inverse carrier. -/
theorem inverseTransport_region_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (region : backward.target.val.RegionId) :
    planned.val.regions
        (forward.inverseTransportRegionEquiv backward targetIso region) =
      (backward.target.val.regions region).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realRegion := backward.result.regionEquiv.symm region
  have backwardData := backward.result.regionImage_data realRegion
  have backwardRegionExact : backward.result.regionEquiv realRegion = region :=
    backward.result.regionEquiv.right_inv region
  rw [backwardRegionExact] at backwardData
  have backwardDataPublic : backward.target.val.regions region =
      (real.val.regions realRegion).rename backward.result.regionEquiv :=
    backwardData
  have middleData := targetIso.region_table realRegion
  have plannedData := forward.result.regionImage_data
    (forward.result.regionEquiv.symm (targetIso.regions realRegion))
  have plannedRegionExact :
      forward.result.regionEquiv
          (forward.result.regionEquiv.symm (targetIso.regions realRegion)) =
        targetIso.regions realRegion :=
    forward.result.regionEquiv.right_inv _
  rw [plannedRegionExact] at plannedData
  unfold inverseTransportRegionEquiv
  change planned.val.regions
      (forward.result.regionEquiv.symm (targetIso.regions realRegion)) = _
  rw [backwardDataPublic]
  have middleRelation :
      (real.val.regions realRegion).rename targetIso.regions =
        (planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion))).rename
          forward.result.regionEquiv :=
    middleData.symm.trans plannedData
  cases realData : real.val.regions realRegion with
  | sheet =>
      cases plannedDataExact : planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet => rfl
      | cut parent =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
  | cut realParent =>
      cases plannedDataExact : planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
      | cut plannedParent =>
          rw [realData, plannedDataExact] at middleRelation
          simp only [CRegion.rename] at middleRelation
          have parentRelation : targetIso.regions realParent =
              forward.result.regionEquiv plannedParent :=
            CRegion.cut.inj middleRelation
          congr 1
          unfold ConcreteWirePrimitive.ArgumentResult.inverseTransportRegionEquiv
          change plannedParent = forward.result.regionEquiv.symm
            (targetIso.regions
              (backward.result.regionEquiv.symm
                (backward.result.regionEquiv realParent)))
          have backwardParentCancel :=
            backward.result.regionEquiv.left_inv realParent
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realParent) = realParent
            at backwardParentCancel
          calc
            plannedParent = forward.result.regionEquiv.symm
                (targetIso.regions realParent) :=
              (forward.result.regionEquiv.left_inv plannedParent).symm.trans
                (congrArg forward.result.regionEquiv.symm
                  parentRelation).symm
            _ = forward.result.regionEquiv.symm
                (targetIso.regions
                  (backward.result.regionEquiv.symm
                    (backward.result.regionEquiv realParent))) :=
              congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardParentCancel.symm

/-- Planned source-site position represented by one real head endpoint after
transport through the supplied target isomorphism. -/
def inverseTransportSourcePosition
    {planned real : CheckedDiagram definitions}
    {forwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (sourceEndpoint : CEndpoint real.val.nodeCount)
    (sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints) :
    Fin forward.result.sites.sites.length :=
  let middleEndpoint := targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleNode := (forward.targetSites.sites.get middlePosition).node
  have generated : middleNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.targetSites.sites.get middlePosition,
        List.get_mem _ _, rfl⟩
  forward.result.sourcePositionOfTargetNode forward.targetSites
    middleNode generated

/-- Site-indexed inverse attachments in real source order.  Each real head
endpoint is transported to its corresponding forward target site before the
construction-owned dropped attachment is selected and pulled back. -/
def inverseAttachments
    {planned real : CheckedDiagram definitions}
    {forwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    List real.val.WireId :=
  List.ofFn fun endpointPosition =>
    let sourceEndpoint :=
      (real.val.wires backwardWire).endpoints.get endpointPosition
    let plannedPosition := forward.inverseTransportSourcePosition targetIso
      wireExact sourceEndpoint (List.get_mem _ _)
    let sourceAttachment :=
      ((forward.result.sites.sites.get plannedPosition).arguments[position]?).getD
        forwardWire
    targetIso.wires.symm (forward.transportWire sourceAttachment)

@[simp] theorem inverseAttachments_length
    {planned real : CheckedDiagram definitions}
    {forwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    (forward.inverseAttachments targetIso wireExact).length =
      (real.val.wires backwardWire).endpoints.length := by
  simp [inverseAttachments]

/-- Exact attachment selected at one real head-endpoint position. -/
theorem inverseAttachments_get
    {planned real : CheckedDiagram definitions}
    {forwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (endpointPosition :
      Fin (real.val.wires backwardWire).endpoints.length) :
    (forward.inverseAttachments targetIso wireExact).get
        (Fin.cast (forward.inverseAttachments_length targetIso wireExact).symm
          endpointPosition) =
      let sourceEndpoint :=
        (real.val.wires backwardWire).endpoints.get endpointPosition
      let plannedPosition := forward.inverseTransportSourcePosition targetIso
        wireExact sourceEndpoint (List.get_mem _ _)
      let sourceAttachment :=
        ((forward.result.sites.sites.get plannedPosition).arguments[position]?).getD
          forwardWire
      targetIso.wires.symm (forward.transportWire sourceAttachment) := by
  simp [inverseAttachments]

/-- Planned source-site position represented by one real source site after
transport through the supplied target isomorphism. -/
def inverseTransportSitePosition
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    Fin forward.result.sites.sites.length :=
  let sourceEndpoint := (backward.result.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.result.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  forward.inverseTransportSourcePosition targetIso wireExact
    sourceEndpoint sourceMember

/-- The site-indexed inverse attachment is exactly the dropped attachment at
the endpoint-derived planned source position. -/
theorem inverseAttachments_site
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (site : Fin backward.result.sites.sites.length) :
    let endpointPosition := Fin.cast backward.result.sites.length site
    (forward.inverseAttachments targetIso wireExact).get
        (Fin.cast (forward.inverseAttachments_length targetIso wireExact).symm
          endpointPosition) =
      targetIso.wires.symm (forward.transportWire
        (((forward.result.sites.sites.get
          (forward.inverseTransportSitePosition backward targetIso
            wireExact site)).arguments[position]?).getD forwardWire)) := by
  dsimp only
  let endpointPosition := Fin.cast backward.result.sites.length site
  have endpointExact :
      (real.val.wires backwardWire).endpoints.get endpointPosition =
        (backward.result.sites.sites.get site).endpoint := by
    have selected := get_of_list_eq backward.result.sites.exhaustive
      endpointPosition
    have selectedPosition :
        Fin.cast (congrArg List.length
          backward.result.sites.exhaustive).symm endpointPosition =
          Fin.cast (by simp) site := by
      apply Fin.ext
      rfl
    rw [selectedPosition] at selected
    simpa using selected.symm
  rw [forward.inverseAttachments_get targetIso wireExact endpointPosition]
  simp only
  have sourceMember : (backward.result.sites.sites.get site).endpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.result.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  let rawEndpoint :
      { endpoint // endpoint ∈
        (real.val.wires backwardWire).endpoints } :=
    ⟨(real.val.wires backwardWire).endpoints.get endpointPosition,
      List.get_mem _ _⟩
  let siteEndpoint :
      { endpoint // endpoint ∈
        (real.val.wires backwardWire).endpoints } :=
    ⟨(backward.result.sites.sites.get site).endpoint, sourceMember⟩
  have endpointsEqual : rawEndpoint = siteEndpoint := by
    apply Subtype.ext
    exact endpointExact
  have positionsEqual := congrArg
    (fun endpoint : { endpoint // endpoint ∈
        (real.val.wires backwardWire).endpoints } =>
      forward.inverseTransportSourcePosition targetIso wireExact
        endpoint.val endpoint.property) endpointsEqual
  unfold inverseTransportSitePosition
  exact congrArg (fun plannedPosition =>
    targetIso.wires.symm (forward.transportWire
      (((forward.result.sites.sites.get plannedPosition).arguments[position]?).getD
        forwardWire))) positionsEqual

/-- Executable optional lookup at a real site reduces to the exact
site-indexed inverse attachment. -/
theorem inverseAttachments_getD_site
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (site : Fin backward.result.sites.sites.length) :
    ((forward.inverseAttachments targetIso wireExact)[site.val]?).getD
        backwardWire =
      targetIso.wires.symm (forward.transportWire
        (((forward.result.sites.sites.get
          (forward.inverseTransportSitePosition backward targetIso
            wireExact site)).arguments[position]?).getD forwardWire)) := by
  have bound : site.val <
      (forward.inverseAttachments targetIso wireExact).length := by
    rw [forward.inverseAttachments_length targetIso wireExact,
      ← backward.result.sites.length]
    exact site.isLt
  rw [List.getElem?_eq_getElem bound]
  have exact := forward.inverseAttachments_site targetIso wireExact
    backward site
  dsimp only at exact
  rw [← exact]
  apply congrArg (forward.inverseAttachments targetIso wireExact).get
  apply Fin.ext
  rfl

/-- The transported inverse node carrier sends each rebuilt node to the
exact planned source site selected by endpoint transport. -/
theorem inverseTransport_targetNode
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    forward.inverseTransportNodeEquiv backward targetIso
        (backward.result.targetNode site) =
      (forward.result.sites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node := by
  let backwardNode := (backward.result.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.result.targetNode site := by
    unfold AppliedArgExtend.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.result.nodeImage backwardNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos backwardMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let sourceEndpoint := (backward.result.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.result.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint := targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleSite := forward.targetSites.sites.get middlePosition
  have middleNodeExact : middleSite.node = targetIso.nodes backwardNode := by
    have selected := get_of_list_eq forward.targetSites.exhaustive
      middleEndpointPosition
    have endpointExact := DenseList.get_index
      (forward.target.val.wires forward.targetWire).endpoints
      middleEndpoint middleMember
    rw [endpointExact] at selected
    have selectedPosition :
        Fin.cast (congrArg List.length
          forward.targetSites.exhaustive).symm middleEndpointPosition =
          Fin.cast (by simp) middlePosition := by
      apply Fin.ext
      rfl
    rw [selectedPosition] at selected
    have corresponds := targetIso.endpointMap_corresponds backwardWire
      sourceEndpoint sourceMember
    simpa [middleSite, sourceEndpoint, backwardNode, AppliedSite.endpoint]
      using (congrArg CEndpoint.node selected).trans corresponds.1
  have middleGenerated : middleSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr ⟨middleSite, List.get_mem _ _, rfl⟩
  let plannedPosition := forward.result.sourcePositionOfTargetNode
    forward.targetSites middleSite.node middleGenerated
  have forwardTarget : forward.result.targetNode plannedPosition =
      middleSite.node :=
    forward.result.targetNode_sourcePositionOfTargetNode
      forward.targetSites middleSite.node middleGenerated
  let plannedNode :=
    (forward.result.sites.sites.get plannedPosition).node
  have plannedMember : plannedNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.result.sites.sites.get plannedPosition,
        List.get_mem _ _, rfl⟩
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.result.targetNode plannedPosition := by
    unfold AppliedArgDrop.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.result.nodeImage plannedNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos plannedMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  unfold inverseTransportNodeEquiv
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.result.targetNode site))) = _
  rw [backwardInverse, ← middleNodeExact,
    ← forwardTarget, ← forwardImage]
  change forward.nodeEquiv.symm (forward.nodeEquiv plannedNode) = plannedNode
  exact forward.nodeEquiv.left_inv plannedNode

/-- The exact forward target node underlying a transported backward site. -/
theorem inverseTransport_middleNode
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    targetIso.nodes (backward.result.sites.sites.get site).node =
      forward.result.targetNode
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site) := by
  let backwardNode := (backward.result.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.result.targetNode site := by
    exact backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedNode :=
    (forward.result.sites.sites.get plannedPosition).node
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.result.targetNode plannedPosition := by
    exact forward.nodeEquiv_generated plannedPosition
  have carrierExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  unfold inverseTransportNodeEquiv at carrierExact
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.result.targetNode site))) =
      plannedNode at carrierExact
  rw [backwardInverse] at carrierExact
  have lifted := congrArg forward.nodeEquiv carrierExact
  have forwardCancel := forward.nodeEquiv.right_inv
    (targetIso.nodes backwardNode)
  change forward.nodeEquiv
      (forward.nodeEquiv.symm (targetIso.nodes backwardNode)) =
    targetIso.nodes backwardNode at forwardCancel
  have exactMiddle : targetIso.nodes backwardNode =
      forward.nodeEquiv plannedNode :=
    forwardCancel.symm.trans lifted
  rw [forwardImage] at exactMiddle
  exact exactMiddle

/-- Rebuilt nodes satisfy the transported node-table law; the erased and
reinserted argument vector cancels at the selected position. -/
theorem inverseTransport_generated_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (site : Fin backward.result.sites.sites.length) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.result.targetNode site)) =
      (backward.target.val.nodes
        (backward.result.targetNode site)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  let backwardSite := backward.result.sites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.result.sites.sites.get plannedPosition
  have nodeExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  have backwardTargetData : backward.target.val.nodes
      (backward.result.targetNode site) =
    .atom (backward.result.regionImage backwardSite.region)
      backward.result.targetArguments := by
    exact backward.result.targetNode_data site
  rw [nodeExact, plannedSite.node_data, backwardTargetData]
  have targetNodeExact := forward.inverseTransport_middleNode backward
    targetIso wireExact site
  have mappedData := targetIso.node_table backwardSite.node
  rw [backwardSite.node_data, targetNodeExact] at mappedData
  have forwardTargetData : forward.target.val.nodes
      (forward.result.targetNode plannedPosition) =
    .atom (forward.result.regionImage plannedSite.region)
      forward.result.targetArguments := by
    exact forward.result.targetNode_data plannedPosition
  rw [forwardTargetData] at mappedData
  have regionExact : forward.result.regionImage plannedSite.region =
      targetIso.regions backwardSite.region :=
    (CNode.atom.inj mappedData).1
  have restored := forward.inverseTargetArguments_exact backward
    targetIso wireExact argumentExact
  rw [restored]
  have plannedArguments : plannedSite.argumentSignatures =
      forward.sourceArgumentList :=
    ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
      forward.sourceArgumentList forward.sourceWire_signature plannedSite
  rw [plannedArguments]
  congr 2
  unfold inverseTransportRegionEquiv
  change plannedSite.region = forward.result.regionEquiv.symm
    (targetIso.regions
      (backward.result.regionEquiv.symm
        (backward.result.regionImage backwardSite.region)))
  rw [backward.result.regionImage_exact]
  have backwardCancel :=
    backward.result.regionEquiv.left_inv backwardSite.region
  change backward.result.regionEquiv.invFun
      (backward.result.regionEquiv backwardSite.region) =
    backwardSite.region at backwardCancel
  have forwardRegionExact :=
    forward.result.regionImage_exact plannedSite.region
  calc
    plannedSite.region = forward.result.regionEquiv.symm
        (forward.result.regionEquiv plannedSite.region) :=
      (forward.result.regionEquiv.left_inv plannedSite.region).symm
    _ = forward.result.regionEquiv.symm
        (forward.result.regionImage plannedSite.region) := by
      rw [forwardRegionExact]
    _ = forward.result.regionEquiv.symm
        (targetIso.regions backwardSite.region) :=
      congrArg forward.result.regionEquiv.symm regionExact
    _ = forward.result.regionEquiv.symm
        (targetIso.regions
          (backward.result.regionEquiv.symm
            (backward.result.regionEquiv backwardSite.region))) :=
      congrArg (fun value => forward.result.regionEquiv.symm
        (targetIso.regions value)) backwardCancel.symm

/-- A real node retained by extension cannot transport to a generated
forward drop target site. -/
theorem inverseTransport_middleNode_retained
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites) :
    targetIso.nodes realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
  intro generated
  unfold ConcreteWirePrimitive.argumentSiteNodes at generated
  rcases List.mem_map.mp generated with
    ⟨middleSite, middleMember, middleNodeExact⟩
  have targetOwner : forward.target.val.endpointOwner?
      ⟨targetIso.nodes realNode, .head⟩ = some forward.targetWire := by
    rw [← middleNodeExact]
    exact middleSite.endpoint_owner
  have mappedData := targetIso.node_table realNode
  have middleData : forward.target.val.nodes (targetIso.nodes realNode) =
      .atom middleSite.region middleSite.argumentSignatures := by
    rw [← middleNodeExact]
    exact middleSite.node_data
  cases sourceData : real.val.nodes realNode with
  | atom region arguments =>
      have sourceOwner := targetIso.atom_owner_backward real.property
        sourceData targetOwner
      have inverseWireExact : targetIso.wires.symm forward.targetWire =
          backwardWire := by
        calc
          targetIso.wires.symm forward.targetWire =
              targetIso.wires.symm (targetIso.wires backwardWire) := by
            rw [wireExact]
          _ = backwardWire := targetIso.wires.left_inv backwardWire
      rw [inverseWireExact] at sourceOwner
      have incident := ConcreteDiagram.endpointOwner?_incident real.val
        ⟨realNode, .head⟩ backwardWire sourceOwner
      rw [← backward.result.sites.exhaustive] at incident
      rcases List.mem_map.mp incident with
        ⟨sourceSite, sourceMember, endpointExact⟩
      apply retained
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨sourceSite, sourceMember,
          congrArg CEndpoint.node endpointExact⟩
  | ref region definition arguments =>
      rw [middleData, sourceData] at mappedData
      contradiction
  | identity region signature arity =>
      rw [middleData, sourceData] at mappedData
      contradiction

/-- Retained extension nodes satisfy the complete transported node-table
law. -/
theorem inverseTransport_retained_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.result.retainedNodeImage realNode retained)) =
      (backward.target.val.nodes
        (backward.result.retainedNodeImage realNode retained)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  have middleRetained := forward.inverseTransport_middleNode_retained
    backward targetIso wireExact realNode retained
  let plannedNode := forward.result.sourceNodeOfRetainedTarget
    forward.targetSites (targetIso.nodes realNode) middleRetained
  have plannedRetained : plannedNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.result.sites :=
    ConcreteWirePrimitive.sourceRetainedNode_not_removed
      forward.result.sites
      (forward.result.retainedBaseNodeOfTarget forward.targetSites
        (targetIso.nodes realNode) middleRetained)
  have backwardImage : backward.nodeEquiv realNode =
      backward.result.retainedNodeImage realNode retained :=
    backward.nodeEquiv_retained realNode retained
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.retainedNodeImage realNode retained) = realNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv realNode
  have forwardInverse : forward.nodeEquiv.symm
      (targetIso.nodes realNode) = plannedNode := by
    unfold AppliedArgDrop.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.result.sourceNode forward.targetSites
      (targetIso.nodes realNode) = plannedNode
    unfold ConcreteWirePrimitive.ArgumentResult.sourceNode
    split
    next generated => exact (middleRetained generated).elim
    next _ => rfl
  have carrierExact : forward.inverseTransportNodeEquiv backward targetIso
      (backward.result.retainedNodeImage realNode retained) =
        plannedNode := by
    unfold inverseTransportNodeEquiv
    change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm
          (backward.result.retainedNodeImage realNode retained))) = _
    rw [backwardInverse, forwardInverse]
  rw [carrierExact]
  have backwardData : backward.target.val.nodes
      (backward.result.retainedNodeImage realNode retained) =
        (real.val.nodes realNode).rename backward.result.regionEquiv :=
    backward.result.retainedNodeImage_data realNode retained
  rw [backwardData]
  have forwardImage : forward.result.retainedNodeImage plannedNode
      plannedRetained = targetIso.nodes realNode :=
    forward.result.retainedNodeImage_sourceNodeOfRetainedTarget
      forward.targetSites (targetIso.nodes realNode) middleRetained
  have forwardData : forward.target.val.nodes (targetIso.nodes realNode) =
      (planned.val.nodes plannedNode).rename forward.result.regionEquiv := by
    rw [← forwardImage]
    exact forward.result.retainedNodeImage_data plannedNode plannedRetained
  have middleData := targetIso.node_table realNode
  rw [forwardData] at middleData
  cases realData : real.val.nodes realNode with
  | atom realRegion realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.atom.inj middleData
          cases parts.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | ref realRegion realDefinition realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion plannedDefinition plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.ref.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | identity realRegion realSignature realArity =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion plannedSignature plannedArity =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.identity.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))

/-- Complete node-table law for the transported inverse drop/extension
carrier. -/
theorem inverseTransport_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (node : backward.target.val.NodeId) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso node) =
      (backward.target.val.nodes node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realNode := backward.nodeEquiv.symm node
  have nodeRecover : backward.nodeEquiv realNode = node :=
    backward.nodeEquiv.right_inv node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.result.sites realNode generated
    have imageExact : backward.nodeEquiv realNode =
        backward.result.targetNode site := by
      unfold AppliedArgExtend.nodeEquiv
        ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.result.nodeImage realNode = _
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos generated]
    have nodeExact : node = backward.result.targetNode site :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_generated_node_table backward
      targetIso wireExact argumentExact site
  · have imageExact : backward.nodeEquiv realNode =
        backward.result.retainedNodeImage realNode generated :=
      backward.nodeEquiv_retained realNode generated
    have nodeExact : node =
        backward.result.retainedNodeImage realNode generated :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_retained_node_table backward
      targetIso wireExact realNode generated

/-- The transported inverse wire carrier acts on every inverse-construction
image by composing the three construction-owned wire equivalences. -/
theorem inverseTransport_wireEquiv_image
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (realWire : real.val.WireId) :
    forward.inverseTransportWireEquiv backward targetIso
        (backward.wireEquiv realWire) =
      forward.wireEquiv.symm (targetIso.wires realWire) := by
  unfold inverseTransportWireEquiv
  change forward.wireEquiv.symm
    (targetIso.wires
      (backward.wireEquiv.symm (backward.wireEquiv realWire))) = _
  have backwardCancel := backward.wireEquiv.left_inv realWire
  change backward.wireEquiv.invFun (backward.wireEquiv realWire) =
    realWire at backwardCancel
  exact congrArg (fun value => forward.wireEquiv.symm
    (targetIso.wires value)) backwardCancel

/-- Complete wire-signature law for the transported inverse carrier. -/
theorem inverseTransport_wire_signature
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).sig =
      (backward.target.val.wires targetWire).sig := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    have backwardTargetSignature :
        (backward.target.val.wires backward.targetWire).sig =
          .rel backward.result.targetArguments := by
      exact backward.result.targetWire_signature
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head,
      forward.sourceWire_signature, backwardTargetSignature]
    have restored := forward.inverseTargetArguments_exact backward
      targetIso wireExact argumentExact
    exact congrArg Sig.rel restored.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    calc
      (planned.val.wires plannedWire).sig =
          (forward.target.val.wires (targetIso.wires realWire)).sig := by
        rw [← plannedImage]
        exact (forward.wireEquiv_retained_signature plannedWire
          plannedDifferent).symm
      _ = (real.val.wires realWire).sig :=
        targetIso.wire_signature realWire
      _ = (backward.target.val.wires
          (backward.wireEquiv realWire)).sig :=
        (backward.wireEquiv_retained_signature realWire head).symm

/-- Complete wire-scope law for the transported inverse carrier. -/
theorem inverseTransport_wire_scope
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).scope =
      forward.inverseTransportRegionEquiv backward targetIso
        (backward.target.val.wires targetWire).scope := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head]
    have backwardScope := backward.result.targetWire_scope_regionImage
    change (backward.target.val.wires backward.targetWire).scope =
        backward.result.regionImage
          (real.val.wires backwardWire).scope at backwardScope
    have forwardScope := forward.result.targetWire_scope_regionImage
    change (forward.target.val.wires forward.targetWire).scope =
        forward.result.regionImage
          (planned.val.wires forwardWire).scope at forwardScope
    have middleScope := targetIso.wire_scope backwardWire
    rw [wireExact] at middleScope
    unfold inverseTransportRegionEquiv
    rw [backwardScope, backward.result.regionImage_exact]
    have backwardCancel := backward.result.regionEquiv.left_inv
      (real.val.wires backwardWire).scope
    change backward.result.regionEquiv.invFun
        (backward.result.regionEquiv
          (real.val.wires backwardWire).scope) =
      (real.val.wires backwardWire).scope at backwardCancel
    calc
      (planned.val.wires forwardWire).scope =
          forward.result.regionEquiv.symm
            (forward.result.regionEquiv
              (planned.val.wires forwardWire).scope) :=
        (forward.result.regionEquiv.left_inv _).symm
      _ = forward.result.regionEquiv.symm
          (forward.target.val.wires forward.targetWire).scope := by
        rw [forwardScope, forward.result.regionImage_exact]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions (real.val.wires backwardWire).scope) := by
        rw [middleScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions
            (backward.result.regionEquiv.symm
              (backward.result.regionEquiv
                (real.val.wires backwardWire).scope))) :=
        congrArg (fun value => forward.result.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    have forwardScope := forward.wireEquiv_retained_scope plannedWire
      plannedDifferent
    rw [plannedImage] at forwardScope
    have backwardScope := backward.wireEquiv_retained_scope realWire head
    have middleScope := targetIso.wire_scope realWire
    unfold inverseTransportRegionEquiv
    rw [backwardScope]
    have backwardCancel := backward.result.regionEquiv.left_inv
      (real.val.wires realWire).scope
    change backward.result.regionEquiv.invFun
        (backward.result.regionEquiv (real.val.wires realWire).scope) =
      (real.val.wires realWire).scope at backwardCancel
    calc
      (planned.val.wires plannedWire).scope =
          forward.result.regionEquiv.symm
            (forward.result.regionEquiv
              (planned.val.wires plannedWire).scope) :=
        (forward.result.regionEquiv.left_inv _).symm
      _ = forward.result.regionEquiv.symm
          (forward.target.val.wires (targetIso.wires realWire)).scope := by
        rw [forwardScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions (real.val.wires realWire).scope) := by
        rw [middleScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions
            (backward.result.regionEquiv.symm
              (backward.result.regionEquiv
                (real.val.wires realWire).scope))) :=
        congrArg (fun value => forward.result.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm

/-- The final inserted argument owner's wire is transported back to the
exact dropped source attachment at the corresponding planned site. -/
theorem inverseTransport_insertedWire
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned forwardOrientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real backwardOrientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (site : Fin backward.result.sites.sites.length) :
    forward.inverseTransportWireEquiv backward targetIso
        (backward.wireEquiv
          (((forward.inverseAttachments targetIso wireExact)[site.val]?).getD
            backwardWire)) =
      ((forward.result.sites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).arguments[position]?).getD forwardWire := by
  rw [forward.inverseTransport_wireEquiv_image]
  rw [forward.inverseAttachments_getD_site targetIso wireExact backward site]
  let sourceAttachment :=
    ((forward.result.sites.sites.get
      (forward.inverseTransportSitePosition backward targetIso
        wireExact site)).arguments[position]?).getD forwardWire
  have middleCancel : targetIso.wires
      (targetIso.wires.symm (forward.transportWire sourceAttachment)) =
        forward.transportWire sourceAttachment :=
    targetIso.wires.right_inv _
  calc
    forward.wireEquiv.symm
        (targetIso.wires
          (targetIso.wires.symm
            (forward.transportWire sourceAttachment))) =
      forward.wireEquiv.symm (forward.transportWire sourceAttachment) :=
        congrArg forward.wireEquiv.symm middleCancel
    _ = forward.wireEquiv.symm (forward.wireEquiv sourceAttachment) := by
      rw [forward.transportWire_eq_wireEquiv]
    _ = sourceAttachment := forward.wireEquiv.left_inv _

end AppliedArgDrop

def applyArgDrop
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation) :
    Except WireArgumentError
      (AppliedArgDrop source orientation wire position) := do
  match accepted : ConcreteWirePrimitive.argDrop source wire position with
  | .error error => throw (.concreteRejected error)
  | .ok result =>
      let attachments :=
        result.sites.sites.filterMap fun site => site.arguments[position]?
      let gate ← Internal.checkDropGate source orientation wire attachments
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => throw .semanticLedgerRejected
      | .rel sourceArguments =>
          let ledger ←
            Internal.optionToExcept .semanticLedgerRejected <|
              ArgumentsSemantics.checkDropLedger result sourceArguments
                sourceSignature position
          let semanticCheck :
              Except WireArgumentError
                (Internal.DropSemanticReceipt (orientation := orientation)
                  (position := position) ledger) :=
            match gate with
            | .uniform _ =>
                match attachments with
                | [] => throw .semanticLedgerRejected
                | attachment :: _ => do
                    let fixed ←
                      Internal.optionToExcept .semanticLedgerRejected <|
                        ArgumentsSemantics.checkFixedDropLedger ledger
                          attachment position
                    pure (Internal.DropSemanticReceipt.uniform fixed)
            | .gated _ polarity =>
                pure (Internal.DropSemanticReceipt.gated polarity)
          let semantics ← semanticCheck
          let sourceRemovedExact :=
            ConcreteWirePrimitive.argDrop_sourceRemovedWires_exact
              source wire position result accepted
          let localCountExact :=
            ConcreteWirePrimitive.argDrop_localCount_exact
              source wire position result accepted
          let targetArgumentsExact :=
            ConcreteWirePrimitive.argDrop_targetArguments_exact source wire
              sourceArguments sourceSignature position result accepted
          let argumentsExact := fun site =>
            ConcreteWirePrimitive.argDrop_arguments_exact source wire
              sourceArguments sourceSignature position result accepted site
          pure
            ⟨attachments, gate, result, sourceArguments, sourceSignature,
              sourceRemovedExact, localCountExact, targetArgumentsExact,
              argumentsExact, ledger, semantics⟩

def applyArgExtend
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (orientation : Orientation) :
    Except WireArgumentError
      (AppliedArgExtend source orientation wire position newArgument
        attachments) := do
  match accepted : ConcreteWirePrimitive.argExtend source wire position
      newArgument attachments with
  | .error error => throw (.concreteRejected error)
  | .ok result =>
      let gate ← Internal.checkExtendGate source orientation wire attachments
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => throw .semanticLedgerRejected
      | .rel sourceArguments =>
          let ledger ←
            Internal.optionToExcept .semanticLedgerRejected <|
              ArgumentsSemantics.checkExtendLedger result sourceArguments
                sourceSignature position
          let semanticCheck :
              Except WireArgumentError
                (Internal.ExtendSemanticReceipt (orientation := orientation)
                  (position := position) ledger) :=
            match gate with
            | .uniform _ =>
                match attachments with
                | [] => throw .semanticLedgerRejected
                | attachment :: _ => do
                    let fixed ←
                      Internal.optionToExcept .semanticLedgerRejected <|
                        ArgumentsSemantics.checkFixedExtendLedger ledger
                          attachment position
                    pure (Internal.ExtendSemanticReceipt.uniform fixed)
            | .gated _ polarity =>
                pure (Internal.ExtendSemanticReceipt.gated polarity)
          let semantics ← semanticCheck
          let sourceRemovedExact :=
            ConcreteWirePrimitive.argExtend_sourceRemovedWires_exact
              source wire position newArgument attachments result accepted
          let localCountExact :=
            ConcreteWirePrimitive.argExtend_localCount_exact
              source wire position newArgument attachments result accepted
          let targetArgumentsExact :=
            ConcreteWirePrimitive.argExtend_targetArguments_exact source wire
              sourceArguments sourceSignature position newArgument attachments
              result accepted
          let positionValid :=
            ConcreteWirePrimitive.argExtend_position_valid source wire
              sourceArguments sourceSignature position newArgument attachments
              result accepted
          let argumentsExact := fun site =>
            ConcreteWirePrimitive.argExtend_arguments_exact source wire
              sourceArguments sourceSignature position newArgument attachments
              result accepted site
          pure
            ⟨gate, result, sourceArguments, sourceSignature,
              sourceRemovedExact, localCountExact, targetArgumentsExact,
              positionValid, argumentsExact, ledger, semantics⟩

/-- Checked arity shift is a full-model cylindrification equivalence. -/

theorem arg_drop_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (applied : AppliedArgDrop source orientation wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  cases applied.semantics with
  | uniform fixed =>
      cases orientation with
      | forward =>
          exact (fixed.denotes model definitionEnv).mp
      | backward =>
          exact (fixed.denotes model definitionEnv).mpr
  | gated polarity =>
      have compiledExact :
          polarity.compiled =
            applied.ledger.factorization.sourceScope :=
        SiteCompilation.unique polarity.compiled
          applied.ledger.factorization.sourceScope
      cases orientation with
      | forward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 1 :=
            of_decide_eq_true (by
              simpa [Internal.joinPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).2 legal
      | backward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 0 :=
            of_decide_eq_true (by
              simpa [Internal.joinPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).1 legal

/--
Checked argument extension is either an ungated fixed-parameter equivalence
or the sever-family implication selected by orientation and cut parity.
-/
theorem arg_extend_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (orientation : Orientation)
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  cases applied.semantics with
  | uniform fixed =>
      cases orientation with
      | forward =>
          exact (fixed.denotes model definitionEnv).mp
      | backward =>
          exact (fixed.denotes model definitionEnv).mpr
  | gated polarity =>
      have compiledExact :
          polarity.compiled =
            applied.ledger.factorization.sourceScope :=
        SiteCompilation.unique polarity.compiled
          applied.ledger.factorization.sourceScope
      cases orientation with
      | forward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 0 :=
            of_decide_eq_true (by
              simpa [Internal.severPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).1 legal
      | backward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 1 :=
            of_decide_eq_true (by
              simpa [Internal.severPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).2 legal

end Arguments

end WirePrimitive

end VisualProof
