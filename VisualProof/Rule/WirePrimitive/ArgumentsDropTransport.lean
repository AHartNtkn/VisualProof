import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace Arguments

namespace AppliedArgDrop

/-- Pair-specific endpoint transport. Rebuilt application nodes are related
directly in their restored argument coordinate; retained nodes compose the
unchanged construction transports with the supplied suffix isomorphism. -/
def inverseTransportEndpointMap
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount) :
    CEndpoint planned.val.nodeCount :=
  let realNode := backward.nodeEquiv.symm endpoint.node
  if generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites then
    ⟨forward.inverseTransportNodeEquiv backward targetIso endpoint.node,
      endpoint.port⟩
  else
    let realWire := backward.wireEquiv.symm targetWire
    let middleEndpoint := targetIso.endpointMap realWire
      ⟨realNode, endpoint.port⟩
    ⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩

/-- Inverse of the pair-specific endpoint transport. -/
def inverseTransportEndpointInverse
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint planned.val.nodeCount) :
    CEndpoint backward.target.val.nodeCount :=
  if generated : endpoint.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites then
    ⟨(forward.inverseTransportNodeEquiv backward targetIso).symm
        endpoint.node, endpoint.port⟩
  else
    let realWire := backward.wireEquiv.symm targetWire
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨forward.nodeEquiv endpoint.node, endpoint.port⟩
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    ⟨backward.nodeEquiv realEndpoint.node, realEndpoint.port⟩

/-- On retained nodes, the pair transport is exactly suffix composition and
therefore preserves incidence without any argument-coordinate case. -/
theorem inverseTransportEndpointMap_mem_retained
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints)
    (retained : backward.nodeEquiv.symm endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites) :
    forward.inverseTransportEndpointMap backward targetIso targetWire endpoint
        ∈ (planned.val.wires
          (forward.inverseTransportWireEquiv backward targetIso
            targetWire)).endpoints := by
  let realWire := backward.wireEquiv.symm targetWire
  have backwardWireExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  have realMember :
      (⟨backward.nodeEquiv.symm endpoint.node, endpoint.port⟩ :
        CEndpoint real.val.nodeCount) ∈
        (real.val.wires realWire).endpoints := by
    apply backward.retainedEndpointInverse_mem realWire endpoint
    · simpa [backwardWireExact] using member
    · exact retained
  let realEndpoint : CEndpoint real.val.nodeCount :=
    ⟨backward.nodeEquiv.symm endpoint.node, endpoint.port⟩
  let middleEndpoint := targetIso.endpointMap realWire realEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires (targetIso.wires realWire)).endpoints :=
    targetIso.endpointMap_mem realWire realEndpoint realMember
  have middleRetained : middleEndpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    have retainedImage := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact
        (backward.nodeEquiv.symm endpoint.node) retained
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    intro generated
    apply retainedImage
    rw [← corresponds.1]
    exact generated
  let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
  have plannedMember :
      (⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩ :
        CEndpoint planned.val.nodeCount) ∈
        (planned.val.wires plannedWire).endpoints := by
    apply forward.retainedEndpointInverse_mem plannedWire middleEndpoint
    · have forwardWireExact : forward.wireEquiv plannedWire =
          targetIso.wires realWire := forward.wireEquiv.right_inv _
      simpa [forwardWireExact] using middleMember
    · intro plannedGenerated
      have generatedImage := forward.nodeEquiv_generated_mem
        (forward.nodeEquiv.symm middleEndpoint.node) plannedGenerated
      apply middleRetained
      exact Eq.mp (congrArg
        (fun node => node ∈
          ConcreteWirePrimitive.argumentSiteNodes forward.targetSites)
        (forward.nodeEquiv.right_inv middleEndpoint.node)) generatedImage
  have endpointExact :
      forward.inverseTransportEndpointMap backward targetIso targetWire
          endpoint =
        (⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩ :
          CEndpoint planned.val.nodeCount) := by
    unfold inverseTransportEndpointMap
    rw [dif_neg retained]
  have wireCarrierExact :
      forward.inverseTransportWireEquiv backward targetIso targetWire =
        plannedWire := rfl
  rw [endpointExact, wireCarrierExact]
  exact plannedMember

/-- The endpoint introduced only by the inverse extension maps directly to
the construction-owned endpoint erased by the forward drop. -/
theorem inverseTransportEndpointMap_inserted
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (site : Fin backward.sourceSites.sites.length) :
    let attachment :=
      ((forward.inverseAttachments targetIso wireExact)[site.val]?).getD
        backwardWire
    let targetWire := backward.wireEquiv attachment
    let endpoint : CEndpoint backward.target.val.nodeCount :=
      ⟨backward.targetNode site, .arg position⟩
    forward.inverseTransportEndpointMap backward targetIso targetWire endpoint =
      ⟨(forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node, .arg position⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso targetWire =
      ((forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).arguments[position]?).getD forwardWire := by
  dsimp only
  let realNode := (backward.sourceSites.sites.get site).node
  have generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardNode : backward.nodeEquiv realNode =
      backward.targetNode site := backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.targetNode site) = realNode := by
    rw [← backwardNode]
    exact backward.nodeEquiv.left_inv realNode
  constructor
  · unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm (backward.targetNode site) =
      realNode from backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · exact forward.inverseTransport_insertedWire targetIso wireExact
      backward site

/-- Rebuilt head endpoints map directly to the original planned heads. -/
theorem inverseTransportEndpointMap_head
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.sourceSites.sites.length) :
    forward.inverseTransportEndpointMap backward targetIso
        backward.targetWire ⟨backward.targetNode site, .head⟩ =
      ⟨(forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node, .head⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso
        backward.targetWire = forwardWire := by
  let realNode := (backward.sourceSites.sites.get site).node
  have generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardNode : backward.nodeEquiv realNode =
      backward.targetNode site := backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.targetNode site) = realNode := by
    rw [← backwardNode]
    exact backward.nodeEquiv.left_inv realNode
  constructor
  · unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm (backward.targetNode site) = realNode
      from backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · exact forward.inverseTransportWireEquiv_head backward targetIso
      wireExact

end AppliedArgDrop

end Arguments

end WirePrimitive

end VisualProof
