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

end AppliedArgDrop

end Arguments

end WirePrimitive

end VisualProof
