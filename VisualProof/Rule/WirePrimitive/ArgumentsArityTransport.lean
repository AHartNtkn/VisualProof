import VisualProof.Rule.WirePrimitive.ArgumentsArityCarrierTransport

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

namespace AppliedArityShift

/-- Pair-specific endpoint transport. Generated rebuilt atoms already have
the restored argument vector, while retained nodes compose the two
construction carriers with the supplied suffix isomorphism. -/
def inverseTransportEndpointMap
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount) :
    CEndpoint planned.val.nodeCount :=
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let realNode := backwardNodes.symm endpoint.node
  if generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites then
    ⟨forward.inverseTransportNodeEquiv backward targetIso endpoint.node,
      endpoint.port⟩
  else if head : targetWire = backward.targetWire then
    ⟨forward.inverseTransportNodeEquiv backward targetIso endpoint.node,
      endpoint.port⟩
  else
    let targetRetained : targetWire ∉
        backward.argumentResult.targetRemovedWires := by
      rw [backward.targetRemovedWires_exact]
      intro member
      exact head (List.mem_singleton.mp member)
    let realWire := backward.argumentResult.sourceWireOfRetainedTarget
      targetWire targetRetained
    let middleEndpoint := targetIso.endpointMap realWire
      ⟨realNode, endpoint.port⟩
    ⟨(forward.argumentResult.nodeEquiv forward.targetSites).symm
        middleEndpoint.node,
      middleEndpoint.port⟩

/-- Inverse of the pair-specific arity endpoint transport. -/
def inverseTransportEndpointInverse
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (candidate : CEndpoint planned.val.nodeCount) :
    CEndpoint backward.target.val.nodeCount :=
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  let middleNode := forwardNodes candidate.node
  let realNode := targetIso.nodes.symm middleNode
  if generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites then
    ⟨(backward.argumentResult.nodeEquiv backward.targetSites) realNode,
      candidate.port⟩
  else if head : targetWire = backward.targetWire then
    ⟨(backward.argumentResult.nodeEquiv backward.targetSites) realNode,
      candidate.port⟩
  else
    let targetRetained : targetWire ∉
        backward.argumentResult.targetRemovedWires := by
      rw [backward.targetRemovedWires_exact]
      intro member
      exact head (List.mem_singleton.mp member)
    let realWire := backward.argumentResult.sourceWireOfRetainedTarget
      targetWire targetRetained
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨middleNode, candidate.port⟩
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    ⟨(backward.argumentResult.nodeEquiv backward.targetSites)
        realEndpoint.node,
      realEndpoint.port⟩

/-- On retained nodes the pair endpoint transport is exactly the retained
construction core composed with the suffix isomorphism. -/
theorem inverseTransportEndpointMap_mem_retained
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints)
    (retained :
      (backward.argumentResult.nodeEquiv backward.targetSites).symm
          endpoint.node ∉
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites) :
    forward.inverseTransportEndpointMap backward targetIso wireExact
        targetWire endpoint ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire)).endpoints := by
  have head : targetWire ≠ backward.targetWire := by
    intro same
    subst targetWire
    have incident := member
    rw [← backward.targetSites.exhaustive] at incident
    rcases List.mem_map.mp incident with ⟨site, siteMember, exact⟩
    apply retained
    have nodeExact : endpoint.node = site.node :=
      (congrArg CEndpoint.node exact).symm
    let realNode :=
      (backward.argumentResult.nodeEquiv backward.targetSites).symm
        endpoint.node
    have imageGenerated : site.node ∈
        ConcreteWirePrimitive.argumentSiteNodes backward.targetSites := by
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr ⟨site, siteMember, rfl⟩
    obtain ⟨position, targetExact⟩ :=
      backward.argumentResult.targetSiteNode_generated
        backward.targetSites site.node imageGenerated
    let sourceNode :=
      (backward.sourceSites.sites.get position).node
    have sourceMember : sourceNode ∈
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨backward.sourceSites.sites.get position,
          List.get_mem _ _, rfl⟩
    have sourceImage :
        (backward.argumentResult.nodeEquiv backward.targetSites) sourceNode =
          backward.argumentResult.targetNode position := by
      unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.argumentResult.nodeImage sourceNode = _
      have sourceMemberRaw : sourceNode ∈
          ConcreteWirePrimitive.argumentSiteNodes
            backward.argumentResult.sites := sourceMember
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos sourceMemberRaw]
      change backward.argumentResult.targetNode
        (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          backward.argumentResult.sites
          (backward.argumentResult.sites.sites.get position).node _) = _
      rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
    have targetNodeExact : backward.argumentResult.targetNode position =
        site.node := targetExact.symm
    have inverseExact :
        (backward.argumentResult.nodeEquiv backward.targetSites).symm
          site.node = sourceNode := by
      rw [← targetNodeExact, ← sourceImage]
      exact (backward.argumentResult.nodeEquiv
        backward.targetSites).left_inv sourceNode
    simpa [realNode, nodeExact, inverseExact] using sourceMember
  have targetRetained : targetWire ∉
      backward.argumentResult.targetRemovedWires := by
    rw [backward.targetRemovedWires_exact]
    intro removed
    exact head (List.mem_singleton.mp removed)
  let realWire := backward.argumentResult.sourceWireOfRetainedTarget
    targetWire targetRetained
  have realRetained : realWire ∉
      backward.argumentResult.sourceRemovedWires :=
    backward.argumentResult.sourceRetainedWire_not_removed
      (backward.argumentResult.retainedBaseWireOfTarget targetWire
        targetRetained)
  have backwardImage :
      backward.argumentResult.retainedWireImage realWire realRetained =
        targetWire :=
    backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
      targetWire targetRetained
  let realEndpoint : CEndpoint real.val.nodeCount :=
    ⟨(backward.argumentResult.nodeEquiv backward.targetSites).symm
      endpoint.node, endpoint.port⟩
  have realMember : realEndpoint ∈
      (real.val.wires realWire).endpoints := by
    apply argumentResult_retainedEndpointInverse_mem
      backward.argumentResult backward.targetSites realWire realRetained
    · simpa [backwardImage] using member
    · exact retained
  let middleEndpoint := targetIso.endpointMap realWire realEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires (targetIso.wires realWire)).endpoints :=
    targetIso.endpointMap_mem realWire realEndpoint realMember
  have middleNodeRetained : middleEndpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    have retainedImage := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact realEndpoint.node retained
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    intro generated
    apply retainedImage
    rw [← corresponds.1]
    exact generated
  let middleWire := targetIso.wires realWire
  have middleWireRetained : middleWire ∉
      forward.argumentResult.targetRemovedWires := by
    intro removed
    exact realRetained
      ((forward.inverseTransport_removedWire_iff backward targetIso
        wireExact realWire).mpr removed)
  let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
    middleWire middleWireRetained
  have plannedRetained : plannedWire ∉
      forward.argumentResult.sourceRemovedWires :=
      forward.argumentResult.sourceRetainedWire_not_removed
      (forward.argumentResult.retainedBaseWireOfTarget middleWire
        middleWireRetained)
  have forwardImage :
      forward.argumentResult.retainedWireImage plannedWire plannedRetained =
        middleWire :=
    forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
      middleWire middleWireRetained
  have plannedNodeRetained :
      (forward.argumentResult.nodeEquiv forward.targetSites).symm
          middleEndpoint.node ∉
        ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
    intro generated
    apply middleNodeRetained
    let position :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
        forward.sourceSites _ generated
    have sourceExact :
        (forward.sourceSites.sites.get position).node =
          (forward.argumentResult.nodeEquiv forward.targetSites).symm
            middleEndpoint.node :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
        forward.sourceSites _ generated
    have sourceMember :
        (forward.sourceSites.sites.get position).node ∈
          ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨forward.sourceSites.sites.get position,
          List.get_mem _ _, rfl⟩
    have imageExact :
        (forward.argumentResult.nodeEquiv forward.targetSites)
            (forward.sourceSites.sites.get position).node =
          forward.argumentResult.targetNode position := by
      unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change forward.argumentResult.nodeImage
        (forward.sourceSites.sites.get position).node = _
      have sourceMemberRaw :
          (forward.sourceSites.sites.get position).node ∈
            ConcreteWirePrimitive.argumentSiteNodes
              forward.argumentResult.sites := sourceMember
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos sourceMemberRaw]
      change forward.argumentResult.targetNode
          (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
            forward.argumentResult.sites
            (forward.argumentResult.sites.sites.get position).node _) = _
      rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
    have targetGenerated :=
      forward.argumentResult.generatedNode_targetSiteNode
        forward.targetSites position
    rw [sourceExact] at imageExact
    have recovered := (forward.argumentResult.nodeEquiv
      forward.targetSites).right_inv middleEndpoint.node
    have targetMiddleExact : forward.argumentResult.targetNode position =
        middleEndpoint.node := imageExact.symm.trans recovered
    rw [← targetMiddleExact]
    exact targetGenerated
  have plannedMember :
      (⟨(forward.argumentResult.nodeEquiv forward.targetSites).symm
          middleEndpoint.node, middleEndpoint.port⟩ :
        CEndpoint planned.val.nodeCount) ∈
        (planned.val.wires plannedWire).endpoints := by
    apply argumentResult_retainedEndpointInverse_mem
      forward.argumentResult forward.targetSites plannedWire plannedRetained
    · simpa [forwardImage] using middleMember
    · exact plannedNodeRetained
  have endpointExact :
      forward.inverseTransportEndpointMap backward targetIso wireExact
          targetWire endpoint =
        ⟨(forward.argumentResult.nodeEquiv forward.targetSites).symm
          middleEndpoint.node, middleEndpoint.port⟩ := by
    unfold inverseTransportEndpointMap
    rw [dif_neg retained, dif_neg head]
  have carrierExact :
      forward.inverseTransportWireEquiv backward targetIso wireExact
        targetWire = plannedWire := by
    change forward.inverseTransportWireMap backward targetIso wireExact
      targetWire = plannedWire
    unfold inverseTransportWireMap
    rw [dif_neg head]
  rw [endpointExact, carrierExact]
  exact plannedMember

/-- Rebuilt unshift heads map directly to their exact planned source heads. -/
theorem inverseTransportEndpointMap_head
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.sourceSites.sites.length) :
    forward.inverseTransportEndpointMap backward targetIso wireExact
        backward.targetWire
        ⟨backward.argumentResult.targetNode site, .head⟩ =
      ⟨(forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node, .head⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso wireExact
        backward.targetWire = forwardWire := by
  let realNode := (backward.sourceSites.sites.get site).node
  have generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage :
      backward.argumentResult.nodeEquiv backward.targetSites realNode =
        backward.argumentResult.targetNode site := by
    unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.argumentResult.nodeImage realNode = _
    have generatedRaw : realNode ∈
        ConcreteWirePrimitive.argumentSiteNodes
          backward.argumentResult.sites := generated
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos generatedRaw]
    change backward.argumentResult.targetNode
      (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
        backward.argumentResult.sites
        (backward.argumentResult.sites.sites.get site).node _) = _
    rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse :
      (backward.argumentResult.nodeEquiv backward.targetSites).symm
          (backward.argumentResult.targetNode site) = realNode := by
    rw [← backwardImage]
    exact (backward.argumentResult.nodeEquiv
      backward.targetSites).left_inv realNode
  constructor
  · simp only [inverseTransportEndpointMap]
    rw [backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · change forward.inverseTransportWireMap backward targetIso wireExact
      backward.targetWire = forwardWire
    simp [inverseTransportWireMap]

/-- Every retained rebuilt argument coordinate maps to the exact planned
attachment at the same coordinate. -/
theorem inverseTransportEndpointMap_argument
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.sourceSites.sites.length)
    (index : Nat)
    (indexBound : index < backward.argumentResult.targetArguments.length) :
    let realSite := backward.sourceSites.sites.get site
    let realAttachment := realSite.arguments[index]'
      (by
        have sourceArgs := forward.inverseSourceArguments_exact backward
          targetIso wireExact
        have siteLength := realSite.arguments_length.trans
          (congrArg List.length
            (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
              backward.sourceArgumentList backward.sourceWire_signature
              realSite))
        rw [backward.targetArguments_exact,
          sourceArgs, Internal.eraseAt_append_last] at indexBound
        rw [siteLength, sourceArgs]
        simp
        omega)
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    let plannedAttachment := plannedSite.arguments[index]'
      (by
        have plannedLength := plannedSite.arguments_length.trans
          (congrArg List.length
            (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
              forward.sourceArgumentList forward.sourceWire_signature
              plannedSite))
        rw [plannedLength]
        have restored := forward.inverseTargetArguments_exact backward
          targetIso wireExact
        rw [← restored]
        exact indexBound)
    let targetAttachment :=
      backward.argumentResult.contextWireMap realAttachment
    forward.inverseTransportEndpointMap backward targetIso wireExact
        targetAttachment
        ⟨backward.argumentResult.targetNode site, .arg index⟩ =
      ⟨plannedSite.node, .arg index⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso wireExact
        targetAttachment = plannedAttachment ∧
    backward.target.val.endpointOwner?
        ⟨backward.argumentResult.targetNode site, .arg index⟩ =
      some targetAttachment := by
  dsimp only
  let realSite := backward.sourceSites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.sourceSites.sites.get plannedPosition
  have restored := forward.inverseTargetArguments_exact backward targetIso
    wireExact
  have plannedLength : plannedSite.arguments.length =
      forward.sourceArgumentList.length :=
    plannedSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          forward.sourceArgumentList forward.sourceWire_signature plannedSite))
  have plannedBound : index < plannedSite.arguments.length := by
    rw [plannedLength, ← restored]
    omega
  let plannedAttachment := plannedSite.arguments[index]'plannedBound
  have sourceArgs := forward.inverseSourceArguments_exact backward targetIso
    wireExact
  have realLength : realSite.arguments.length =
      backward.sourceArgumentList.length :=
    realSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          backward.sourceArgumentList backward.sourceWire_signature realSite))
  have realBound : index < realSite.arguments.length := by
    rw [backward.targetArguments_exact, sourceArgs,
      Internal.eraseAt_append_last] at indexBound
    rw [realLength, sourceArgs]
    simp
    omega
  let realAttachment := realSite.arguments[index]'realBound
  have realRetained : realAttachment ∉
      backward.argumentResult.sourceRemovedWires := by
    intro removed
    change realAttachment ∈
      backwardWire :: backward.argumentResult.spec.removedWires at removed
    rcases List.mem_cons.mp removed with head | removedLocal
    · exact realSite.argument_ne_head index realBound head
    · rcases backward.removedLocal_exact realAttachment removedLocal with
        ⟨_localSite, _localMember, endpointsExact⟩
      have owner := realSite.argument_owner index realBound
      have incident := ConcreteDiagram.endpointOwner?_incident real.val
        ⟨realSite.node, .arg index⟩ realAttachment owner
      rw [endpointsExact] at incident
      have endpointExact := List.mem_singleton.mp incident
      have portExact := congrArg CEndpoint.port endpointExact
      simp only at portExact
      have before : index < forward.sourceArgumentList.length := by
        rw [plannedLength] at plannedBound
        exact plannedBound
      have indexExact : index = forward.sourceArgumentList.length := by
        injection portExact
      exact (Nat.ne_of_lt before) indexExact
  let targetAttachment :=
    backward.argumentResult.contextWireMap realAttachment
  have targetAttachmentExact : targetAttachment =
      backward.argumentResult.retainedWireImage realAttachment realRetained :=
    backward.argumentResult.contextWireMap_retained realAttachment
      realRetained
  have targetRetained :=
    backward.argumentResult.retainedWireImage_not_targetRemoved
      realAttachment realRetained
  have targetAttachmentRetained : targetAttachment ∉
      backward.argumentResult.targetRemovedWires := by
    rw [targetAttachmentExact]
    exact targetRetained
  have targetDifferent : targetAttachment ≠ backward.targetWire := by
    intro same
    apply targetRetained
    rw [backward.targetRemovedWires_exact]
    exact List.mem_singleton.mpr (targetAttachmentExact.symm.trans same)
  have erasedSelected :
      (ConcreteWirePrimitive.eraseAt realSite.arguments
        forward.sourceArgumentList.length)[index]? =
        some realAttachment := by
    rw [Internal.eraseAt_getElem?_before]
    · simp [realAttachment, realBound]
    · rw [plannedLength] at plannedBound
      exact plannedBound
  have selected :
      (backward.argumentResult.spec.arguments site)[index]? =
        some (.existing realAttachment) := by
    rw [backward.siteArguments_exact site]
    unfold existingReferences
    rw [List.getElem?_map, erasedSelected]
    rfl
  have backwardOwner :=
    backward.argumentResult.generatedArgument_endpointOwner site index
      indexBound realAttachment selected realRetained
  rw [← targetAttachmentExact] at backwardOwner
  have realOwner := realSite.argument_owner index realBound
  have middleOwner := targetIso.atom_owner_forward real.property
    forward.target.property realSite.node_data realOwner
  have middleNode := forward.inverseTransport_middleNode backward targetIso
    wireExact site
  change targetIso.nodes realSite.node =
    forward.argumentResult.targetNode plannedPosition at middleNode
  rw [middleNode] at middleOwner
  have forwardOwner := forward.targetNode_existing_owner plannedPosition
    index plannedBound
  have middleWire : targetIso.wires realAttachment =
      forward.argumentResult.retainedWireImage plannedAttachment (by
        rw [forward.sourceRemovedWires_exact]
        simpa [plannedAttachment] using
          plannedSite.argument_ne_head index plannedBound) := by
    simpa [plannedAttachment] using
      Option.some.inj (middleOwner.symm.trans forwardOwner)
  have generated : realSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr ⟨realSite, List.get_mem _ _, rfl⟩
  have backwardImage :
      (backward.argumentResult.nodeEquiv backward.targetSites) realSite.node =
        backward.argumentResult.targetNode site := by
    unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.argumentResult.nodeImage realSite.node = _
    have generatedRaw : realSite.node ∈
        ConcreteWirePrimitive.argumentSiteNodes
          backward.argumentResult.sites := generated
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos generatedRaw]
    change backward.argumentResult.targetNode
      (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
        backward.argumentResult.sites
        (backward.argumentResult.sites.sites.get site).node _) = _
    rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse :
      (backward.argumentResult.nodeEquiv backward.targetSites).symm
          (backward.argumentResult.targetNode site) = realSite.node := by
    rw [← backwardImage]
    exact (backward.argumentResult.nodeEquiv
      backward.targetSites).left_inv realSite.node
  constructor
  · simp only [inverseTransportEndpointMap]
    rw [backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · constructor
    · change forward.inverseTransportWireMap backward targetIso wireExact
        targetAttachment = plannedAttachment
      unfold inverseTransportWireMap
      split
      next same => exact (targetDifferent same).elim
      next notHead =>
        have backwardRoundTrip :=
          backward.argumentResult.sourceWireOfRetainedTarget_retainedWireImage
            realAttachment realRetained targetRetained
        have plannedRetained : plannedAttachment ∉
            forward.argumentResult.sourceRemovedWires := by
          rw [forward.sourceRemovedWires_exact]
          simpa [plannedAttachment] using
            plannedSite.argument_ne_head index plannedBound
        have middleTargetRetained :=
          forward.argumentResult.retainedWireImage_not_targetRemoved
            plannedAttachment plannedRetained
        have forwardRoundTrip :=
          forward.argumentResult.sourceWireOfRetainedTarget_retainedWireImage
            plannedAttachment plannedRetained middleTargetRetained
        have backwardRoundTripPublic :
            backward.argumentResult.sourceWireOfRetainedTarget
                targetAttachment targetAttachmentRetained =
              realAttachment := by
          exact (backward.argumentResult.sourceWireOfRetainedTarget_congr
            targetAttachment
            (backward.argumentResult.retainedWireImage realAttachment
              realRetained) targetAttachmentRetained targetRetained
              targetAttachmentExact).trans
                backwardRoundTrip
        let recoveredReal :=
          backward.argumentResult.sourceWireOfRetainedTarget
            targetAttachment targetAttachmentRetained
        have recoveredRealRetained : recoveredReal ∉
            backward.argumentResult.sourceRemovedWires :=
          backward.argumentResult.sourceRetainedWire_not_removed
            (backward.argumentResult.retainedBaseWireOfTarget
              targetAttachment targetAttachmentRetained)
        have recoveredMiddleRetained : targetIso.wires recoveredReal ∉
            forward.argumentResult.targetRemovedWires := by
          intro removed
          exact recoveredRealRetained
            ((forward.inverseTransport_removedWire_iff backward targetIso
              wireExact recoveredReal).mpr removed)
        have recoveredMiddleExact : targetIso.wires recoveredReal =
            forward.argumentResult.retainedWireImage plannedAttachment
              plannedRetained := by
          calc
            targetIso.wires recoveredReal =
                targetIso.wires realAttachment :=
              congrArg targetIso.wires backwardRoundTripPublic
            _ = _ := middleWire
        change forward.argumentResult.sourceWireOfRetainedTarget
            (targetIso.wires recoveredReal) recoveredMiddleRetained =
          plannedAttachment
        exact (forward.argumentResult.sourceWireOfRetainedTarget_congr
          (targetIso.wires recoveredReal)
          (forward.argumentResult.retainedWireImage plannedAttachment
            plannedRetained) recoveredMiddleRetained middleTargetRetained
              recoveredMiddleExact).trans forwardRoundTrip
    · exact backwardOwner

/-- The pair endpoint map preserves incidence on every rebuilt unshift
target wire. -/
theorem inverseTransportEndpointMap_mem
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    forward.inverseTransportEndpointMap backward targetIso wireExact
        targetWire endpoint ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire)).endpoints := by
  rcases endpoint with ⟨targetNode, port⟩
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let realNode := backwardNodes.symm targetNode
  by_cases retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · exact forward.inverseTransportEndpointMap_mem_retained backward
      targetIso wireExact targetWire ⟨targetNode, port⟩ member retained
  · have generated : realNode ∈
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites :=
      Classical.not_not.mp retained
    let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.sourceSites realNode generated
    let realSite := backward.sourceSites.sites.get site
    have siteNode : realSite.node = realNode :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
        backward.sourceSites realNode generated
    have imageExact : backwardNodes realNode =
        backward.argumentResult.targetNode site := by
      unfold backwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.argumentResult.nodeImage realNode = _
      have generatedRaw : realNode ∈
          ConcreteWirePrimitive.argumentSiteNodes
            backward.argumentResult.sites := generated
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos generatedRaw]
      rfl
    have recover : backwardNodes realNode = targetNode :=
      backwardNodes.right_inv targetNode
    have targetNodeExact : targetNode =
        backward.argumentResult.targetNode site :=
      recover.symm.trans imageExact
    rw [targetNodeExact] at member ⊢
    have required : port ∈ backward.target.val.requiredPorts
        (backward.argumentResult.targetNode site) :=
      ConcreteDiagram.incident_port_required definitions backward.target.val
        backward.target.property targetWire
          ⟨backward.argumentResult.targetNode site, port⟩ member
    have actualOwner : backward.target.val.endpointOwner?
        ⟨backward.argumentResult.targetNode site, port⟩ =
          some targetWire :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        backward.target.val backward.target.property
        (backward.argumentResult.targetNode site) port required targetWire
          member
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    cases port with
    | head =>
        have generatedOwner :=
          backward.argumentResult.targetNode_head_owner site
        have targetWireExact : targetWire = backward.targetWire :=
          Option.some.inj (actualOwner.symm.trans generatedOwner)
        subst targetWire
        have transported := forward.inverseTransportEndpointMap_head backward
          targetIso wireExact site
        rw [transported.1, transported.2]
        exact ConcreteDiagram.endpointOwner?_incident planned.val
          ⟨plannedSite.node, .head⟩ forwardWire plannedSite.endpoint_owner
    | arg index =>
        have targetData := backward.argumentResult.targetNode_data site
        have targetDataPublic : backward.target.val.nodes
            (backward.argumentResult.targetNode site) =
          .atom (backward.argumentResult.regionImage realSite.region)
            backward.argumentResult.targetArguments := targetData
        have indexBound : index <
            backward.argumentResult.targetArguments.length := by
          rw [ConcreteDiagram.requiredPorts, targetDataPublic] at required
          simpa using required
        have transported := forward.inverseTransportEndpointMap_argument
          backward targetIso wireExact site index indexBound
        let realAttachment := realSite.arguments[index]'
          (by
            have sourceArgs := forward.inverseSourceArguments_exact backward
              targetIso wireExact
            have realLength := realSite.arguments_length.trans
              (congrArg List.length
                (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                  backward.sourceArgumentList backward.sourceWire_signature
                  realSite))
            have restored := forward.inverseTargetArguments_exact backward
              targetIso wireExact
            rw [realLength, sourceArgs]
            simp
            rw [← restored]
            omega)
        let targetAttachment :=
          backward.argumentResult.contextWireMap realAttachment
        have targetWireExact : targetWire = targetAttachment :=
          Option.some.inj (actualOwner.symm.trans transported.2.2)
        subst targetWire
        rw [transported.1, transported.2.1]
        have plannedLength : plannedSite.arguments.length =
            forward.sourceArgumentList.length :=
          plannedSite.arguments_length.trans
            (congrArg List.length
              (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                forward.sourceArgumentList forward.sourceWire_signature
                plannedSite))
        have restored := forward.inverseTargetArguments_exact backward
          targetIso wireExact
        have plannedBound : index < plannedSite.arguments.length := by
          rw [plannedLength, ← restored]
          exact indexBound
        exact ConcreteDiagram.endpointOwner?_incident planned.val
          ⟨plannedSite.node, .arg index⟩
          (plannedSite.arguments[index]'plannedBound)
          (plannedSite.argument_owner index plannedBound)
    | identity index =>
        have targetData := backward.argumentResult.targetNode_data site
        have targetDataPublic : backward.target.val.nodes
            (backward.argumentResult.targetNode site) =
          .atom (backward.argumentResult.regionImage realSite.region)
            backward.argumentResult.targetArguments := targetData
        rw [ConcreteDiagram.requiredPorts, targetDataPublic] at required
        simp at required

/-- The pair endpoint inverse preserves incidence on every planned wire. -/
theorem inverseTransportEndpointInverse_mem
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (candidate : CEndpoint planned.val.nodeCount)
    (member : candidate ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire)).endpoints) :
    forward.inverseTransportEndpointInverse backward targetIso wireExact
        targetWire candidate ∈
      (backward.target.val.wires targetWire).endpoints := by
  rcases candidate with ⟨plannedNode, port⟩
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let middleNode := forwardNodes plannedNode
  let realNode := targetIso.nodes.symm middleNode
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.sourceSites realNode generated
    let realSite := backward.sourceSites.sites.get site
    have siteNode : realSite.node = realNode :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
        backward.sourceSites realNode generated
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    have realRecover : targetIso.nodes realNode = middleNode :=
      targetIso.nodes.right_inv middleNode
    have mappedMiddle := forward.inverseTransport_middleNode backward
      targetIso wireExact site
    change targetIso.nodes realSite.node =
      forward.argumentResult.targetNode plannedPosition at mappedMiddle
    rw [siteNode, realRecover] at mappedMiddle
    have plannedMember : plannedSite.node ∈
        ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨plannedSite, List.get_mem _ _, rfl⟩
    have plannedImage : forwardNodes plannedSite.node =
        forward.argumentResult.targetNode plannedPosition := by
      unfold forwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change forward.argumentResult.nodeImage plannedSite.node = _
      have plannedMemberRaw : plannedSite.node ∈
          ConcreteWirePrimitive.argumentSiteNodes
            forward.argumentResult.sites := plannedMember
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos plannedMemberRaw]
      change forward.argumentResult.targetNode
        (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          forward.argumentResult.sites
          (forward.argumentResult.sites.sites.get plannedPosition).node _) = _
      rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
    have plannedNodeExact : plannedNode = plannedSite.node := by
      apply forwardNodes.injective
      exact mappedMiddle.trans plannedImage.symm
    rw [plannedNodeExact] at member ⊢
    have required : port ∈ planned.val.requiredPorts plannedSite.node :=
      ConcreteDiagram.incident_port_required definitions planned.val
        planned.property
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire) ⟨plannedSite.node, port⟩ member
    have actualOwner : planned.val.endpointOwner?
        ⟨plannedSite.node, port⟩ =
          some (forward.inverseTransportWireEquiv backward targetIso
            wireExact targetWire) :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions planned.val
        planned.property plannedSite.node port required
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire) member
    have inverseExact :
        forward.inverseTransportEndpointInverse backward targetIso wireExact
            targetWire ⟨plannedSite.node, port⟩ =
          ⟨backward.argumentResult.targetNode site, port⟩ := by
      simp only [inverseTransportEndpointInverse]
      have inverseReal : targetIso.nodes.symm
          (forwardNodes plannedSite.node) = realNode := by
        unfold realNode middleNode
        exact congrArg (fun node => targetIso.nodes.symm
          (forwardNodes node)) plannedNodeExact.symm
      rw [inverseReal, dif_pos generated, ← siteNode]
      congr 1
      unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.argumentResult.nodeImage realSite.node = _
      have generatedRaw : realSite.node ∈
          ConcreteWirePrimitive.argumentSiteNodes
            backward.argumentResult.sites := by simpa [siteNode] using generated
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos generatedRaw]
      change backward.argumentResult.targetNode
        (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          backward.argumentResult.sites
          (backward.argumentResult.sites.sites.get site).node _) = _
      rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
    rw [inverseExact]
    cases port with
    | head =>
        have plannedOwner := plannedSite.endpoint_owner
        have carrierHead :
            forward.inverseTransportWireEquiv backward targetIso wireExact
                targetWire = forwardWire :=
          Option.some.inj (actualOwner.symm.trans plannedOwner)
        have transported := forward.inverseTransportEndpointMap_head backward
          targetIso wireExact site
        have targetWireExact : targetWire = backward.targetWire := by
          apply (forward.inverseTransportWireEquiv backward targetIso
            wireExact).injective
          rw [carrierHead, transported.2]
        rw [targetWireExact]
        exact ConcreteDiagram.endpointOwner?_incident backward.target.val
          ⟨backward.argumentResult.targetNode site, .head⟩
          backward.targetWire
          (backward.argumentResult.targetNode_head_owner site)
    | arg index =>
        have plannedBound : index < plannedSite.arguments.length := by
          simpa [ConcreteDiagram.requiredPorts, plannedSite.node_data,
            plannedSite.arguments_length] using required
        have plannedOwner := plannedSite.argument_owner index plannedBound
        have carrierArgument :
            forward.inverseTransportWireEquiv backward targetIso wireExact
                targetWire = plannedSite.arguments[index]'plannedBound :=
          Option.some.inj (actualOwner.symm.trans plannedOwner)
        have restored := forward.inverseTargetArguments_exact backward
          targetIso wireExact
        have plannedLength : plannedSite.arguments.length =
            forward.sourceArgumentList.length :=
          plannedSite.arguments_length.trans
            (congrArg List.length
              (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                forward.sourceArgumentList forward.sourceWire_signature
                plannedSite))
        have indexBound : index <
            backward.argumentResult.targetArguments.length := by
          rw [restored, ← plannedLength]
          exact plannedBound
        have transported := forward.inverseTransportEndpointMap_argument
          backward targetIso wireExact site index indexBound
        let realAttachment := realSite.arguments[index]'
          (by
            have sourceArgs := forward.inverseSourceArguments_exact backward
              targetIso wireExact
            have realLength := realSite.arguments_length.trans
              (congrArg List.length
                (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                  backward.sourceArgumentList backward.sourceWire_signature
                  realSite))
            rw [realLength, sourceArgs]
            simp
            rw [plannedLength] at plannedBound
            omega)
        let targetAttachment :=
          backward.argumentResult.contextWireMap realAttachment
        have targetWireExact : targetWire = targetAttachment := by
          apply (forward.inverseTransportWireEquiv backward targetIso
            wireExact).injective
          rw [carrierArgument, transported.2.1]
        rw [targetWireExact]
        exact ConcreteDiagram.endpointOwner?_incident backward.target.val
          ⟨backward.argumentResult.targetNode site, .arg index⟩
          targetAttachment transported.2.2
    | identity index =>
        simp [ConcreteDiagram.requiredPorts, plannedSite.node_data] at required
  · have middleRetained := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact realNode generated
    have plannedRetained : plannedNode ∉
        ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
      intro plannedGenerated
      apply middleRetained
      let position :=
        ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          forward.sourceSites plannedNode plannedGenerated
      have sourceExact :
          (forward.sourceSites.sites.get position).node = plannedNode :=
        ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
          forward.sourceSites plannedNode plannedGenerated
      have sourceMember :
          (forward.sourceSites.sites.get position).node ∈
            ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
        unfold ConcreteWirePrimitive.argumentSiteNodes
        exact List.mem_map.mpr
          ⟨forward.sourceSites.sites.get position,
            List.get_mem _ _, rfl⟩
      have imageExact : forwardNodes
          (forward.sourceSites.sites.get position).node =
            forward.argumentResult.targetNode position := by
        unfold forwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
        change forward.argumentResult.nodeImage
          (forward.sourceSites.sites.get position).node = _
        have sourceMemberRaw :
            (forward.sourceSites.sites.get position).node ∈
              ConcreteWirePrimitive.argumentSiteNodes
                forward.argumentResult.sites := sourceMember
        rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
          dif_pos sourceMemberRaw]
        change forward.argumentResult.targetNode
          (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
            forward.argumentResult.sites
            (forward.argumentResult.sites.sites.get position).node _) = _
        rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
      have targetGenerated :=
        forward.argumentResult.generatedNode_targetSiteNode
          forward.targetSites position
      rw [sourceExact] at imageExact
      have realRecover : targetIso.nodes realNode = middleNode :=
        targetIso.nodes.right_inv middleNode
      have targetExact : targetIso.nodes realNode =
          forward.argumentResult.targetNode position :=
        realRecover.trans imageExact
      rw [targetExact]
      exact targetGenerated
    have head : targetWire ≠ backward.targetWire := by
      intro same
      subst targetWire
      have carrierHead :
          forward.inverseTransportWireEquiv backward targetIso wireExact
              backward.targetWire = forwardWire := by
        change forward.inverseTransportWireMap backward targetIso wireExact
          backward.targetWire = forwardWire
        simp [inverseTransportWireMap]
      rw [carrierHead] at member
      have incident := member
      rw [← forward.sourceSites.exhaustive] at incident
      rcases List.mem_map.mp incident with ⟨site, siteMember, endpointExact⟩
      apply plannedRetained
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr ⟨site, siteMember,
        congrArg CEndpoint.node endpointExact⟩
    have targetRetained : targetWire ∉
        backward.argumentResult.targetRemovedWires := by
      rw [backward.targetRemovedWires_exact]
      intro removed
      exact head (List.mem_singleton.mp removed)
    let realWire := backward.argumentResult.sourceWireOfRetainedTarget
      targetWire targetRetained
    have realRetained : realWire ∉
        backward.argumentResult.sourceRemovedWires :=
      backward.argumentResult.sourceRetainedWire_not_removed
        (backward.argumentResult.retainedBaseWireOfTarget targetWire
          targetRetained)
    have backwardImage :
        backward.argumentResult.retainedWireImage realWire realRetained =
          targetWire :=
      backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        targetWire targetRetained
    let middleWire := targetIso.wires realWire
    have middleWireRetained : middleWire ∉
        forward.argumentResult.targetRemovedWires := by
      intro removed
      exact realRetained
        ((forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mpr removed)
    let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
      middleWire middleWireRetained
    have plannedWireRetained : plannedWire ∉
        forward.argumentResult.sourceRemovedWires :=
      forward.argumentResult.sourceRetainedWire_not_removed
        (forward.argumentResult.retainedBaseWireOfTarget middleWire
          middleWireRetained)
    have forwardImage :
        forward.argumentResult.retainedWireImage plannedWire
          plannedWireRetained = middleWire :=
      forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        middleWire middleWireRetained
    have carrierExact :
        forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire = plannedWire := by
      change forward.inverseTransportWireMap backward targetIso wireExact
        targetWire = plannedWire
      unfold inverseTransportWireMap
      rw [dif_neg head]
    rw [carrierExact] at member
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨middleNode, port⟩
    have middleMember : middleEndpoint ∈
        (forward.target.val.wires middleWire).endpoints := by
      have pushed := argumentResult_retainedEndpointImage_mem
        forward.argumentResult forward.targetSites plannedWire
          ⟨plannedNode, port⟩ member plannedRetained
      simpa [forwardImage] using pushed
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    have realMember : realEndpoint ∈
        (real.val.wires realWire).endpoints :=
      targetIso.endpointInverse_mem realWire middleEndpoint middleMember
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    rw [targetIso.endpointMap_right_inv realWire middleEndpoint middleMember]
      at corresponds
    have realEndpointNode : realEndpoint.node = realNode := by
      apply targetIso.nodes.injective
      have realRecover : targetIso.nodes realNode = middleNode :=
        targetIso.nodes.right_inv middleNode
      exact corresponds.1.symm.trans realRecover.symm
    have finalMember := argumentResult_retainedEndpointImage_mem
      backward.argumentResult backward.targetSites realWire realEndpoint
        realMember (by simpa [realEndpointNode] using generated)
    rw [backwardImage] at finalMember
    simp only [inverseTransportEndpointInverse]
    rw [show targetIso.nodes.symm (forwardNodes plannedNode) = realNode
      from rfl, dif_neg generated, dif_neg head]
    exact finalMember

/-- The pair endpoint inverse cancels the map on incident rebuilt
endpoints. -/
theorem inverseTransportEndpointInverse_map
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    forward.inverseTransportEndpointInverse backward targetIso wireExact
        targetWire
        (forward.inverseTransportEndpointMap backward targetIso wireExact
          targetWire endpoint) = endpoint := by
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  let realNode := backwardNodes.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · have backwardRecover : backwardNodes realNode = endpoint.node :=
      backwardNodes.right_inv endpoint.node
    simp only [inverseTransportEndpointMap]
    rw [show backwardNodes.symm endpoint.node = realNode from rfl,
      dif_pos generated]
    simp only [inverseTransportEndpointInverse]
    have forwardRecover : forwardNodes
        (forward.inverseTransportNodeEquiv backward targetIso endpoint.node) =
      targetIso.nodes realNode := by
      unfold inverseTransportNodeEquiv
        ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
      change forwardNodes
          (forwardNodes.symm
            (targetIso.nodes (backwardNodes.symm endpoint.node))) = _
      rw [show backwardNodes.symm endpoint.node = realNode from rfl]
      exact forwardNodes.right_inv _
    have forwardRecoverRaw :
        (forward.argumentResult.nodeEquiv forward.targetSites)
            (forward.inverseTransportNodeEquiv backward targetIso
              endpoint.node) = targetIso.nodes realNode :=
      forwardRecover
    simp only [forwardRecoverRaw]
    have isoRecover : targetIso.nodes.symm (targetIso.nodes realNode) =
        realNode := targetIso.nodes.left_inv realNode
    simp only [isoRecover, dif_pos generated]
    exact Internal.endpoint_eq backwardRecover rfl
  · by_cases head : targetWire = backward.targetWire
    · simp only [inverseTransportEndpointMap]
      rw [show backwardNodes.symm endpoint.node = realNode from rfl,
        dif_neg generated, dif_pos head]
      simp only [inverseTransportEndpointInverse]
      have forwardRecover : forwardNodes
          (forward.inverseTransportNodeEquiv backward targetIso
            endpoint.node) = targetIso.nodes realNode := by
        unfold inverseTransportNodeEquiv
          ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
        change forwardNodes
            (forwardNodes.symm
              (targetIso.nodes (backwardNodes.symm endpoint.node))) = _
        rw [show backwardNodes.symm endpoint.node = realNode from rfl]
        exact forwardNodes.right_inv _
      have forwardRecoverRaw :
          (forward.argumentResult.nodeEquiv forward.targetSites)
              (forward.inverseTransportNodeEquiv backward targetIso
                endpoint.node) = targetIso.nodes realNode :=
        forwardRecover
      simp only [forwardRecoverRaw]
      have isoRecover : targetIso.nodes.symm (targetIso.nodes realNode) =
          realNode := targetIso.nodes.left_inv realNode
      simp only [isoRecover, dif_neg generated, dif_pos head]
      have backwardRecover : backwardNodes realNode = endpoint.node :=
        backwardNodes.right_inv endpoint.node
      exact Internal.endpoint_eq backwardRecover rfl
    · have targetRetained : targetWire ∉
          backward.argumentResult.targetRemovedWires := by
        rw [backward.targetRemovedWires_exact]
        intro removed
        exact head (List.mem_singleton.mp removed)
      let realWire := backward.argumentResult.sourceWireOfRetainedTarget
        targetWire targetRetained
      have realRetained : realWire ∉
          backward.argumentResult.sourceRemovedWires :=
        backward.argumentResult.sourceRetainedWire_not_removed
          (backward.argumentResult.retainedBaseWireOfTarget targetWire
            targetRetained)
      have backwardImage :
          backward.argumentResult.retainedWireImage realWire realRetained =
            targetWire :=
        backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
          targetWire targetRetained
      let realEndpoint : CEndpoint real.val.nodeCount :=
        ⟨realNode, endpoint.port⟩
      have realMember : realEndpoint ∈
          (real.val.wires realWire).endpoints := by
        apply argumentResult_retainedEndpointInverse_mem
          backward.argumentResult backward.targetSites realWire realRetained
        · simpa [backwardImage] using member
        · exact generated
      let middleEndpoint := targetIso.endpointMap realWire realEndpoint
      have middleMember := targetIso.endpointMap_mem realWire realEndpoint
        realMember
      have middleNodeExact : middleEndpoint.node =
          targetIso.nodes realNode :=
        (targetIso.endpointMap_corresponds realWire realEndpoint
          realMember).1
      have mapExact :
          forward.inverseTransportEndpointMap backward targetIso wireExact
              targetWire endpoint =
            ⟨forwardNodes.symm middleEndpoint.node,
              middleEndpoint.port⟩ := by
        simp only [inverseTransportEndpointMap]
        rw [show backwardNodes.symm endpoint.node = realNode from rfl,
          dif_neg generated, dif_neg head]
      have forwardCancelRaw :
          (forward.argumentResult.nodeEquiv forward.targetSites)
              ((forward.argumentResult.nodeEquiv
                forward.targetSites).symm middleEndpoint.node) =
            middleEndpoint.node :=
        (forward.argumentResult.nodeEquiv
          forward.targetSites).right_inv middleEndpoint.node
      have inverseReal : targetIso.nodes.symm
          middleEndpoint.node = realNode := by
        calc
          targetIso.nodes.symm middleEndpoint.node =
              targetIso.nodes.symm (targetIso.nodes realNode) :=
            congrArg targetIso.nodes.symm middleNodeExact
          _ = realNode := targetIso.nodes.left_inv realNode
      have targetCancel := targetIso.endpointMap_left_inv realWire
        realEndpoint realMember
      rw [mapExact]
      simp only [inverseTransportEndpointInverse]
      rw [forwardCancelRaw, inverseReal, dif_neg generated, dif_neg head,
        targetCancel]
      have backwardRecover : backwardNodes realNode = endpoint.node :=
        backwardNodes.right_inv endpoint.node
      exact Internal.endpoint_eq backwardRecover rfl

/-- The pair endpoint map cancels its inverse on incident planned
endpoints. -/
theorem inverseTransportEndpointMap_inverse
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (candidate : CEndpoint planned.val.nodeCount)
    (member : candidate ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire)).endpoints) :
    forward.inverseTransportEndpointMap backward targetIso wireExact
        targetWire
        (forward.inverseTransportEndpointInverse backward targetIso wireExact
          targetWire candidate) = candidate := by
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  let middleNode := forwardNodes candidate.node
  let realNode := targetIso.nodes.symm middleNode
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · simp only [inverseTransportEndpointInverse]
    rw [show targetIso.nodes.symm (forwardNodes candidate.node) = realNode
      from rfl, dif_pos generated]
    simp only [inverseTransportEndpointMap]
    have backwardCancelRaw :
        (backward.argumentResult.nodeEquiv backward.targetSites).symm
            ((backward.argumentResult.nodeEquiv
              backward.targetSites) realNode) = realNode :=
      (backward.argumentResult.nodeEquiv
        backward.targetSites).left_inv realNode
    simp only [backwardCancelRaw, dif_pos generated]
    congr 1
    unfold inverseTransportNodeEquiv
      ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
    change forwardNodes.symm
        (targetIso.nodes (backwardNodes.symm (backwardNodes realNode))) =
      candidate.node
    calc
      forwardNodes.symm
          (targetIso.nodes (backwardNodes.symm (backwardNodes realNode))) =
          forwardNodes.symm (targetIso.nodes realNode) :=
        congrArg (fun node => forwardNodes.symm (targetIso.nodes node))
          (backwardNodes.left_inv realNode)
      _ = candidate.node := by
        have targetRecover : targetIso.nodes realNode = middleNode :=
          targetIso.nodes.right_inv middleNode
        rw [targetRecover]
        exact forwardNodes.left_inv candidate.node
  · by_cases head : targetWire = backward.targetWire
    · simp only [inverseTransportEndpointInverse]
      rw [show targetIso.nodes.symm (forwardNodes candidate.node) = realNode
        from rfl, dif_neg generated, dif_pos head]
      simp only [inverseTransportEndpointMap]
      have backwardCancelRaw :
          (backward.argumentResult.nodeEquiv backward.targetSites).symm
              ((backward.argumentResult.nodeEquiv
                backward.targetSites) realNode) = realNode :=
        (backward.argumentResult.nodeEquiv
          backward.targetSites).left_inv realNode
      simp only [backwardCancelRaw, dif_neg generated, dif_pos head]
      congr 1
      unfold inverseTransportNodeEquiv
        ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
      change forwardNodes.symm
          (targetIso.nodes (backwardNodes.symm (backwardNodes realNode))) =
        candidate.node
      calc
        forwardNodes.symm
            (targetIso.nodes (backwardNodes.symm (backwardNodes realNode))) =
            forwardNodes.symm (targetIso.nodes realNode) :=
          congrArg (fun node => forwardNodes.symm (targetIso.nodes node))
            (backwardNodes.left_inv realNode)
        _ = candidate.node := by
          have targetRecover : targetIso.nodes realNode = middleNode :=
            targetIso.nodes.right_inv middleNode
          rw [targetRecover]
          exact forwardNodes.left_inv candidate.node
    · have targetRetained : targetWire ∉
          backward.argumentResult.targetRemovedWires := by
        rw [backward.targetRemovedWires_exact]
        intro removed
        exact head (List.mem_singleton.mp removed)
      let realWire := backward.argumentResult.sourceWireOfRetainedTarget
        targetWire targetRetained
      have realRetained : realWire ∉
          backward.argumentResult.sourceRemovedWires :=
        backward.argumentResult.sourceRetainedWire_not_removed
          (backward.argumentResult.retainedBaseWireOfTarget targetWire
            targetRetained)
      let middleWire := targetIso.wires realWire
      have middleWireRetained : middleWire ∉
          forward.argumentResult.targetRemovedWires := by
        intro removed
        exact realRetained
          ((forward.inverseTransport_removedWire_iff backward targetIso
            wireExact realWire).mpr removed)
      let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
        middleWire middleWireRetained
      have plannedWireRetained : plannedWire ∉
          forward.argumentResult.sourceRemovedWires :=
        forward.argumentResult.sourceRetainedWire_not_removed
          (forward.argumentResult.retainedBaseWireOfTarget middleWire
            middleWireRetained)
      have forwardImage :
          forward.argumentResult.retainedWireImage plannedWire
            plannedWireRetained = middleWire :=
        forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
          middleWire middleWireRetained
      have carrierExact :
          forward.inverseTransportWireEquiv backward targetIso wireExact
            targetWire = plannedWire := by
        change forward.inverseTransportWireMap backward targetIso wireExact
          targetWire = plannedWire
        unfold inverseTransportWireMap
        rw [dif_neg head]
      have plannedRetained : candidate.node ∉
          ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
        intro plannedGenerated
        have middleGenerated : forwardNodes candidate.node ∈
            ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
          let position :=
            ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
              forward.sourceSites candidate.node plannedGenerated
          have sourceExact :=
            ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
              forward.sourceSites candidate.node plannedGenerated
          have sourceMember :
              (forward.sourceSites.sites.get position).node ∈
                ConcreteWirePrimitive.argumentSiteNodes
                  forward.sourceSites := by
            unfold ConcreteWirePrimitive.argumentSiteNodes
            exact List.mem_map.mpr
              ⟨forward.sourceSites.sites.get position,
                List.get_mem _ _, rfl⟩
          have imageExact : forwardNodes
              (forward.sourceSites.sites.get position).node =
                forward.argumentResult.targetNode position := by
            unfold forwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
            change forward.argumentResult.nodeImage
              (forward.sourceSites.sites.get position).node = _
            have sourceMemberRaw :
                (forward.sourceSites.sites.get position).node ∈
                  ConcreteWirePrimitive.argumentSiteNodes
                    forward.argumentResult.sites := sourceMember
            rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
              dif_pos sourceMemberRaw]
            change forward.argumentResult.targetNode
              (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
                forward.argumentResult.sites
                (forward.argumentResult.sites.sites.get position).node _) = _
            rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
          rw [sourceExact] at imageExact
          rw [imageExact]
          exact forward.argumentResult.generatedNode_targetSiteNode
            forward.targetSites position
        have realRecover : targetIso.nodes realNode = middleNode :=
          targetIso.nodes.right_inv middleNode
        apply (forward.inverseTransport_middleNode_retained backward targetIso
          wireExact realNode generated)
        exact Eq.mp (congrArg
          (fun node => node ∈
            ConcreteWirePrimitive.argumentSiteNodes forward.targetSites)
          realRecover.symm) middleGenerated
      rw [carrierExact] at member
      let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
        ⟨middleNode, candidate.port⟩
      have middleMember : middleEndpoint ∈
          (forward.target.val.wires middleWire).endpoints := by
        have pushed := argumentResult_retainedEndpointImage_mem
          forward.argumentResult forward.targetSites plannedWire candidate
            member plannedRetained
        simpa [forwardImage] using pushed
      let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
      have realMember := targetIso.endpointInverse_mem realWire middleEndpoint
        middleMember
      have realEndpointNode : realEndpoint.node = realNode := by
        have corresponds := targetIso.endpointMap_corresponds realWire
          realEndpoint realMember
        rw [targetIso.endpointMap_right_inv realWire middleEndpoint
          middleMember] at corresponds
        apply targetIso.nodes.injective
        have realRecover : targetIso.nodes realNode = middleNode :=
          targetIso.nodes.right_inv middleNode
        exact corresponds.1.symm.trans realRecover.symm
      have realGenerated : realEndpoint.node ∉
          ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
        simpa [realEndpointNode] using generated
      have inverseExact :
          forward.inverseTransportEndpointInverse backward targetIso wireExact
              targetWire candidate =
            ⟨backwardNodes realEndpoint.node, realEndpoint.port⟩ := by
        simp only [inverseTransportEndpointInverse]
        rw [show targetIso.nodes.symm (forwardNodes candidate.node) = realNode
          from rfl, dif_neg generated, dif_neg head]
      rw [inverseExact]
      simp only [inverseTransportEndpointMap]
      have backwardCancel : backwardNodes.symm
          (backwardNodes realEndpoint.node) = realEndpoint.node :=
        backwardNodes.left_inv realEndpoint.node
      rw [backwardCancel, dif_neg realGenerated, dif_neg head]
      have targetCancel := targetIso.endpointMap_right_inv realWire
        middleEndpoint middleMember
      rw [targetCancel]
      change
        { node := forwardNodes.symm (forwardNodes candidate.node),
          port := candidate.port } = candidate
      have forwardCancel : forwardNodes.symm
          (forwardNodes candidate.node) = candidate.node :=
        forwardNodes.left_inv candidate.node
      exact Internal.endpoint_eq forwardCancel rfl

/-- The transported region carrier restores the planned root. -/
theorem inverseTransport_root
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val) :
    forward.inverseTransportRegionEquiv backward targetIso
        backward.target.val.root = planned.val.root := by
  unfold inverseTransportRegionEquiv
  change forward.argumentResult.regionEquiv.symm
    (targetIso.regions
      (backward.argumentResult.regionEquiv.symm backward.target.val.root)) = _
  have backwardRoot : backward.target.val.root =
      backward.argumentResult.regionEquiv real.val.root := by
    exact backward.argumentResult.targetRoot_exact.trans
      (backward.argumentResult.regionImage_exact real.val.root)
  rw [backwardRoot]
  have backwardCancel :=
    backward.argumentResult.regionEquiv.left_inv real.val.root
  change backward.argumentResult.regionEquiv.invFun
      (backward.argumentResult.regionEquiv real.val.root) = real.val.root
    at backwardCancel
  calc
    _ = forward.argumentResult.regionEquiv.symm
        (targetIso.regions real.val.root) :=
      congrArg (fun value => forward.argumentResult.regionEquiv.symm
        (targetIso.regions value)) backwardCancel
    _ = forward.argumentResult.regionEquiv.symm forward.target.val.root := by
      rw [targetIso.root]
    _ = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionEquiv planned.val.root) := by
      congr 1
      exact forward.argumentResult.targetRoot_exact.trans
        (forward.argumentResult.regionImage_exact planned.val.root)
    _ = planned.val.root := forward.argumentResult.regionEquiv.left_inv _

/-- Region tables commute with the composed construction carrier. -/
theorem inverseTransport_region_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (region : backward.target.val.RegionId) :
    planned.val.regions
        (forward.inverseTransportRegionEquiv backward targetIso region) =
      (backward.target.val.regions region).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realRegion := backward.argumentResult.regionEquiv.symm region
  have backwardData := backward.argumentResult.regionImage_data realRegion
  have backwardRegionExact :
      backward.argumentResult.regionEquiv realRegion = region :=
    backward.argumentResult.regionEquiv.right_inv region
  rw [backwardRegionExact] at backwardData
  have backwardDataPublic : backward.target.val.regions region =
      (real.val.regions realRegion).rename
        backward.argumentResult.regionEquiv := backwardData
  have middleData := targetIso.region_table realRegion
  have plannedData := forward.argumentResult.regionImage_data
    (forward.argumentResult.regionEquiv.symm
      (targetIso.regions realRegion))
  have plannedRegionExact : forward.argumentResult.regionEquiv
      (forward.argumentResult.regionEquiv.symm
        (targetIso.regions realRegion)) = targetIso.regions realRegion :=
    forward.argumentResult.regionEquiv.right_inv _
  rw [plannedRegionExact] at plannedData
  unfold inverseTransportRegionEquiv
  change planned.val.regions
      (forward.argumentResult.regionEquiv.symm
        (targetIso.regions realRegion)) = _
  rw [backwardDataPublic]
  have relation :
      (real.val.regions realRegion).rename targetIso.regions =
        (planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion))).rename
          forward.argumentResult.regionEquiv :=
    middleData.symm.trans plannedData
  cases realData : real.val.regions realRegion with
  | sheet =>
      cases plannedExact : planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet => rfl
      | cut parent =>
          rw [realData, plannedExact] at relation
          contradiction
  | cut realParent =>
      cases plannedExact : planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet =>
          rw [realData, plannedExact] at relation
          contradiction
      | cut plannedParent =>
          rw [realData, plannedExact] at relation
          simp only [CRegion.rename] at relation
          have parentRelation : targetIso.regions realParent =
              forward.argumentResult.regionEquiv plannedParent :=
            CRegion.cut.inj relation
          congr 1
          unfold ConcreteWirePrimitive.ArgumentResult.inverseTransportRegionEquiv
          have backwardParentCancel :=
            backward.argumentResult.regionEquiv.left_inv realParent
          calc
            plannedParent = forward.argumentResult.regionEquiv.symm
                (targetIso.regions realParent) :=
              (forward.argumentResult.regionEquiv.left_inv
                plannedParent).symm.trans
                (congrArg forward.argumentResult.regionEquiv.symm
                  parentRelation).symm
            _ = forward.argumentResult.regionEquiv.symm
                (targetIso.regions
                  (backward.argumentResult.regionEquiv.symm
                    (backward.argumentResult.regionEquiv realParent))) :=
              congrArg (fun value => forward.argumentResult.regionEquiv.symm
                (targetIso.regions value)) backwardParentCancel.symm

/-- The endpoint transport node component is the composed node carrier. -/
theorem inverseTransportEndpointMap_node
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    (forward.inverseTransportEndpointMap backward targetIso wireExact
      targetWire endpoint).node =
      forward.inverseTransportNodeEquiv backward targetIso endpoint.node := by
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  let realNode := backwardNodes.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · simp only [inverseTransportEndpointMap]
    rw [show backwardNodes.symm endpoint.node = realNode from rfl,
      dif_pos generated]
  · by_cases head : targetWire = backward.targetWire
    · simp only [inverseTransportEndpointMap]
      rw [show backwardNodes.symm endpoint.node = realNode from rfl,
        dif_neg generated, dif_pos head]
    · have targetRetained : targetWire ∉
          backward.argumentResult.targetRemovedWires := by
        rw [backward.targetRemovedWires_exact]
        intro removed
        exact head (List.mem_singleton.mp removed)
      let realWire := backward.argumentResult.sourceWireOfRetainedTarget
        targetWire targetRetained
      have realRetained : realWire ∉
          backward.argumentResult.sourceRemovedWires :=
        backward.argumentResult.sourceRetainedWire_not_removed
          (backward.argumentResult.retainedBaseWireOfTarget targetWire
            targetRetained)
      have backwardImage :
          backward.argumentResult.retainedWireImage realWire realRetained =
            targetWire :=
        backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
          targetWire targetRetained
      let realEndpoint : CEndpoint real.val.nodeCount :=
        ⟨realNode, endpoint.port⟩
      have realMember : realEndpoint ∈
          (real.val.wires realWire).endpoints := by
        apply argumentResult_retainedEndpointInverse_mem
          backward.argumentResult backward.targetSites realWire realRetained
        · simpa [backwardImage] using member
        · exact generated
      let middleEndpoint := targetIso.endpointMap realWire realEndpoint
      have corresponds := targetIso.endpointMap_corresponds realWire
        realEndpoint realMember
      simp only [inverseTransportEndpointMap]
      rw [show backwardNodes.symm endpoint.node = realNode from rfl,
        dif_neg generated, dif_neg head]
      unfold inverseTransportNodeEquiv
        ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
      change forwardNodes.symm middleEndpoint.node =
        forwardNodes.symm (targetIso.nodes realNode)
      exact congrArg forwardNodes.symm corresponds.1

/-- The endpoint transport preserves every non-identity port exactly and
can only change storage indices between corresponding identity ports. -/
theorem inverseTransportEndpointMap_port_shape
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    (forward.inverseTransportEndpointMap backward targetIso wireExact
        targetWire endpoint).port = endpoint.port ∨
      ∃ sourceIndex targetIndex,
        endpoint.port = .identity sourceIndex ∧
          (forward.inverseTransportEndpointMap backward targetIso wireExact
            targetWire endpoint).port = .identity targetIndex := by
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let realNode := backwardNodes.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · left
    simp only [inverseTransportEndpointMap]
    rw [show backwardNodes.symm endpoint.node = realNode from rfl,
      dif_pos generated]
  · by_cases head : targetWire = backward.targetWire
    · left
      simp only [inverseTransportEndpointMap]
      rw [show backwardNodes.symm endpoint.node = realNode from rfl,
        dif_neg generated, dif_pos head]
    · have targetRetained : targetWire ∉
          backward.argumentResult.targetRemovedWires := by
        rw [backward.targetRemovedWires_exact]
        intro removed
        exact head (List.mem_singleton.mp removed)
      let realWire := backward.argumentResult.sourceWireOfRetainedTarget
        targetWire targetRetained
      have realRetained : realWire ∉
          backward.argumentResult.sourceRemovedWires :=
        backward.argumentResult.sourceRetainedWire_not_removed
          (backward.argumentResult.retainedBaseWireOfTarget targetWire
            targetRetained)
      have backwardImage :
          backward.argumentResult.retainedWireImage realWire realRetained =
            targetWire :=
        backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
          targetWire targetRetained
      let realEndpoint : CEndpoint real.val.nodeCount :=
        ⟨realNode, endpoint.port⟩
      have realMember : realEndpoint ∈
          (real.val.wires realWire).endpoints := by
        apply argumentResult_retainedEndpointInverse_mem
          backward.argumentResult backward.targetSites realWire realRetained
        · simpa [backwardImage] using member
        · exact generated
      let middleEndpoint := targetIso.endpointMap realWire realEndpoint
      have middleMember := targetIso.endpointMap_mem realWire realEndpoint
        realMember
      have corresponds := targetIso.endpointMap_corresponds realWire
        realEndpoint realMember
      have mappedPort :
          (forward.inverseTransportEndpointMap backward targetIso wireExact
            targetWire endpoint).port = middleEndpoint.port := by
        simp only [inverseTransportEndpointMap]
        rw [show backwardNodes.symm endpoint.node = realNode from rfl,
          dif_neg generated, dif_neg head]
      unfold PortCorresponds at corresponds
      cases realData : real.val.nodes realEndpoint.node with
      | atom region arguments =>
          rw [realData] at corresponds
          cases middleData : forward.target.val.nodes middleEndpoint.node <;>
            simp [middleData] at corresponds
          all_goals exact Or.inl (mappedPort.trans corresponds.2)
      | ref region definition arguments =>
          rw [realData] at corresponds
          cases middleData : forward.target.val.nodes middleEndpoint.node <;>
            simp [middleData] at corresponds
          all_goals exact Or.inl (mappedPort.trans corresponds.2)
      | identity region signature arity =>
          rw [realData] at corresponds
          cases middleData : forward.target.val.nodes middleEndpoint.node with
          | atom targetRegion targetArguments =>
              change forward.target.val.nodes
                  (targetIso.endpointMap realWire realEndpoint).node =
                .atom targetRegion targetArguments at middleData
              simp [middleData] at corresponds
              exact Or.inl (mappedPort.trans corresponds.2)
          | ref targetRegion definition targetArguments =>
              change forward.target.val.nodes
                  (targetIso.endpointMap realWire realEndpoint).node =
                .ref targetRegion definition targetArguments at middleData
              simp [middleData] at corresponds
              exact Or.inl (mappedPort.trans corresponds.2)
          | identity targetRegion targetSignature targetArity =>
              change forward.target.val.nodes
                  (targetIso.endpointMap realWire realEndpoint).node =
                .identity targetRegion targetSignature targetArity
                  at middleData
              have sourceRequired :=
                ConcreteDiagram.incident_port_required definitions real.val
                  real.property realWire realEndpoint realMember
              rw [ConcreteDiagram.requiredPorts, realData] at sourceRequired
              rcases List.mem_map.mp sourceRequired with
                ⟨sourceIndex, _sourceBound, sourcePort⟩
              have middleRequired :=
                ConcreteDiagram.incident_port_required definitions
                  forward.target.val forward.target.property
                  (targetIso.wires realWire) middleEndpoint middleMember
              rw [ConcreteDiagram.requiredPorts, middleData] at middleRequired
              rcases List.mem_map.mp middleRequired with
                ⟨targetIndex, _targetBound, targetPort⟩
              exact Or.inr ⟨sourceIndex, targetIndex, sourcePort.symm,
                mappedPort.trans targetPort.symm⟩

/-- The endpoint map satisfies exact concrete port correspondence for the
construction-owned node carrier. -/
theorem inverseTransportEndpointMap_corresponds
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    PortCorresponds backward.target.val planned.val
      (forward.inverseTransportNodeEquiv backward targetIso) endpoint
      (forward.inverseTransportEndpointMap backward targetIso wireExact
        targetWire endpoint) := by
  let mapped := forward.inverseTransportEndpointMap backward targetIso
    wireExact targetWire endpoint
  have mappedNode : mapped.node =
      forward.inverseTransportNodeEquiv backward targetIso endpoint.node :=
    forward.inverseTransportEndpointMap_node backward targetIso wireExact
      targetWire endpoint member
  have mappedData : planned.val.nodes mapped.node =
      (backward.target.val.nodes endpoint.node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
    rw [mappedNode]
    exact forward.inverseTransport_node_table backward targetIso wireExact
      endpoint.node
  have portShape := forward.inverseTransportEndpointMap_port_shape backward
    targetIso wireExact targetWire endpoint member
  have sourceRequired := ConcreteDiagram.incident_port_required definitions
    backward.target.val backward.target.property targetWire endpoint member
  unfold PortCorresponds
  refine ⟨mappedNode, ?_⟩
  cases sourceData : backward.target.val.nodes endpoint.node with
  | atom region arguments =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      cases portShape with
      | inl exactPort => exact exactPort
      | inr identityPorts =>
          rcases identityPorts with
            ⟨sourceIndex, _targetIndex, sourcePort, _targetPort⟩
          rw [sourcePort] at sourceRequired
          simp at sourceRequired
  | ref region definition arguments =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      cases portShape with
      | inl exactPort => exact exactPort
      | inr identityPorts =>
          rcases identityPorts with
            ⟨sourceIndex, _targetIndex, sourcePort, _targetPort⟩
          rw [sourcePort] at sourceRequired
          simp at sourceRequired
  | identity region signature arity =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      refine ⟨rfl, rfl, ?_⟩
      cases portShape with
      | inl exactPort =>
          rcases List.mem_map.mp sourceRequired with
            ⟨sourceIndex, _sourceBound, sourcePort⟩
          exact ⟨sourceIndex, sourceIndex, sourcePort.symm,
            exactPort.trans sourcePort.symm⟩
      | inr identityPorts => exact identityPorts

/-- Total concrete isomorphism reconstructed directly from the accepted
arity shift, its checked inverse unshift, and the supplied suffix
isomorphism. -/
def inverseTransportIso
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    ConcreteIso backward.target.val planned.val where
  regions := forward.inverseTransportRegionEquiv backward targetIso
  nodes := forward.inverseTransportNodeEquiv backward targetIso
  wires := forward.inverseTransportWireEquiv backward targetIso wireExact
  root := forward.inverseTransport_root backward targetIso
  region_table := forward.inverseTransport_region_table backward targetIso
  node_table := forward.inverseTransport_node_table backward targetIso
    wireExact
  wire_signature := forward.inverseTransport_wire_signature backward
    targetIso wireExact
  wire_scope := forward.inverseTransport_wire_scope backward targetIso
    wireExact
  endpointMap := forward.inverseTransportEndpointMap backward targetIso
    wireExact
  endpointInverse := forward.inverseTransportEndpointInverse backward
    targetIso wireExact
  endpointMap_mem := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointMap_mem backward targetIso wireExact
      targetWire endpoint member
  endpointInverse_mem := by
    intro targetWire candidate member
    exact forward.inverseTransportEndpointInverse_mem backward targetIso
      wireExact targetWire candidate member
  endpointMap_left_inv := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointInverse_map backward targetIso
      wireExact targetWire endpoint member
  endpointMap_right_inv := by
    intro targetWire candidate member
    exact forward.inverseTransportEndpointMap_inverse backward targetIso
      wireExact targetWire candidate member
  endpointMap_corresponds := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointMap_corresponds backward targetIso
      wireExact targetWire endpoint member


end AppliedArityShift

end Arguments

end WirePrimitive

end VisualProof
