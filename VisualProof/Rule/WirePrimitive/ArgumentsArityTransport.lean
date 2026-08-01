import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

namespace AppliedArityShift

/-- Planned source-site position represented by one real arity-unshift site
after transport through the supplied suffix isomorphism. -/
def inverseTransportSitePosition
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
    Fin forward.sourceSites.sites.length :=
  let sourceEndpoint := (backward.sourceSites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.sourceSites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint :=
    targetIso.endpointMap backwardWire sourceEndpoint
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
  forward.argumentResult.sourcePositionOfTargetNode forward.targetSites
    middleNode generated

/-- The suffix isomorphism sends each real unshift source site to the exact
forward shift target node selected by endpoint order. -/
theorem inverseTransport_middleNode
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
    targetIso.nodes (backward.sourceSites.sites.get site).node =
      forward.argumentResult.targetNode
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site) := by
  let sourceEndpoint := (backward.sourceSites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.sourceSites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint :=
    targetIso.endpointMap backwardWire sourceEndpoint
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
  have middleNodeExact : middleSite.node =
      targetIso.nodes (backward.sourceSites.sites.get site).node := by
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
    simpa [middleSite, sourceEndpoint, AppliedSite.endpoint] using
      (congrArg CEndpoint.node selected).trans corresponds.1
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  have generated : middleSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨middleSite, List.get_mem _ _, rfl⟩
  have targetExact : forward.argumentResult.targetNode plannedPosition =
      middleSite.node :=
    forward.argumentResult.targetNode_sourcePositionOfTargetNode
      forward.targetSites middleSite.node generated
  exact middleNodeExact.symm.trans targetExact.symm

/-- A real node retained by unshift cannot map to a generated shift target
site. -/
theorem inverseTransport_middleNode_retained
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites) :
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
      rw [← backward.sourceSites.exhaustive] at incident
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

/-- Every wire selected by the inverse unshift is carried by the suffix
isomorphism to the shift-created head/local block. -/
theorem inverseTransport_removedWire_image
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realWire : real.val.WireId)
    (removed : realWire ∈ backward.argumentResult.sourceRemovedWires) :
    targetIso.wires realWire ∈
      forward.argumentResult.targetRemovedWires := by
  change realWire ∈
      backwardWire :: backward.argumentResult.spec.removedWires at removed
  rcases List.mem_cons.mp removed with head | removedLocal
  · subst realWire
    unfold ConcreteWirePrimitive.ArgumentResult.targetRemovedWires
    exact List.mem_cons.mpr (Or.inl wireExact)
  · rcases backward.removedLocal_exact realWire removedLocal with
      ⟨site, siteMember, endpointsExact⟩
    obtain ⟨sitePosition, siteGet⟩ := List.get_of_mem siteMember
    let sourceEndpoint : CEndpoint real.val.nodeCount :=
      ⟨site.node, .arg forward.sourceArgumentList.length⟩
    have sourceMember : sourceEndpoint ∈
        (real.val.wires realWire).endpoints := by
      rw [endpointsExact]
      simp [sourceEndpoint]
    let middleEndpoint := targetIso.endpointMap realWire sourceEndpoint
    have middleMember : middleEndpoint ∈
        (forward.target.val.wires (targetIso.wires realWire)).endpoints :=
      targetIso.endpointMap_mem realWire sourceEndpoint sourceMember
    have middleNode : middleEndpoint.node =
        forward.targetNode
          (forward.inverseTransportSitePosition backward targetIso
            wireExact sitePosition) := by
      have nodeExact := forward.inverseTransport_middleNode backward targetIso
        wireExact sitePosition
      have corresponds := targetIso.endpointMap_corresponds realWire
        sourceEndpoint sourceMember
      rw [siteGet] at nodeExact
      simpa [AppliedArityShift.targetNode] using
        corresponds.1.trans nodeExact
    have middlePort : middleEndpoint.port =
        .arg forward.sourceArgumentList.length := by
      have corresponds := targetIso.endpointMap_corresponds realWire
        sourceEndpoint sourceMember
      have sourceData := site.node_data
      unfold PortCorresponds at corresponds
      rw [sourceData] at corresponds
      exact corresponds.2
    let plannedSite := forward.inverseTransportSitePosition backward targetIso
      wireExact sitePosition
    have owner := forward.targetNode_local_owner plannedSite
    have plannedSiteLength :
        (forward.sourceSites.sites.get plannedSite).arguments.length =
          forward.sourceArgumentList.length := by
      exact (forward.sourceSites.sites.get plannedSite).arguments_length.trans
        (congrArg List.length
          (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
            forward.sourceArgumentList forward.sourceWire_signature
            (forward.sourceSites.sites.get plannedSite)))
    have mappedOwner : forward.target.val.endpointOwner? middleEndpoint =
        some (targetIso.wires realWire) :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        forward.target.val forward.target.property middleEndpoint.node
        middleEndpoint.port
        (ConcreteDiagram.incident_port_required definitions
          forward.target.val forward.target.property
          (targetIso.wires realWire) middleEndpoint middleMember)
        (targetIso.wires realWire) middleMember
    have localWireExact : targetIso.wires realWire =
        forward.targetLocalWire plannedSite := by
      have endpointExact : middleEndpoint =
          (⟨forward.targetNode plannedSite,
            .arg (forward.sourceSites.sites.get plannedSite).arguments.length⟩ :
            CEndpoint forward.target.val.nodeCount) := by
        calc
          middleEndpoint = ⟨middleEndpoint.node, middleEndpoint.port⟩ := by
            cases middleEndpoint
            rfl
          _ = _ := by rw [middleNode, middlePort, plannedSiteLength]
      rw [endpointExact, owner] at mappedOwner
      exact Option.some.inj mappedOwner.symm
    unfold ConcreteWirePrimitive.ArgumentResult.targetRemovedWires
    apply List.mem_cons.mpr
    right
    rw [localWireExact]
    exact forward.targetLocalWire_mem plannedSite

/-- Conversely, every member of the shift-created head/local block has a
unique preimage selected by the inverse unshift. -/
theorem inverseTransport_removedWire_preimage
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : forward.target.val.WireId)
    (removed : targetWire ∈ forward.argumentResult.targetRemovedWires) :
    targetIso.wires.symm targetWire ∈
      backward.argumentResult.sourceRemovedWires := by
  rcases forward.targetRemovedWire_cases targetWire removed with
      head | ⟨plannedSite, localExact⟩
  · subst targetWire
    change targetIso.wires.symm forward.targetWire ∈
      backwardWire :: backward.argumentResult.spec.removedWires
    apply List.mem_cons.mpr
    left
    calc
      targetIso.wires.symm forward.targetWire =
          targetIso.wires.symm (targetIso.wires backwardWire) := by
        rw [wireExact]
      _ = backwardWire := targetIso.wires.left_inv backwardWire
  · subst targetWire
    let realWire := targetIso.wires.symm
      (forward.targetLocalWire plannedSite)
    let candidate : CEndpoint forward.target.val.nodeCount :=
      ⟨forward.targetNode plannedSite,
        .arg (forward.sourceSites.sites.get plannedSite).arguments.length⟩
    have candidateOwner : forward.target.val.endpointOwner? candidate =
        some (forward.targetLocalWire plannedSite) := by
      exact forward.targetNode_local_owner plannedSite
    have candidateMember : candidate ∈
        (forward.target.val.wires
          (forward.targetLocalWire plannedSite)).endpoints :=
      ConcreteDiagram.endpointOwner?_incident forward.target.val candidate
        (forward.targetLocalWire plannedSite) candidateOwner
    have mappedMember : candidate ∈
        (forward.target.val.wires (targetIso.wires realWire)).endpoints := by
      have cancel : targetIso.wires realWire =
          forward.targetLocalWire plannedSite :=
        targetIso.wires.right_inv _
      simpa [cancel] using candidateMember
    obtain ⟨realEndpoint, realMember, corresponds⟩ :=
      targetIso.endpoint_backward realWire candidate mappedMember
    have realGenerated : realEndpoint.node ∈
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
      by_cases generated : realEndpoint.node ∈
          ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
      · exact generated
      · exfalso
        have middleRetained := forward.inverseTransport_middleNode_retained
          backward targetIso wireExact realEndpoint.node generated
        apply middleRetained
        have plannedGenerated :=
          forward.argumentResult.generatedNode_targetSiteNode
            forward.targetSites plannedSite
        rw [← corresponds.1]
        simpa [candidate, AppliedArityShift.targetNode] using plannedGenerated
    unfold ConcreteWirePrimitive.argumentSiteNodes at realGenerated
    rcases List.mem_map.mp realGenerated with
      ⟨realSite, realSiteMember, realNodeExact⟩
    obtain ⟨realSitePosition, realSiteGet⟩ :=
      List.get_of_mem realSiteMember
    have realPortExact : realEndpoint.port =
        .arg forward.sourceArgumentList.length := by
      have realData := realSite.node_data
      unfold PortCorresponds at corresponds
      rw [← realNodeExact, realData] at corresponds
      have plannedLength :
          (forward.sourceSites.sites.get plannedSite).arguments.length =
            forward.sourceArgumentList.length := by
        exact (forward.sourceSites.sites.get plannedSite).arguments_length.trans
          (congrArg List.length
            (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
              forward.sourceArgumentList forward.sourceWire_signature
              (forward.sourceSites.sites.get plannedSite)))
      exact corresponds.2.symm.trans
        (congrArg CPort.arg plannedLength)
    rcases backward.siteLocal_removed realSitePosition with
      ⟨selectedWire, selectedRemoved, selectedEndpoints⟩
    have selectedMember :
        (⟨realEndpoint.node, .arg forward.sourceArgumentList.length⟩ :
          CEndpoint real.val.nodeCount) ∈
          (real.val.wires selectedWire).endpoints := by
      rw [selectedEndpoints]
      simp only [List.mem_singleton]
      calc
        (⟨realEndpoint.node, .arg forward.sourceArgumentList.length⟩ :
            CEndpoint real.val.nodeCount) =
            ⟨(backward.sourceSites.sites.get realSitePosition).node,
              .arg forward.sourceArgumentList.length⟩ := by
          rw [realSiteGet, realNodeExact]
        _ = _ := rfl
    have realEndpointExact : realEndpoint =
        (⟨realEndpoint.node, .arg forward.sourceArgumentList.length⟩ :
          CEndpoint real.val.nodeCount) := by
      calc
        realEndpoint = ⟨realEndpoint.node, realEndpoint.port⟩ := by
          cases realEndpoint
          rfl
        _ = _ := by rw [realPortExact]
    rw [← realEndpointExact] at selectedMember
    have required := ConcreteDiagram.incident_port_required definitions
      real.val real.property realWire realEndpoint realMember
    have realOwner := ConcreteDiagram.endpointOwner?_eq_of_incident
      definitions real.val real.property realEndpoint.node realEndpoint.port
      required realWire realMember
    have selectedOwner := ConcreteDiagram.endpointOwner?_eq_of_incident
      definitions real.val real.property realEndpoint.node realEndpoint.port
      required selectedWire selectedMember
    have selectedExact : realWire = selectedWire := by
      rw [realOwner] at selectedOwner
      exact Option.some.inj selectedOwner
    change realWire ∈
      backwardWire :: backward.argumentResult.spec.removedWires
    apply List.mem_cons.mpr
    right
    rw [selectedExact]
    exact selectedRemoved

/-- The suffix wire equivalence reflects the exact construction removal
blocks. -/
theorem inverseTransport_removedWire_iff
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realWire : real.val.WireId) :
    realWire ∈ backward.argumentResult.sourceRemovedWires ↔
      targetIso.wires realWire ∈
        forward.argumentResult.targetRemovedWires := by
  constructor
  · exact forward.inverseTransport_removedWire_image backward targetIso
      wireExact realWire
  · intro removed
    have preimage := forward.inverseTransport_removedWire_preimage backward
      targetIso wireExact (targetIso.wires realWire) removed
    simpa using preimage

/-- Wire map obtained by exposing the inverse construction's retained real
source, crossing the suffix isomorphism, and closing the forward common
core. -/
def inverseTransportWireMap
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) : planned.val.WireId :=
  if head : targetWire = backward.targetWire then
    forwardWire
  else
    let realWire := backward.argumentResult.sourceWireOfRetainedTarget
      targetWire (by
        rw [backward.targetRemovedWires_exact]
        intro member
        exact head (List.mem_singleton.mp member))
    let middleWire := targetIso.wires realWire
    forward.argumentResult.sourceWireOfRetainedTarget middleWire (by
      intro removed
      have realRemoved :=
        (forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mpr removed
      exact (backward.argumentResult.sourceRetainedWire_not_removed
        (backward.argumentResult.retainedBaseWireOfTarget targetWire (by
          rw [backward.targetRemovedWires_exact]
          intro member
          exact head (List.mem_singleton.mp member))) realRemoved))

/-- Inverse wire map, using the forward retained embedding followed by the
suffix inverse and the unshift retained embedding. -/
def inverseTransportWireInverse
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (sourceWire : planned.val.WireId) : backward.target.val.WireId :=
  if head : sourceWire = forwardWire then
    backward.targetWire
  else
    let middleWire := forward.argumentResult.retainedWireImage sourceWire (by
      rw [forward.sourceRemovedWires_exact]
      simpa [head])
    let realWire := targetIso.wires.symm middleWire
    backward.argumentResult.retainedWireImage realWire (by
      intro removed
      have middleRemoved :=
        (forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mp removed
      have middleExact : targetIso.wires realWire = middleWire :=
        targetIso.wires.right_inv middleWire
      rw [middleExact] at middleRemoved
      exact (forward.argumentResult.retainedWireImage_not_targetRemoved
        sourceWire (by
          rw [forward.sourceRemovedWires_exact]
          simpa [head])) middleRemoved)

/-- The construction-owned arity wire maps cancel on inverse target wires. -/
theorem inverseTransportWire_left_inv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    forward.inverseTransportWireInverse backward targetIso wireExact
        (forward.inverseTransportWireMap backward targetIso wireExact
          targetWire) = targetWire := by
  by_cases head : targetWire = backward.targetWire
  · subst targetWire
    simp [inverseTransportWireMap, inverseTransportWireInverse]
  · let targetRetained : targetWire ∉
        backward.argumentResult.targetRemovedWires := by
      rw [backward.targetRemovedWires_exact]
      intro member
      exact head (List.mem_singleton.mp member)
    let realWire := backward.argumentResult.sourceWireOfRetainedTarget
      targetWire targetRetained
    have realRetained : realWire ∉
        backward.argumentResult.sourceRemovedWires :=
      backward.argumentResult.sourceRetainedWire_not_removed
        (backward.argumentResult.retainedBaseWireOfTarget targetWire
          targetRetained)
    let middleWire := targetIso.wires realWire
    have middleRetained : middleWire ∉
        forward.argumentResult.targetRemovedWires := by
      exact fun removed => realRetained
        ((forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mpr removed)
    let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
      middleWire middleRetained
    have plannedRetained : plannedWire ∉
        forward.argumentResult.sourceRemovedWires :=
      forward.argumentResult.sourceRetainedWire_not_removed
        (forward.argumentResult.retainedBaseWireOfTarget middleWire
          middleRetained)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      exact plannedRetained (by
        rw [forward.sourceRemovedWires_exact, same]
        simp)
    unfold inverseTransportWireMap inverseTransportWireInverse
    rw [dif_neg head, dif_neg plannedDifferent]
    change backward.argumentResult.retainedWireImage
        (targetIso.wires.symm
          (forward.argumentResult.retainedWireImage plannedWire _)) _ =
      targetWire
    have forwardRoundTrip :=
      forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        middleWire middleRetained
    have realExact : targetIso.wires.symm
        (forward.argumentResult.retainedWireImage plannedWire
          plannedRetained) =
          realWire := by
      calc
        _ = targetIso.wires.symm middleWire :=
          congrArg targetIso.wires.symm forwardRoundTrip
        _ = realWire := targetIso.wires.left_inv realWire
    have backwardRoundTrip :=
      backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        targetWire targetRetained
    exact (backward.argumentResult.retainedWireImage_congr _ _ _ _
      realExact).trans backwardRoundTrip

/-- The construction-owned arity wire maps cancel on planned source wires. -/
theorem inverseTransportWire_right_inv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (sourceWire : planned.val.WireId) :
    forward.inverseTransportWireMap backward targetIso wireExact
        (forward.inverseTransportWireInverse backward targetIso wireExact
          sourceWire) = sourceWire := by
  by_cases head : sourceWire = forwardWire
  · subst sourceWire
    simp [inverseTransportWireMap, inverseTransportWireInverse]
  · let sourceRetained : sourceWire ∉
        forward.argumentResult.sourceRemovedWires := by
      rw [forward.sourceRemovedWires_exact]
      simpa [head]
    let middleWire := forward.argumentResult.retainedWireImage sourceWire
      sourceRetained
    have middleRetained : middleWire ∉
        forward.argumentResult.targetRemovedWires :=
      forward.argumentResult.retainedWireImage_not_targetRemoved sourceWire
        sourceRetained
    let realWire := targetIso.wires.symm middleWire
    have realRetained : realWire ∉
        backward.argumentResult.sourceRemovedWires := by
      intro removed
      have mapped := (forward.inverseTransport_removedWire_iff backward
        targetIso wireExact realWire).mp removed
      have exact : targetIso.wires realWire = middleWire :=
        targetIso.wires.right_inv middleWire
      rw [exact] at mapped
      exact middleRetained mapped
    let targetWire := backward.argumentResult.retainedWireImage realWire
      realRetained
    have targetRetained : targetWire ∉
        backward.argumentResult.targetRemovedWires :=
      backward.argumentResult.retainedWireImage_not_targetRemoved realWire
        realRetained
    have targetDifferent : targetWire ≠ backward.targetWire := by
      intro same
      exact targetRetained (by
        change targetWire ∈ backward.argumentResult.targetRemovedWires
        rw [backward.targetRemovedWires_exact]
        exact List.mem_cons.mpr (Or.inl same))
    unfold inverseTransportWireInverse inverseTransportWireMap
    rw [dif_neg head]
    change (if same : targetWire = backward.targetWire then forwardWire
      else _) = sourceWire
    rw [dif_neg targetDifferent]
    let recoveredRealWire :=
      backward.argumentResult.sourceWireOfRetainedTarget targetWire
        targetRetained
    have recoveredRealRetained : recoveredRealWire ∉
        backward.argumentResult.sourceRemovedWires :=
      backward.argumentResult.sourceRetainedWire_not_removed
        (backward.argumentResult.retainedBaseWireOfTarget targetWire
          targetRetained)
    have recoveredMiddleRetained : targetIso.wires recoveredRealWire ∉
        forward.argumentResult.targetRemovedWires := by
      intro removed
      exact recoveredRealRetained
        ((forward.inverseTransport_removedWire_iff backward targetIso
          wireExact recoveredRealWire).mpr removed)
    change forward.argumentResult.sourceWireOfRetainedTarget
        (targetIso.wires
          (backward.argumentResult.sourceWireOfRetainedTarget targetWire
            targetRetained)) recoveredMiddleRetained = sourceWire
    have backwardRoundTrip :=
      backward.argumentResult.sourceWireOfRetainedTarget_retainedWireImage
        realWire realRetained targetRetained
    have middleExact : targetIso.wires
        (backward.argumentResult.sourceWireOfRetainedTarget targetWire
          targetRetained) = middleWire := by
      calc
        _ = targetIso.wires realWire := congrArg targetIso.wires
          backwardRoundTrip
        _ = middleWire := targetIso.wires.right_inv middleWire
    have forwardRoundTrip :=
      forward.argumentResult.sourceWireOfRetainedTarget_retainedWireImage
        sourceWire sourceRetained middleRetained
    exact (forward.argumentResult.sourceWireOfRetainedTarget_congr _ _ _ _
      middleExact).trans forwardRoundTrip

/-- Exact wire carrier for the transported arity inverse pair. -/
def inverseTransportWireEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    Data.Finite.FiniteEquiv backward.target.val.WireId planned.val.WireId where
  toFun := forward.inverseTransportWireMap backward targetIso wireExact
  invFun := forward.inverseTransportWireInverse backward targetIso wireExact
  left_inv := forward.inverseTransportWire_left_inv backward targetIso
    wireExact
  right_inv := forward.inverseTransportWire_right_inv backward targetIso
    wireExact

/-- Region carrier of the transported inverse arity pair. -/
def inverseTransportRegionEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.RegionId
      planned.val.RegionId :=
  forward.argumentResult.inverseTransportRegionEquiv
    backward.argumentResult targetIso

/-- Node carrier of the transported inverse arity pair. -/
def inverseTransportNodeEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.NodeId planned.val.NodeId :=
  forward.argumentResult.inverseTransportNodeEquiv backward.argumentResult
    forward.targetSites backward.targetSites targetIso

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

end AppliedArityShift

end Arguments

end WirePrimitive

end VisualProof
