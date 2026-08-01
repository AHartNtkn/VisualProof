import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

namespace AppliedArityShift

private theorem eraseAt_append_last (values : List α) (value : α) :
    ConcreteWirePrimitive.eraseAt (values ++ [value]) values.length =
      values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [ConcreteWirePrimitive.eraseAt, induction]

private theorem endpoint_eq
    {left right : CEndpoint nodeCount}
    (nodeExact : left.node = right.node)
    (portExact : left.port = right.port) : left = right := by
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          cases nodeExact
          cases portExact
          rfl

private theorem eraseAt_getElem?_before
    (values : List α) (position index : Nat)
    (before : index < position) :
    (ConcreteWirePrimitive.eraseAt values position)[index]? =
      values[index]? := by
  induction values generalizing position index with
  | nil => cases position <;> simp [ConcreteWirePrimitive.eraseAt]
  | cons head tail induction =>
      cases position with
      | zero => omega
      | succ position =>
          cases index with
          | zero => rfl
          | succ index =>
              simp only [Nat.succ_lt_succ_iff] at before
              simpa [ConcreteWirePrimitive.eraseAt] using
                induction position index before

/-- The suffix isomorphism identifies the real unshift source signature with
the exact shift target signature. -/
theorem inverseSourceArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.sourceArgumentList =
      forward.sourceArgumentList ++ [newArgument] := by
  have signatureExact := targetIso.wire_signature backwardWire
  rw [wireExact, forward.targetWire_signature,
    backward.sourceWire_signature] at signatureExact
  exact Sig.rel.inj signatureExact.symm

/-- Shift followed by its checked unshift restores the planned relation
argument vector exactly. -/
theorem inverseTargetArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.argumentResult.targetArguments =
      forward.sourceArgumentList := by
  rw [backward.targetArguments_exact,
    forward.inverseSourceArguments_exact backward targetIso wireExact]
  exact eraseAt_append_last forward.sourceArgumentList newArgument

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

/-- The transported node carrier sends each rebuilt unshift node to its
exact planned source-site node. -/
theorem inverseTransport_targetNode
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
    forward.inverseTransportNodeEquiv backward targetIso
        (backward.argumentResult.targetNode site) =
      (forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node := by
  let backwardNode := (backward.sourceSites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage :
      backward.argumentResult.nodeEquiv backward.targetSites backwardNode =
        backward.argumentResult.targetNode site := by
    unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.argumentResult.nodeImage backwardNode = _
    unfold ConcreteWirePrimitive.ArgumentResult.nodeImage
    have backwardMemberRaw : backwardNode ∈
        ConcreteWirePrimitive.argumentSiteNodes
          backward.argumentResult.sites := backwardMember
    rw [dif_pos backwardMemberRaw]
    change backward.argumentResult.targetNode
        (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          backward.argumentResult.sites
          (backward.argumentResult.sites.sites.get site).node _) = _
    rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse :
      (backward.argumentResult.nodeEquiv backward.targetSites).symm
          (backward.argumentResult.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact (backward.argumentResult.nodeEquiv
      backward.targetSites).left_inv backwardNode
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedNode := (forward.sourceSites.sites.get plannedPosition).node
  have plannedMember : plannedNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.sourceSites.sites.get plannedPosition,
        List.get_mem _ _, rfl⟩
  have forwardImage :
      forward.argumentResult.nodeEquiv forward.targetSites plannedNode =
        forward.argumentResult.targetNode plannedPosition := by
    unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.argumentResult.nodeImage plannedNode = _
    unfold ConcreteWirePrimitive.ArgumentResult.nodeImage
    have plannedMemberRaw : plannedNode ∈
        ConcreteWirePrimitive.argumentSiteNodes
          forward.argumentResult.sites := plannedMember
    rw [dif_pos plannedMemberRaw]
    change forward.argumentResult.targetNode
        (ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
          forward.argumentResult.sites
          (forward.argumentResult.sites.sites.get plannedPosition).node _) = _
    rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  unfold inverseTransportNodeEquiv
  change (forward.argumentResult.nodeEquiv forward.targetSites).symm
      (targetIso.nodes
        ((backward.argumentResult.nodeEquiv backward.targetSites).symm
          (backward.argumentResult.targetNode site))) = plannedNode
  rw [backwardInverse,
    forward.inverseTransport_middleNode backward targetIso wireExact site,
    ← forwardImage]
  exact (forward.argumentResult.nodeEquiv
    forward.targetSites).left_inv plannedNode

/-- Generated rebuilt nodes satisfy the exact restored payload law. -/
theorem inverseTransport_generated_node_table
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
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.argumentResult.targetNode site)) =
      (backward.target.val.nodes
        (backward.argumentResult.targetNode site)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  let backwardSite := backward.sourceSites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.sourceSites.sites.get plannedPosition
  have nodeExact := forward.inverseTransport_targetNode backward targetIso
    wireExact site
  have backwardTargetData : backward.target.val.nodes
      (backward.argumentResult.targetNode site) =
        .atom (backward.argumentResult.regionImage backwardSite.region)
          backward.argumentResult.targetArguments :=
    backward.argumentResult.targetNode_data site
  rw [nodeExact, plannedSite.node_data, backwardTargetData]
  have targetNodeExact := forward.inverseTransport_middleNode backward
    targetIso wireExact site
  have mappedData := targetIso.node_table backwardSite.node
  rw [backwardSite.node_data, targetNodeExact] at mappedData
  have forwardTargetData : forward.target.val.nodes
      (forward.argumentResult.targetNode plannedPosition) =
        .atom (forward.argumentResult.regionImage plannedSite.region)
          forward.argumentResult.targetArguments :=
    forward.argumentResult.targetNode_data plannedPosition
  rw [forwardTargetData] at mappedData
  have regionExact : forward.argumentResult.regionImage plannedSite.region =
      targetIso.regions backwardSite.region :=
    (CNode.atom.inj mappedData).1
  rw [forward.inverseTargetArguments_exact backward targetIso wireExact]
  have plannedArguments : plannedSite.argumentSignatures =
      forward.sourceArgumentList :=
    ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
      forward.sourceArgumentList forward.sourceWire_signature plannedSite
  rw [plannedArguments]
  congr 2
  unfold inverseTransportRegionEquiv
  rw [backward.argumentResult.regionImage_exact]
  have backwardCancel := backward.argumentResult.regionEquiv.left_inv
    backwardSite.region
  calc
    plannedSite.region = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionEquiv plannedSite.region) :=
      (forward.argumentResult.regionEquiv.left_inv plannedSite.region).symm
    _ = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionImage plannedSite.region) := by
      rw [forward.argumentResult.regionImage_exact]
    _ = forward.argumentResult.regionEquiv.symm
        (targetIso.regions backwardSite.region) :=
      congrArg forward.argumentResult.regionEquiv.symm regionExact
    _ = forward.argumentResult.regionEquiv.symm
        (targetIso.regions
          (backward.argumentResult.regionEquiv.symm
            (backward.argumentResult.regionEquiv backwardSite.region))) :=
              congrArg (fun value => forward.argumentResult.regionEquiv.symm
        (targetIso.regions value)) backwardCancel.symm

/-- Retained rebuilt nodes satisfy the exact transported payload law. -/
theorem inverseTransport_retained_node_table
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
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.argumentResult.retainedNodeImage realNode retained)) =
      (backward.target.val.nodes
        (backward.argumentResult.retainedNodeImage realNode retained)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  have middleRetained := forward.inverseTransport_middleNode_retained
    backward targetIso wireExact realNode retained
  let plannedNode := forward.argumentResult.sourceNodeOfRetainedTarget
    forward.targetSites (targetIso.nodes realNode) middleRetained
  have plannedRetained : plannedNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites :=
    ConcreteWirePrimitive.sourceRetainedNode_not_removed
      forward.sourceSites
      (forward.argumentResult.retainedBaseNodeOfTarget forward.targetSites
        (targetIso.nodes realNode) middleRetained)
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let forwardNodes := forward.argumentResult.nodeEquiv forward.targetSites
  have backwardImage : backwardNodes realNode =
      backward.argumentResult.retainedNodeImage realNode retained := by
    unfold backwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.argumentResult.nodeImage realNode = _
    have retainedRaw : realNode ∉
        ConcreteWirePrimitive.argumentSiteNodes
          backward.argumentResult.sites := retained
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retainedRaw]
  have backwardInverse : backwardNodes.symm
      (backward.argumentResult.retainedNodeImage realNode retained) =
        realNode := by
    rw [← backwardImage]
    exact backwardNodes.left_inv realNode
  have forwardInverse : forwardNodes.symm
      (targetIso.nodes realNode) = plannedNode := by
    unfold forwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.argumentResult.sourceNode forward.targetSites
      (targetIso.nodes realNode) = plannedNode
    unfold ConcreteWirePrimitive.ArgumentResult.sourceNode
    split
    next generated => exact (middleRetained generated).elim
    next _ => rfl
  have carrierExact : forward.inverseTransportNodeEquiv backward targetIso
      (backward.argumentResult.retainedNodeImage realNode retained) =
        plannedNode := by
    unfold inverseTransportNodeEquiv
    change forwardNodes.symm
      (targetIso.nodes
        (backwardNodes.symm
          (backward.argumentResult.retainedNodeImage realNode retained))) = _
    rw [backwardInverse, forwardInverse]
  rw [carrierExact]
  have backwardData : backward.target.val.nodes
      (backward.argumentResult.retainedNodeImage realNode retained) =
        (real.val.nodes realNode).rename
          backward.argumentResult.regionEquiv :=
    backward.argumentResult.retainedNodeImage_data realNode retained
  rw [backwardData]
  have forwardImage : forward.argumentResult.retainedNodeImage plannedNode
      plannedRetained = targetIso.nodes realNode :=
    forward.argumentResult.retainedNodeImage_sourceNodeOfRetainedTarget
      forward.targetSites (targetIso.nodes realNode) middleRetained
  have forwardData : forward.target.val.nodes (targetIso.nodes realNode) =
      (planned.val.nodes plannedNode).rename
        forward.argumentResult.regionEquiv := by
    rw [← forwardImage]
    exact forward.argumentResult.retainedNodeImage_data plannedNode
      plannedRetained
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
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          exact (forward.argumentResult.regionEquiv.left_inv
              plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              parts.1).trans
              (congrArg (fun value =>
                forward.argumentResult.regionEquiv.symm
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
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          exact (forward.argumentResult.regionEquiv.left_inv
              plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              parts.1).trans
              (congrArg (fun value =>
                forward.argumentResult.regionEquiv.symm
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
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          exact (forward.argumentResult.regionEquiv.left_inv
              plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              parts.1).trans
              (congrArg (fun value =>
                forward.argumentResult.regionEquiv.symm
                  (targetIso.regions value)) backwardCancel.symm))

/-- Complete node-table law for the transported arity inverse carrier. -/
theorem inverseTransport_node_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {newArgument : Sig}
    (forward : AppliedArityShift planned forwardWire newArgument)
    {backwardWire : real.val.WireId}
    (backward : AppliedArityUnshift real backwardWire
      forward.sourceArgumentList.length)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (node : backward.target.val.NodeId) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso node) =
      (backward.target.val.nodes node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let backwardNodes := backward.argumentResult.nodeEquiv backward.targetSites
  let realNode := backwardNodes.symm node
  have nodeRecover : backwardNodes realNode = node :=
    backwardNodes.right_inv node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
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
    have nodeExact : node = backward.argumentResult.targetNode site :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_generated_node_table backward
      targetIso wireExact site
  · have imageExact : backwardNodes realNode =
        backward.argumentResult.retainedNodeImage realNode generated := by
      unfold backwardNodes ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.argumentResult.nodeImage realNode = _
      have generatedRaw : realNode ∉
          ConcreteWirePrimitive.argumentSiteNodes
            backward.argumentResult.sites := generated
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_neg generatedRaw]
    have nodeExact : node =
        backward.argumentResult.retainedNodeImage realNode generated :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_retained_node_table backward
      targetIso wireExact realNode generated

/-- Complete wire-signature law for the construction-owned arity carrier. -/
theorem inverseTransport_wire_signature
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
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso wireExact
        targetWire)).sig =
      (backward.target.val.wires targetWire).sig := by
  by_cases head : targetWire = backward.targetWire
  · subst targetWire
    change (planned.val.wires
      (forward.inverseTransportWireMap backward targetIso wireExact
        backward.targetWire)).sig = _
    rw [show forward.inverseTransportWireMap backward targetIso wireExact
        backward.targetWire = forwardWire by
      simp [inverseTransportWireMap]]
    rw [forward.sourceWire_signature]
    change Sig.rel forward.sourceArgumentList =
      (backward.argumentResult.checked.val.wires
        backward.argumentResult.targetWire).sig
    rw [
      backward.argumentResult.targetWire_signature,
      forward.inverseTargetArguments_exact backward targetIso wireExact]
  · have targetRetained : targetWire ∉
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
    have backwardImage :
        backward.argumentResult.retainedWireImage realWire realRetained =
          targetWire :=
      backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        targetWire targetRetained
    let middleWire := targetIso.wires realWire
    have middleRetained : middleWire ∉
        forward.argumentResult.targetRemovedWires := by
      intro removed
      exact realRetained
        ((forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mpr removed)
    let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
      middleWire middleRetained
    have plannedRetained : plannedWire ∉
        forward.argumentResult.sourceRemovedWires :=
      forward.argumentResult.sourceRetainedWire_not_removed
        (forward.argumentResult.retainedBaseWireOfTarget middleWire
          middleRetained)
    have forwardImage :
        forward.argumentResult.retainedWireImage plannedWire
          plannedRetained = middleWire :=
      forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        middleWire middleRetained
    have carrierExact :
        forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire = plannedWire := by
      change forward.inverseTransportWireMap backward targetIso wireExact
        targetWire = plannedWire
      unfold inverseTransportWireMap
      rw [dif_neg head]
    calc
      (planned.val.wires
          (forward.inverseTransportWireEquiv backward targetIso wireExact
            targetWire)).sig =
          (planned.val.wires plannedWire).sig := by rw [carrierExact]
      _ = (forward.target.val.wires middleWire).sig := by
        rw [← forwardImage]
        exact (forward.argumentResult.retainedWireImage_signature
          plannedWire plannedRetained).symm
      _ = (real.val.wires realWire).sig :=
        targetIso.wire_signature realWire
      _ = (backward.target.val.wires targetWire).sig := by
        rw [← backwardImage]
        exact (backward.argumentResult.retainedWireImage_signature
          realWire realRetained).symm

/-- Complete wire-scope law for the construction-owned arity carrier. -/
theorem inverseTransport_wire_scope
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
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso wireExact
        targetWire)).scope =
      forward.inverseTransportRegionEquiv backward targetIso
        (backward.target.val.wires targetWire).scope := by
  by_cases head : targetWire = backward.targetWire
  · subst targetWire
    have backwardScope :=
      backward.argumentResult.targetWire_scope_regionImage
    have forwardScope := forward.argumentResult.targetWire_scope_regionImage
    have forwardScopePublic :
        (forward.target.val.wires forward.targetWire).scope =
          forward.argumentResult.regionImage
            (planned.val.wires forwardWire).scope := forwardScope
    have middleScope := targetIso.wire_scope backwardWire
    rw [wireExact] at middleScope
    change (planned.val.wires
      (forward.inverseTransportWireMap backward targetIso wireExact
        backward.targetWire)).scope = _
    rw [show forward.inverseTransportWireMap backward targetIso wireExact
        backward.targetWire = forwardWire by
      simp [inverseTransportWireMap]]
    change (planned.val.wires forwardWire).scope =
      forward.argumentResult.regionEquiv.symm
        (targetIso.regions
          (backward.argumentResult.regionEquiv.symm
            (backward.argumentResult.checked.val.wires
              backward.argumentResult.targetWire).scope))
    rw [backwardScope, backward.argumentResult.regionImage_exact]
    have backwardCancel := backward.argumentResult.regionEquiv.left_inv
      (real.val.wires backwardWire).scope
    calc
      (planned.val.wires forwardWire).scope =
          forward.argumentResult.regionEquiv.symm
            (forward.argumentResult.regionEquiv
              (planned.val.wires forwardWire).scope) :=
        (forward.argumentResult.regionEquiv.left_inv _).symm
      _ = forward.argumentResult.regionEquiv.symm
          (forward.target.val.wires forward.targetWire).scope := by
        rw [forwardScopePublic,
          forward.argumentResult.regionImage_exact]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions (real.val.wires backwardWire).scope) := by
        rw [middleScope]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions
            (backward.argumentResult.regionEquiv.symm
              (backward.argumentResult.regionEquiv
                (real.val.wires backwardWire).scope))) :=
        congrArg (fun value => forward.argumentResult.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm

  · have targetRetained : targetWire ∉
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
    have backwardImage :
        backward.argumentResult.retainedWireImage realWire realRetained =
          targetWire :=
      backward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        targetWire targetRetained
    let middleWire := targetIso.wires realWire
    have middleRetained : middleWire ∉
        forward.argumentResult.targetRemovedWires := by
      intro removed
      exact realRetained
        ((forward.inverseTransport_removedWire_iff backward targetIso
          wireExact realWire).mpr removed)
    let plannedWire := forward.argumentResult.sourceWireOfRetainedTarget
      middleWire middleRetained
    have plannedRetained : plannedWire ∉
        forward.argumentResult.sourceRemovedWires :=
      forward.argumentResult.sourceRetainedWire_not_removed
        (forward.argumentResult.retainedBaseWireOfTarget middleWire
          middleRetained)
    have forwardImage :
        forward.argumentResult.retainedWireImage plannedWire
          plannedRetained = middleWire :=
      forward.argumentResult.retainedWireImage_sourceWireOfRetainedTarget
        middleWire middleRetained
    have carrierExact :
        forward.inverseTransportWireEquiv backward targetIso wireExact
          targetWire = plannedWire := by
      change forward.inverseTransportWireMap backward targetIso wireExact
        targetWire = plannedWire
      unfold inverseTransportWireMap
      rw [dif_neg head]
    have backwardScope :=
      backward.argumentResult.retainedWireImage_scope realWire realRetained
    rw [backwardImage] at backwardScope
    have backwardScopePublic :
        (backward.target.val.wires targetWire).scope =
          backward.argumentResult.regionImage
            (real.val.wires realWire).scope := backwardScope
    have forwardScope :=
      forward.argumentResult.retainedWireImage_scope plannedWire
        plannedRetained
    rw [forwardImage] at forwardScope
    have forwardScopePublic :
        (forward.target.val.wires middleWire).scope =
          forward.argumentResult.regionImage
            (planned.val.wires plannedWire).scope := forwardScope
    have middleScope := targetIso.wire_scope realWire
    rw [carrierExact]
    change (planned.val.wires plannedWire).scope =
      forward.argumentResult.regionEquiv.symm
        (targetIso.regions
          (backward.argumentResult.regionEquiv.symm
            (backward.target.val.wires targetWire).scope))
    rw [backwardScopePublic,
      backward.argumentResult.regionImage_exact]
    have backwardCancel := backward.argumentResult.regionEquiv.left_inv
      (real.val.wires realWire).scope
    calc
      (planned.val.wires plannedWire).scope =
          forward.argumentResult.regionEquiv.symm
            (forward.argumentResult.regionEquiv
              (planned.val.wires plannedWire).scope) :=
        (forward.argumentResult.regionEquiv.left_inv _).symm
      _ = forward.argumentResult.regionEquiv.symm
          (forward.target.val.wires middleWire).scope := by
        rw [forwardScopePublic,
          forward.argumentResult.regionImage_exact]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions (real.val.wires realWire).scope) := by
        rw [middleScope]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions
            (backward.argumentResult.regionEquiv.symm
              (backward.argumentResult.regionEquiv
                (real.val.wires realWire).scope))) :=
        congrArg (fun value => forward.argumentResult.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm

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
          sourceArgs, eraseAt_append_last] at indexBound
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
      eraseAt_append_last] at indexBound
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
    rw [eraseAt_getElem?_before]
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
    exact endpoint_eq backwardRecover rfl
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
      exact endpoint_eq backwardRecover rfl
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
      exact endpoint_eq backwardRecover rfl

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
      exact endpoint_eq forwardCancel rfl

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
