import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRaw

namespace VisualProof

namespace ConcreteWireQuantifier

private def eraseWireNodes
    (source : CheckedDiagram definitions) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (node ∉ ([] : List source.val.NodeId))

private def eraseWireSourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (target :
      (ConcreteDiagram.DenseErasure.eraseWireCandidate
        source removed).NodeId) :
    source.val.NodeId :=
  (eraseWireNodes source).get target

private def eraseWireTargetNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    (ConcreteDiagram.DenseErasure.eraseWireCandidate
      source removed).NodeId :=
  (Data.Finite.indexOf? (eraseWireNodes source) node).get
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      simp [eraseWireNodes, ConcreteDiagram.nodesList,
        Data.Finite.mem_allFin]))

@[simp] private theorem eraseWireSourceNode_target
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    eraseWireSourceNode source removed
        (eraseWireTargetNode source removed node) =
      node := by
  unfold eraseWireSourceNode eraseWireTargetNode
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      simp [eraseWireNodes, ConcreteDiagram.nodesList,
        Data.Finite.mem_allFin]))

private def eraseWireSourceEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (endpoint :
      CEndpoint
        (ConcreteDiagram.DenseErasure.eraseWireCandidate
          source removed).nodeCount) :
    CEndpoint source.val.nodeCount :=
  ⟨eraseWireSourceNode source removed endpoint.node, endpoint.port⟩

private theorem eraseWireCandidate_target_requiredPorts
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    (ConcreteDiagram.DenseErasure.eraseWireCandidate
        source removed).requiredPorts
          (eraseWireTargetNode source removed node) =
      source.val.requiredPorts node := by
  have nodeExact :
      (eraseWireNodes source).get
          (eraseWireTargetNode source removed node) =
        node :=
    eraseWireSourceNode_target source removed node
  unfold ConcreteDiagram.requiredPorts
  cases sourceNodeEq : source.val.nodes node <;>
    simp only [eraseWireNodes, eraseWireTargetNode,
      ConcreteDiagram.DenseErasure.eraseWireCandidate] at nodeExact ⊢ <;>
    simp only [nodeExact, sourceNodeEq]

private theorem eraseWireCandidate_endpoint_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWire :
      (ConcreteDiagram.DenseErasure.eraseWireCandidate
        source removed).WireId)
    (endpoint :
      CEndpoint
        (ConcreteDiagram.DenseErasure.eraseWireCandidate
          source removed).nodeCount)
    (incident :
      endpoint ∈
        ((ConcreteDiagram.DenseErasure.eraseWireCandidate
          source removed).wires targetWire).endpoints) :
    eraseWireSourceEndpoint source removed endpoint ∈
      (source.val.wires
        ((ConcreteDiagram.DenseErasure.retainedWires
          source.val [removed]).get targetWire)).endpoints := by
  unfold ConcreteDiagram.DenseErasure.eraseWireCandidate at incident
  rcases List.mem_filterMap.mp incident with
    ⟨sourceEndpoint, sourceIncident, mapped⟩
  split at mapped
  · rename_i retained
    have mappedEndpoint :
        (⟨
            (Data.Finite.indexOf? (eraseWireNodes source)
              sourceEndpoint.node).get
                (Data.Finite.indexOf?_isSome_iff.mpr retained),
            sourceEndpoint.port⟩ :
          CEndpoint (eraseWireNodes source).length) =
          endpoint := Option.some.inj (by
            simpa [eraseWireNodes] using mapped)
    have sourceNode :
        sourceEndpoint.node =
          eraseWireSourceNode source removed endpoint.node := by
      have indexed :=
        Data.Finite.indexOf?_sound
          ((Option.some_get
            (Data.Finite.indexOf?_isSome_iff.mpr retained)).symm)
      have targetNodeEq := congrArg CEndpoint.node mappedEndpoint
      rw [← targetNodeEq]
      exact indexed.symm
    have sourcePort :
        sourceEndpoint.port = endpoint.port :=
      congrArg CEndpoint.port mappedEndpoint
    cases sourceEndpoint
    cases endpoint
    simp only at sourceNode sourcePort ⊢
    subst sourceNode
    subst sourcePort
    exact sourceIncident
  · simp at mapped

/--
A canonical wire erasure can be well formed only when the erased wire has no
source incidences.
-/
theorem eraseWireCandidate_wellFormed_implies_endpoints_empty
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (candidateWellFormed :
      (ConcreteDiagram.DenseErasure.eraseWireCandidate
        source removed).WellFormed definitions) :
    (source.val.wires removed).endpoints = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro endpoint incident
  let candidate :=
    ConcreteDiagram.DenseErasure.eraseWireCandidate source removed
  let targetNode : candidate.NodeId :=
    eraseWireTargetNode source removed endpoint.node
  have sourceRequired :=
    ConcreteDiagram.incident_port_required definitions source.val source.property
      removed endpoint incident
  have targetRequired :
      endpoint.port ∈ candidate.requiredPorts targetNode := by
    rw [eraseWireCandidate_target_requiredPorts]
    simpa [candidate, targetNode] using sourceRequired
  obtain ⟨targetWire, targetOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions candidate
      candidateWellFormed targetNode endpoint.port targetRequired
  have targetIncident :=
    ConcreteDiagram.endpointOwner?_incident candidate
      (⟨targetNode, endpoint.port⟩ : CEndpoint candidate.nodeCount)
      targetWire targetOwner
  let survivor :=
    (ConcreteDiagram.DenseErasure.retainedWires
      source.val [removed]).get targetWire
  have survivorIncident :
      endpoint ∈ (source.val.wires survivor).endpoints := by
    have origin :=
      eraseWireCandidate_endpoint_origin source removed targetWire
        (⟨targetNode, endpoint.port⟩ : CEndpoint candidate.nodeCount)
        targetIncident
    simpa [candidate, survivor, targetNode,
      eraseWireSourceEndpoint] using origin
  have survivorDifferent : survivor ≠ removed := by
    have member := List.get_mem
      (ConcreteDiagram.DenseErasure.retainedWires
        source.val [removed]) targetWire
    simpa [survivor,
      ConcreteDiagram.DenseErasure.retainedWires] using
        (List.mem_filter.mp member).2
  have removedOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions source.val
      source.property endpoint.node endpoint.port sourceRequired removed incident
  have survivorOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions source.val
      source.property endpoint.node endpoint.port sourceRequired survivor
      survivorIncident
  exact survivorDifferent
    (Option.some.inj (survivorOwner.symm.trans removedOwner))

namespace RelationJoinResult

@[simp] theorem bound_dying_endpoints
    (result : RelationJoinResult source wire content parameters) :
    (result.boundFinal.val.wires result.boundDying).endpoints = [] := by
  apply eraseWireCandidate_wellFormed_implies_endpoints_empty
    result.boundFinal result.boundDying
  rw [← result.final_deletion_exact]
  exact result.plainFinal.property

end RelationJoinResult

end ConcreteWireQuantifier

end VisualProof
