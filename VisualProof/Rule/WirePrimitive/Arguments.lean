import VisualProof.Rule.WirePrimitive.ArgumentsArity
import VisualProof.Rule.WirePrimitive.ArgumentsPermute
import VisualProof.Rule.WirePrimitive.ArgumentsDropExtend

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

/-- A retained endpoint is transported by an argument construction with
its port unchanged and its node carried by the construction equivalence. -/
theorem argumentResult_retainedEndpointImage_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ConcreteWirePrimitive.ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints)
    (retained : endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes result.sites) :
    (⟨result.nodeEquiv targetSites endpoint.node, endpoint.port⟩ :
      CEndpoint result.checked.val.nodeCount) ∈
      (result.checked.val.wires
        (result.retainedWireImage sourceWire (by
          intro removed
          exact retained
            (result.sourceRemovedExhausted sourceWire removed endpoint
              incident)))).endpoints := by
  let sourceRetained : sourceWire ∉ result.sourceRemovedWires := by
    intro removed
    exact retained
      (result.sourceRemovedExhausted sourceWire removed endpoint incident)
  have targetIncident := result.retainedNode_forwardIncident
    endpoint.node retained endpoint.port sourceWire incident
  have nodeExact : result.nodeEquiv targetSites endpoint.node =
      result.retainedNodeImage endpoint.node retained := by
    unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change result.nodeImage endpoint.node = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]
  have contextImage := result.contextWireMap_retained sourceWire
    sourceRetained
  rw [contextImage] at targetIncident
  simpa [nodeExact] using targetIncident

/-- Incidence on a retained rebuilt endpoint pulls back through the exact
construction carrier with its port unchanged. -/
theorem argumentResult_retainedEndpointInverse_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ConcreteWirePrimitive.ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (sourceWire : source.val.WireId)
    (sourceRetained : sourceWire ∉ result.sourceRemovedWires)
    (candidate : CEndpoint result.checked.val.nodeCount)
    (incident : candidate ∈
      (result.checked.val.wires
        (result.retainedWireImage sourceWire sourceRetained)).endpoints)
    (retained : (result.nodeEquiv targetSites).symm candidate.node ∉
      ConcreteWirePrimitive.argumentSiteNodes result.sites) :
    (⟨(result.nodeEquiv targetSites).symm candidate.node,
        candidate.port⟩ : CEndpoint source.val.nodeCount) ∈
      (source.val.wires sourceWire).endpoints := by
  let sourceNode := (result.nodeEquiv targetSites).symm candidate.node
  have nodeRecover : result.nodeEquiv targetSites sourceNode =
      candidate.node := (result.nodeEquiv targetSites).right_inv candidate.node
  have targetRequired : candidate.port ∈
      result.checked.val.requiredPorts candidate.node :=
    ConcreteDiagram.incident_port_required definitions result.checked.val
      result.checked.property (result.retainedWireImage sourceWire
        sourceRetained) candidate incident
  have targetNodeImage : result.retainedNodeImage sourceNode retained =
      candidate.node := by
    have image : result.nodeEquiv targetSites sourceNode =
        result.retainedNodeImage sourceNode retained := by
      unfold ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change result.nodeImage sourceNode = _
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]
    rw [← image]
    exact nodeRecover
  have sourceRequired : candidate.port ∈
      source.val.requiredPorts sourceNode := by
    have retainedData : result.checked.val.nodes
        (result.retainedNodeImage sourceNode retained) =
          (source.val.nodes sourceNode).rename result.regionEquiv :=
      result.retainedNodeImage_data sourceNode retained
    rw [ConcreteDiagram.requiredPorts] at targetRequired ⊢
    rw [← targetNodeImage, retainedData] at targetRequired
    cases sourceData : source.val.nodes sourceNode <;>
      simp [sourceData, CNode.rename] at targetRequired ⊢
    all_goals exact targetRequired
  obtain ⟨actualWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode candidate.port sourceRequired
  have actualRetained : actualWire ∉ result.sourceRemovedWires := by
    intro removed
    have actualIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, candidate.port⟩ actualWire sourceOwner
    exact retained (result.sourceRemovedExhausted actualWire removed
      ⟨sourceNode, candidate.port⟩ actualIncident)
  have forwardOwner := result.retainedNodeImage_endpointOwner
    sourceNode retained candidate.port sourceRequired actualWire sourceOwner
  change result.checked.val.endpointOwner?
      ⟨result.retainedNodeImage sourceNode retained, candidate.port⟩ =
        some (result.retainedWireImage actualWire actualRetained)
    at forwardOwner
  have targetOwner : result.checked.val.endpointOwner? candidate =
      some (result.retainedWireImage sourceWire sourceRetained) :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      result.checked.val result.checked.property candidate.node candidate.port
      targetRequired (result.retainedWireImage sourceWire sourceRetained)
      incident
  rw [targetNodeImage, targetOwner] at forwardOwner
  have imageExact : result.retainedWireImage actualWire actualRetained =
      result.retainedWireImage sourceWire sourceRetained :=
    (Option.some.inj forwardOwner).symm
  have actualTargetRetained :=
    result.retainedWireImage_not_targetRemoved actualWire actualRetained
  have sourceTargetRetained :=
    result.retainedWireImage_not_targetRemoved sourceWire sourceRetained
  have actualExact : actualWire = sourceWire := by
    calc
      actualWire = result.sourceWireOfRetainedTarget
          (result.retainedWireImage actualWire actualRetained)
          actualTargetRetained :=
        (result.sourceWireOfRetainedTarget_retainedWireImage actualWire
          actualRetained actualTargetRetained).symm
      _ = result.sourceWireOfRetainedTarget
          (result.retainedWireImage sourceWire sourceRetained)
          sourceTargetRetained :=
        result.sourceWireOfRetainedTarget_congr _ _ _ _ imageExact
      _ = sourceWire :=
        result.sourceWireOfRetainedTarget_retainedWireImage sourceWire
          sourceRetained sourceTargetRetained
  subst actualWire
  exact ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceNode, candidate.port⟩ sourceWire sourceOwner

end Arguments

export Arguments
  (WireArgumentError AppliedArityShift AppliedArityUnshift
    AppliedArgPermute AppliedArgDuplicate AppliedArgContract AppliedArgDrop
    AppliedArgExtend applyArityShift applyArityUnshift applyArgPermute
    applyArgDuplicate applyArgContract applyArgDrop applyArgExtend
    arity_shift_sound arity_unshift_sound arg_permute_sound
    arg_duplicate_sound arg_contract_sound arg_drop_sound arg_extend_sound)

end WirePrimitive

export WirePrimitive
  (WireArgumentError AppliedArityShift AppliedArityUnshift
    AppliedArgPermute AppliedArgDuplicate AppliedArgContract AppliedArgDrop
    AppliedArgExtend applyArityShift applyArityUnshift applyArgPermute
    applyArgDuplicate applyArgContract applyArgDrop applyArgExtend
    arity_shift_sound arity_unshift_sound arg_permute_sound
    arg_duplicate_sound arg_contract_sound arg_drop_sound arg_extend_sound)

end VisualProof
