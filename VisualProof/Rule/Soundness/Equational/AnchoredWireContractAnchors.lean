import VisualProof.Rule.Soundness.Equational.AnchoredWireContractInherited

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- When both certified anchors are available at the same compiler site, their
zero-cut equations and the checked closed-term conversion coalesce the two wire
values directly. -/
theorem finishRegion_moveEndpoint_equiv_of_two_anchors
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.val.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (anchor : Fin input.val.regionCount)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope anchor)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope anchor)
    (sourceWitness targetWitness : Fin input.val.nodeCount)
    (sourceWitnessRegion targetWitnessRegion : Fin input.val.regionCount)
    (sourceTerm targetTerm : Lambda.Term 0 (Fin 0))
    (sourceWitnessShape : input.val.nodes sourceWitness =
      .term sourceWitnessRegion 0 sourceTerm)
    (targetWitnessShape : input.val.nodes targetWitness =
      .term targetWitnessRegion 0 targetTerm)
    (sourceWitnessOccurs : input.val.EndpointOccurs sourceWire
      { node := sourceWitness, port := .output })
    (targetWitnessOccurs : input.val.EndpointOccurs targetWire
      { node := targetWitness, port := .output })
    (sourceWitnessNe : ({ node := sourceWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    (targetWitnessNe : ({ node := targetWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {sourcePath targetPath : List Nat}
    (sourceRoute : Diagram.Splice.RegionRoute input.val anchor sourceWitnessRegion
      sourcePath)
    (targetRoute : Diagram.Splice.RegionRoute input.val anchor targetWitnessRegion
      targetPath)
    (sourceRouteZero : sourceRoute.HasCutDepth 0)
    (targetRouteZero : targetRoute.HasCutDepth 0)
    {rels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input.val sourceWire targetWire endpoint))
    (moveContext : EndpointMoveAwayContext input.val sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input.val sourceWire targetWire endpoint) rels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers anchor)
    (targetCover : targetBinders.Covers anchor)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input.val
      sourceBinders anchor)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      targetBinders anchor)
    (sourceExact : (sourceContext.extend anchor).Exact anchor)
    (targetExact : (targetContext.extend anchor).Exact anchor)
    (sourceItems : ItemSeq signature (sourceContext.extend anchor).length rels)
    (targetItems : ItemSeq signature (targetContext.extend anchor).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (sourceContext.extend anchor) sourceBinders
      (ConcreteElaboration.localOccurrences input.val anchor) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint) fuelTarget)
      (targetContext.extend anchor) targetBinders
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint) anchor) =
        some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin sourceContext.length → model.Carrier)
    (targetOuter : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : moveContext.indexRelation.EnvironmentsAgree
      sourceOuter targetOuter)
    (termValues : model.eval sourceTerm Fin.elim0 =
      model.eval targetTerm Fin.elim0) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val sourceContext anchor sourceItems) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (moveEndpointRaw input.val sourceWire targetWire endpoint)
          targetContext anchor targetItems) := by
  let targetChecked : CheckedDiagram signature :=
    ⟨moveEndpointRaw input.val sourceWire targetWire endpoint, targetWellFormed⟩
  let movedSourceRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint sourceRoute
  let movedTargetRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint targetRoute
  have movedSourceZero : movedSourceRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      sourceRoute sourceRouteZero
  have movedTargetZero : movedTargetRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      targetRoute targetRouteZero
  have movedSourceShape : targetChecked.val.nodes sourceWitness =
      .term sourceWitnessRegion 0 sourceTerm := by
    simpa [targetChecked] using sourceWitnessShape
  have movedTargetShape : targetChecked.val.nodes targetWitness =
      .term targetWitnessRegion 0 targetTerm := by
    simpa [targetChecked] using targetWitnessShape
  have movedSourceOccurs : targetChecked.val.EndpointOccurs sourceWire
      { node := sourceWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := sourceWitness, port := .output } sourceWitnessNe sourceWire).2
        sourceWitnessOccurs
  have movedTargetOccurs : targetChecked.val.EndpointOccurs targetWire
      { node := targetWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := targetWitness, port := .output } targetWitnessNe targetWire).2
        targetWitnessOccurs
  apply finishRegion_moveEndpoint_equiv_of_coalesced input.val input.property
    sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed anchor
    sourceWireVisible targetWireVisible fuelSource fuelTarget sourceContext
    targetContext moveContext sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    sourceItems targetItems sourceCompiled targetCompiled model named sourceOuter
    targetOuter relEnv outerAgrees
  · intro sourceLocal sourceDenotes sourceIndex targetIndex sourceGet targetGet
    have sourceValue :=
      AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route input
        sourceWire sourceWitness sourceWitnessRegion sourceTerm sourceWitnessShape
        sourceWitnessOccurs sourceRoute sourceRouteZero sourceContext sourceBinders
        fuelSource sourceItems sourceCompiled sourceExact sourceCover
        sourceEnumeration model named sourceOuter sourceLocal relEnv sourceDenotes
        sourceIndex sourceGet
    have targetValue :=
      AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route input
        targetWire targetWitness targetWitnessRegion targetTerm targetWitnessShape
        targetWitnessOccurs targetRoute targetRouteZero sourceContext sourceBinders
        fuelSource sourceItems sourceCompiled sourceExact sourceCover
        sourceEnumeration model named sourceOuter sourceLocal relEnv sourceDenotes
        targetIndex targetGet
    exact sourceValue.trans (termValues.trans targetValue.symm)
  · intro targetLocal targetDenotes sourceIndex targetIndex sourceGet targetGet
    have sourceValue :=
      AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        targetChecked sourceWire sourceWitness sourceWitnessRegion sourceTerm
        movedSourceShape movedSourceOccurs movedSourceRoute movedSourceZero
        targetContext targetBinders fuelTarget targetItems targetCompiled targetExact
        targetCover targetEnumeration model named targetOuter targetLocal relEnv
        targetDenotes sourceIndex sourceGet
    have targetValue :=
      AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        targetChecked targetWire targetWitness targetWitnessRegion targetTerm
        movedTargetShape movedTargetOccurs movedTargetRoute movedTargetZero
        targetContext targetBinders fuelTarget targetItems targetCompiled targetExact
        targetCover targetEnumeration model named targetOuter targetLocal relEnv
        targetDenotes targetIndex targetGet
    exact sourceValue.trans (termValues.trans targetValue.symm)

end AnchoredWireContractSoundness

end VisualProof.Rule
