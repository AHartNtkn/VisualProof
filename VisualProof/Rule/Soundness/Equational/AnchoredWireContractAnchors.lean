import VisualProof.Rule.Soundness.Equational.AnchoredWireContractInherited

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- The two executor-certified anchor sites, oriented from the shallower site
to the deeper site for one moved endpoint.  This packages both comparable-scope
branches without changing the Boolean availability contract. -/
structure EndpointAnchorOrder
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (availability : AnchoredWireSoundness.SplitAvailability input keep
      survivorRegion (input.val.nodes endpoint.node).region) where
  shallow : Fin input.val.regionCount
  deep : Fin input.val.regionCount
  anchorWire : Fin input.val.wireCount
  localWire : Fin input.val.wireCount
  wirePair :
    (anchorWire = drop ∧ localWire = keep) ∨
      (anchorWire = keep ∧ localWire = drop)
  anchorWire_encloses_shallow :
    input.val.Encloses (input.val.wires anchorWire).scope shallow
  drop_visible_deep : input.val.Encloses (input.val.wires drop).scope deep
  keep_visible_deep : input.val.Encloses (input.val.wires keep).scope deep
  deep_encloses_endpoint :
    input.val.Encloses deep (input.val.nodes endpoint.node).region
  routePath : List Nat
  route : Diagram.Splice.RegionRoute input.val shallow deep routePath
  anchorWitnessPath : List Nat
  anchorWitnessRegion : Fin input.val.regionCount
  anchorWitnessRoute : Diagram.Splice.RegionRoute input.val shallow
    anchorWitnessRegion anchorWitnessPath
  anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0
  localWitnessPath : List Nat
  localWitnessRegion : Fin input.val.regionCount
  localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
    localWitnessRegion localWitnessPath
  localWitnessZero : localWitnessRoute.HasCutDepth 0

/-- Construct the oriented anchor order from exactly the successful executor's
scope-comparability and zero-route receipts. -/
theorem endpointAnchorOrder_exists
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (survivorRegion : Fin input.val.regionCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (member : endpoint ∈ movedEndpoints input redundant drop)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (availability : AnchoredWireSoundness.SplitAvailability input keep
      survivorRegion (input.val.nodes endpoint.node).region) :
    Nonempty (EndpointAnchorOrder input redundant drop keep redundantRegion
      survivorRegion endpoint availability) := by
  obtain ⟨redundantPath, redundantRoute, redundantZero⟩ :=
    redundant_zero_route input redundant redundantRegion redundantTerm drop
      redundantShape redundantOccurs sameDepth
  obtain ⟨survivorPath, survivorRoute, survivorZero⟩ :=
    availability.witness_zero_route
  rcases movedEndpoint_scopes_comparable input redundant drop keep survivorRegion
      member availability with dropAbove | survivorAbove
  · obtain ⟨routePath, ⟨route⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val
        (input.val.wires drop).scope availability.available dropAbove
    exact ⟨{
      shallow := (input.val.wires drop).scope
      deep := availability.available
      anchorWire := drop
      localWire := keep
      wirePair := Or.inl ⟨rfl, rfl⟩
      anchorWire_encloses_shallow := ⟨0, rfl⟩
      drop_visible_deep := dropAbove
      keep_visible_deep := availability.wire_encloses
      deep_encloses_endpoint := availability.target_inside
      routePath := routePath
      route := route
      anchorWitnessPath := redundantPath
      anchorWitnessRegion := redundantRegion
      anchorWitnessRoute := redundantRoute
      anchorWitnessZero := redundantZero
      localWitnessPath := survivorPath
      localWitnessRegion := survivorRegion
      localWitnessRoute := survivorRoute
      localWitnessZero := survivorZero
    }⟩
  · obtain ⟨routePath, ⟨route⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val
        availability.available (input.val.wires drop).scope survivorAbove
    have dropEnclosesEndpoint : input.val.Encloses
        (input.val.wires drop).scope (input.val.nodes endpoint.node).region :=
      input.property.wire_scopes_enclose drop endpoint
        (movedEndpoints_mem_occurs input redundant drop member)
    exact ⟨{
      shallow := availability.available
      deep := (input.val.wires drop).scope
      anchorWire := keep
      localWire := drop
      wirePair := Or.inr ⟨rfl, rfl⟩
      anchorWire_encloses_shallow := availability.wire_encloses
      drop_visible_deep := ⟨0, rfl⟩
      keep_visible_deep := ConcreteElaboration.checked_encloses_trans
        input.property availability.wire_encloses survivorAbove
      deep_encloses_endpoint := dropEnclosesEndpoint
      routePath := routePath
      route := route
      anchorWitnessPath := survivorPath
      anchorWitnessRegion := survivorRegion
      anchorWitnessRoute := survivorRoute
      anchorWitnessZero := survivorZero
      localWitnessPath := redundantPath
      localWitnessRegion := redundantRegion
      localWitnessRoute := redundantRoute
      localWitnessZero := redundantZero
    }⟩

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
