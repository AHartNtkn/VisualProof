import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- At the deeper of two anchor sites, one anchor value is inherited from the
outer context and the other is certified by a zero-cut route.  Together they
provide the coalescence premise required by an endpoint move. -/
theorem finishRegion_moveEndpoint_equiv_of_inherited_and_anchored
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.val.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (anchorWire localWire : Fin input.val.wireCount)
    (wirePair :
      (anchorWire = sourceWire ∧ localWire = targetWire) ∨
      (anchorWire = targetWire ∧ localWire = sourceWire))
    (anchor : Fin input.val.regionCount)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope anchor)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope anchor)
    (witness : Fin input.val.nodeCount)
    (witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs localWire
      { node := witness, port := .output })
    (witnessNe : ({ node := witness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {witnessPath : List Nat}
    (witnessRoute : Diagram.Splice.RegionRoute input.val anchor witnessRegion
      witnessPath)
    (witnessRouteZero : witnessRoute.HasCutDepth 0)
    {rels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input.val sourceWire targetWire endpoint))
    (context : EndpointMoveAwayContext input.val sourceWire targetWire endpoint
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
    (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (anchorIndex : Fin sourceContext.length)
    (anchorGet : sourceContext.get anchorIndex = anchorWire)
    (anchorValue : sourceOuter anchorIndex = model.eval term Fin.elim0) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val sourceContext anchor sourceItems) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (moveEndpointRaw input.val sourceWire targetWire endpoint)
          targetContext anchor targetItems) := by
  let targetChecked : CheckedDiagram signature :=
    ⟨moveEndpointRaw input.val sourceWire targetWire endpoint, targetWellFormed⟩
  let targetWitnessRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint witnessRoute
  have targetWitnessRouteZero : targetWitnessRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      witnessRoute witnessRouteZero
  have targetWitnessShape : targetChecked.val.nodes witness =
      .term witnessRegion 0 term := by
    simpa [targetChecked] using witnessShape
  have targetWitnessOccurs : targetChecked.val.EndpointOccurs localWire
      { node := witness, port := .output } := by
    exact (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := witness, port := .output } witnessNe localWire).2 witnessOccurs
  let targetAnchorIndex : Fin targetContext.length :=
    Fin.cast (congrArg List.length context.contexts_eq) anchorIndex
  have targetAnchorGet : targetContext.get targetAnchorIndex = anchorWire := by
    have transported := List.get_of_eq context.contexts_eq anchorIndex
    have sourceToTarget : sourceContext.get anchorIndex =
        targetContext.get targetAnchorIndex := by
      simpa only [targetAnchorIndex, List.get_eq_getElem, Fin.val_cast] using
        transported
    exact sourceToTarget.symm.trans anchorGet
  have targetAnchorValue : targetOuter targetAnchorIndex =
      model.eval term Fin.elim0 := by
    have agrees := outerAgrees anchorIndex targetAnchorIndex (by
      show Fin.cast (congrArg List.length context.contexts_eq) anchorIndex =
        targetAnchorIndex
      rfl)
    exact agrees.symm.trans anchorValue
  apply finishRegion_moveEndpoint_equiv_of_coalesced input.val input.property
    sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed anchor
    sourceWireVisible targetWireVisible fuelSource fuelTarget sourceContext
    targetContext context sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    sourceItems targetItems sourceCompiled targetCompiled model named sourceOuter
    targetOuter relEnv outerAgrees
  · intro currentLocal currentDenotes sourceIndex
      targetIndex sourceGet targetGet
    have localValue : ∀ index,
        (sourceContext.extend anchor).get index = localWire →
        ConcreteElaboration.extendedEnvironment sourceContext anchor sourceOuter
            currentLocal index = model.eval term Fin.elim0 := by
      exact AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        input localWire witness witnessRegion term witnessShape witnessOccurs
        witnessRoute witnessRouteZero sourceContext sourceBinders fuelSource
        sourceItems sourceCompiled sourceExact sourceCover sourceEnumeration model
        named sourceOuter currentLocal relEnv currentDenotes
    have anchorValueAt : ∀ index,
        (sourceContext.extend anchor).get index = anchorWire →
        ConcreteElaboration.extendedEnvironment sourceContext anchor sourceOuter
            currentLocal index = model.eval term Fin.elim0 := by
      intro index indexGet
      have chosenGet : (sourceContext.extend anchor).get
          (sourceContext.outerIndex anchor anchorIndex) = anchorWire := by
        simpa only [List.get_eq_getElem] using
          (sourceContext.extend_outer anchor anchorIndex).trans anchorGet
      have indexEq : index = sourceContext.outerIndex anchor anchorIndex := by
        apply Fin.ext
        exact (List.getElem_inj sourceExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using indexGet.trans chosenGet.symm)
      rw [indexEq, moveEndpointRaw_extendedEnvironment_outer]
      exact anchorValue
    rcases wirePair with pair | pair
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (anchorValueAt sourceIndex sourceGet).trans
        (localValue targetIndex targetGet).symm
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (localValue sourceIndex sourceGet).trans
        (anchorValueAt targetIndex targetGet).symm
  · intro currentLocal currentDenotes sourceIndex
      targetIndex sourceGet targetGet
    have localValue : ∀ index,
        (targetContext.extend anchor).get index = localWire →
        ConcreteElaboration.extendedEnvironment targetContext anchor targetOuter
            currentLocal index = model.eval term Fin.elim0 := by
      exact AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        targetChecked localWire witness witnessRegion term targetWitnessShape
        targetWitnessOccurs targetWitnessRoute targetWitnessRouteZero targetContext
        targetBinders fuelTarget targetItems targetCompiled targetExact targetCover
        targetEnumeration model named targetOuter currentLocal relEnv
        currentDenotes
    have anchorValueAt : ∀ index,
        (targetContext.extend anchor).get index = anchorWire →
        ConcreteElaboration.extendedEnvironment targetContext anchor targetOuter
            currentLocal index = model.eval term Fin.elim0 := by
      intro index indexGet
      have chosenGet : (targetContext.extend anchor).get
          (targetContext.outerIndex anchor targetAnchorIndex) = anchorWire := by
        simpa only [List.get_eq_getElem] using
          (targetContext.extend_outer anchor targetAnchorIndex).trans targetAnchorGet
      have indexEq : index = targetContext.outerIndex anchor targetAnchorIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using indexGet.trans chosenGet.symm)
      rw [indexEq, moveEndpointRaw_extendedEnvironment_outer]
      exact targetAnchorValue
    rcases wirePair with pair | pair
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (anchorValueAt sourceIndex sourceGet).trans
        (localValue targetIndex targetGet).symm
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (localValue sourceIndex sourceGet).trans
        (anchorValueAt targetIndex targetGet).symm

end AnchoredWireContractSoundness

end VisualProof.Rule
