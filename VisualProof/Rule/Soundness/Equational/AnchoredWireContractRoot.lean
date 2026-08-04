import VisualProof.Rule.Soundness.Equational.AnchoredWireContractAncestor

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

private theorem extendWireEnv_cast_lengths
    {sourceOuter targetOuter sourceLocal targetLocal : Nat}
    (ambientLength : sourceOuter = targetOuter)
    (localLength : sourceLocal = targetLocal)
    (outerEnv : Fin targetOuter → D)
    (localEnv : Fin targetLocal → D) :
    extendWireEnv (outerEnv ∘ Fin.cast ambientLength)
        (localEnv ∘ Fin.cast localLength) =
      extendWireEnv outerEnv localEnv ∘ Fin.cast (by omega) := by
  subst targetOuter
  subst targetLocal
  rfl

private theorem rootEnvironment_cast_lengths
    {source target : ConcreteDiagram}
    (sourceAmbient sourceLocals : ConcreteElaboration.WireContext source)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext target)
    (ambientLength : sourceAmbient.length = targetAmbient.length)
    (localLength : sourceLocals.length = targetLocals.length)
    (targetOuter : Fin targetAmbient.length → D)
    (targetLocal : Fin targetLocals.length → D) :
    ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
        (targetOuter ∘ Fin.cast ambientLength)
        (targetLocal ∘ Fin.cast localLength) =
      ConcreteElaboration.rootEnvironment targetAmbient targetLocals
        targetOuter targetLocal ∘ Fin.cast (by
          rw [List.length_append, List.length_append, ambientLength,
            localLength]) := by
  unfold ConcreteElaboration.rootEnvironment
  rw [extendWireEnv_cast_lengths ambientLength localLength]
  funext index
  apply congrArg (extendWireEnv targetOuter targetLocal)
  apply Fin.ext
  rfl

def endpointMoveSourceOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def endpointMoveTargetOpen (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := moveEndpointRaw input.val sourceWire targetWire endpoint
  boundary := boundary

@[simp] theorem endpointMoveTargetOpen_exposedWires
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (boundary : List (Fin input.val.wireCount)) :
    (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
      ).exposedWires = (endpointMoveSourceOpen input boundary).exposedWires := rfl

@[simp] theorem endpointMoveTargetOpen_hiddenWires
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (boundary : List (Fin input.val.wireCount)) :
    (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
      ).hiddenWires = (endpointMoveSourceOpen input boundary).hiddenWires := by
  unfold endpointMoveTargetOpen endpointMoveSourceOpen
    OpenConcreteDiagram.hiddenWires
  simp only [moveEndpointRaw_root]
  rw [moveEndpointRaw_exactScopeWires]
  rfl

@[simp] theorem endpointMoveTargetOpen_rootWires
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (boundary : List (Fin input.val.wireCount)) :
    (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
      ).rootWires = (endpointMoveSourceOpen input boundary).rootWires := by
  simp [OpenConcreteDiagram.rootWires]
  rfl

theorem endpointMoveSourceOpen_wellFormed
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (endpointMoveSourceOpen input boundary).WellFormed signature := {
  diagram_well_formed := input.property
  boundary_is_root_scoped := boundaryRoot
}

theorem endpointMoveTargetOpen_wellFormed
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature) :
    (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
      ).WellFormed signature := {
  diagram_well_formed := targetWellFormed
  boundary_is_root_scoped := by
    intro wire member
    simpa [endpointMoveTargetOpen] using boundaryRoot wire member
}

/-- Two zero-spine anchors available at the ordered-open root coalesce the
source and target wire values, so the authoritative root occurrence compiler
is invariant under one certified endpoint move. -/
theorem finishRoot_moveEndpoint_equiv_of_two_anchors
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.val.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope input.val.root)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope input.val.root)
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
    (sourceRoute : Diagram.Splice.RegionRoute input.val input.val.root
      sourceWitnessRegion sourcePath)
    (targetRoute : Diagram.Splice.RegionRoute input.val input.val.root
      targetWitnessRegion targetPath)
    (sourceRouteZero : sourceRoute.HasCutDepth 0)
    (targetRouteZero : targetRoute.HasCutDepth 0)
    (sourceItems : ItemSeq signature
      (endpointMoveSourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      (endpointMoveSourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.regionCount)
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.root) = some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outer : Fin (endpointMoveSourceOpen input boundary).exposedWires.length →
      model.Carrier)
    (termValues : model.eval sourceTerm Fin.elim0 =
      model.eval targetTerm Fin.elim0) :
    denoteRegion (relCtx := []) model named outer PUnit.unit
        (ConcreteElaboration.finishRoot
          (endpointMoveSourceOpen input boundary).exposedWires
          (endpointMoveSourceOpen input boundary).hiddenWires sourceItems) ↔
      denoteRegion (relCtx := []) model named outer PUnit.unit
        (ConcreteElaboration.finishRoot
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).exposedWires
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).hiddenWires targetItems) := by
  let source := endpointMoveSourceOpen input boundary
  let target := endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
  have sourceWellFormed := endpointMoveSourceOpen_wellFormed input boundary
    boundaryRoot
  have targetWellFormedOpen := endpointMoveTargetOpen_wellFormed input sourceWire
    targetWire endpoint boundary boundaryRoot targetWellFormed
  let sourceChecked : CheckedOpenDiagram signature := ⟨source, sourceWellFormed⟩
  let targetChecked : CheckedOpenDiagram signature :=
    ⟨target, targetWellFormedOpen⟩
  have sourceExact := OpenConcreteDiagram.rootWires_exact source sourceWellFormed
  have targetExact := OpenConcreteDiagram.rootWires_exact target targetWellFormedOpen
  have contextsEq : source.rootWires = target.rootWires := by
    exact (endpointMoveTargetOpen_rootWires input sourceWire targetWire endpoint
      boundary).symm
  have moveContext : EndpointMoveContext input.val sourceWire targetWire endpoint
      source.rootWires target.rootWires := {
    contexts_eq := contextsEq
    source_mem := (sourceExact.mem_iff sourceWire).2 sourceWireVisible
    target_mem := (sourceExact.mem_iff targetWire).2 targetWireVisible
  }
  have binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty := {
    relationContexts_eq := rfl
    binders_eq := HEq.rfl
  }
  have identityRelationRenamingEq :
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
        RelationRenaming [] []) =
          (fun {arity} (relation : RelVar [] arity) => relation) := by
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    rfl
  have semantic : ∀ direction,
      ConcreteElaboration.ItemSeqSimulation model named direction
        (endpointMoveRelation input.val sourceWire targetWire source.rootWires
          target.rootWires) sourceItems targetItems := by
    intro direction
    simpa only [identityRelationRenamingEq, ItemSeq.renameRelations_id] using
      (compileOccurrences_moveEndpoint_itemSeqSimulation input.val input.property
        sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed model
        named direction input.val.regionCount input.val.regionCount input.val.root
        source.rootWires target.rootWires moveContext sourceExact.nodup
        targetExact.nodup ConcreteElaboration.BinderContext.empty
        ConcreteElaboration.BinderContext.empty binderWitness
        (ConcreteElaboration.BinderContext.empty_covers_root input.property)
        (ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed)
        (ConcreteElaboration.BinderContext.Enumeration.empty input.val)
        (ConcreteElaboration.BinderContext.Enumeration.empty
          (moveEndpointRaw input.val sourceWire targetWire endpoint))
        sourceExact targetExact sourceItems targetItems (by
          simpa [source] using sourceCompiled) (by
          simpa [target] using targetCompiled))
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
  have movedSourceOccurs : targetChecked.val.diagram.EndpointOccurs sourceWire
      { node := sourceWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := sourceWitness, port := .output } sourceWitnessNe sourceWire).2
        sourceWitnessOccurs
  have movedTargetOccurs : targetChecked.val.diagram.EndpointOccurs targetWire
      { node := targetWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := targetWitness, port := .output } targetWitnessNe targetWire).2
      targetWitnessOccurs
  have exposedEq : target.exposedWires = source.exposedWires := by
    exact endpointMoveTargetOpen_exposedWires input sourceWire targetWire endpoint
      boundary
  have hiddenEq : target.hiddenWires = source.hiddenWires := by
    exact endpointMoveTargetOpen_hiddenWires input sourceWire targetWire endpoint
      boundary
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, sourceDenotes⟩
    let hiddenLength := congrArg List.length hiddenEq
    let targetLocal := localEnv ∘ Fin.cast hiddenLength
    refine ⟨targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceDenotes ⊢
    have sourceRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) (extendWireEnv outer localEnv) PUnit.unit
      sourceItems).1 sourceDenotes
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires outer localEnv
    let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
      target.hiddenWires outer targetLocal
    change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit sourceItems at sourceRawDenotes
    have rawEq : ∀ targetIndex,
        targetRaw targetIndex = sourceRaw (Fin.cast
          (congrArg List.length contextsEq).symm targetIndex) := by
      intro targetIndex
      have functions := rootEnvironment_cast_lengths target.exposedWires
        target.hiddenWires source.exposedWires source.hiddenWires
        (congrArg List.length exposedEq) hiddenLength outer localEnv
      exact congrFun functions targetIndex
    have sourceCoalesced : ∀ sourceIndex targetIndex,
        source.rootWires.get sourceIndex = sourceWire →
        source.rootWires.get targetIndex = targetWire →
        sourceRaw sourceIndex = sourceRaw targetIndex := by
      intro sourceIndex targetIndex sourceGet targetGet
      have sourceValue :=
        AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
          sourceChecked sourceWire sourceWitness sourceWitnessRegion sourceTerm
          sourceWitnessShape sourceWitnessOccurs sourceRoute sourceRouteZero
          sourceItems (by simpa [sourceChecked, source] using sourceCompiled)
          model named sourceRaw sourceRawDenotes sourceIndex sourceGet
      have targetValue :=
        AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
          sourceChecked targetWire targetWitness targetWitnessRegion targetTerm
          targetWitnessShape targetWitnessOccurs targetRoute targetRouteZero
          sourceItems (by simpa [sourceChecked, source] using sourceCompiled)
          model named sourceRaw sourceRawDenotes targetIndex targetGet
      exact sourceValue.trans (termValues.trans targetValue.symm)
    have agrees := endpointMoveRelation_environmentsAgree input.val sourceWire
      targetWire source.rootWires target.rootWires sourceRaw targetRaw
      (fun sourceIndex targetIndex sameWire => by
        let targetAsSource := Fin.cast
          (congrArg List.length contextsEq).symm targetIndex
        have targetGet : source.rootWires.get targetAsSource =
            target.rootWires.get targetIndex := by
          simpa [targetAsSource] using List.get_of_eq contextsEq targetAsSource
        have indexEq : sourceIndex = targetAsSource := by
          apply Fin.ext
          exact (List.getElem_inj sourceExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using sameWire.trans targetGet.symm)
        exact (congrArg sourceRaw indexEq).trans (rawEq targetIndex).symm)
      (fun sourceIndex targetIndex sourceGet targetGet => by
        let targetAsSource := Fin.cast
          (congrArg List.length contextsEq).symm targetIndex
        have targetGetSource : source.rootWires.get targetAsSource = targetWire := by
          have transported := List.get_of_eq contextsEq targetAsSource
          exact transported.trans targetGet
        exact (sourceCoalesced sourceIndex targetAsSource sourceGet
          targetGetSource).trans (rawEq targetIndex).symm)
    have targetRawDenotes := semantic .forward sourceRaw targetRaw PUnit.unit agrees
      sourceRawDenotes
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := target.exposedWires)
        (bs := target.hiddenWires))) (extendWireEnv outer targetLocal) PUnit.unit
      targetItems).2
    exact targetRawDenotes
  · rintro ⟨localEnv, targetDenotes⟩
    let hiddenLength := congrArg List.length hiddenEq
    let sourceLocal := localEnv ∘ Fin.cast hiddenLength.symm
    refine ⟨sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetDenotes ⊢
    have targetRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := target.exposedWires)
        (bs := target.hiddenWires))) (extendWireEnv outer localEnv) PUnit.unit
      targetItems).1 targetDenotes
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires outer sourceLocal
    let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
      target.hiddenWires outer localEnv
    change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit targetItems at targetRawDenotes
    have rawEq : ∀ targetIndex,
        targetRaw targetIndex = sourceRaw (Fin.cast
          (congrArg List.length contextsEq).symm targetIndex) := by
      intro targetIndex
      have functions := rootEnvironment_cast_lengths source.exposedWires
        source.hiddenWires target.exposedWires target.hiddenWires
        (congrArg List.length exposedEq).symm hiddenLength.symm outer localEnv
      let sourceIndex := Fin.cast (congrArg List.length contextsEq).symm
        targetIndex
      have atSource := congrFun functions sourceIndex
      have mapped : Fin.cast (congrArg List.length contextsEq) sourceIndex =
          targetIndex := by
        apply Fin.ext
        rfl
      simpa [sourceRaw, targetRaw, sourceLocal, sourceIndex, mapped] using
        atSource.symm
    have targetCoalesced : ∀ sourceIndex targetIndex,
        target.rootWires.get sourceIndex = sourceWire →
        target.rootWires.get targetIndex = targetWire →
        targetRaw sourceIndex = targetRaw targetIndex := by
      intro sourceIndex targetIndex sourceGet targetGet
      have sourceValue :=
        AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
          targetChecked sourceWire sourceWitness sourceWitnessRegion sourceTerm
          (by simpa [targetChecked, target] using sourceWitnessShape)
          movedSourceOccurs movedSourceRoute movedSourceZero targetItems
          (by simpa [targetChecked, target] using targetCompiled) model named targetRaw
          targetRawDenotes sourceIndex sourceGet
      have targetValue :=
        AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
          targetChecked targetWire targetWitness targetWitnessRegion targetTerm
          (by simpa [targetChecked, target] using targetWitnessShape)
          movedTargetOccurs movedTargetRoute movedTargetZero targetItems
          (by simpa [targetChecked, target] using targetCompiled) model named targetRaw
          targetRawDenotes targetIndex targetGet
      exact sourceValue.trans (termValues.trans targetValue.symm)
    have agrees := endpointMoveRelation_environmentsAgree input.val sourceWire
      targetWire source.rootWires target.rootWires sourceRaw targetRaw
      (fun sourceIndex targetIndex sameWire => by
        let targetAsSource := Fin.cast
          (congrArg List.length contextsEq).symm targetIndex
        have targetGet : source.rootWires.get targetAsSource =
            target.rootWires.get targetIndex := by
          simpa [targetAsSource] using List.get_of_eq contextsEq targetAsSource
        have indexEq : sourceIndex = targetAsSource := by
          apply Fin.ext
          exact (List.getElem_inj sourceExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using sameWire.trans targetGet.symm)
        exact (congrArg sourceRaw indexEq).trans (rawEq targetIndex).symm)
      (fun sourceIndex targetIndex sourceGet targetGet => by
        let sourceAsTarget := Fin.cast
          (congrArg List.length contextsEq) sourceIndex
        have sourceGetTarget : target.rootWires.get sourceAsTarget = sourceWire := by
          have transported := List.get_of_eq contextsEq sourceIndex
          exact transported.symm.trans sourceGet
        have mappedBack : Fin.cast (congrArg List.length contextsEq).symm
            sourceAsTarget = sourceIndex := by
          apply Fin.ext
          rfl
        have coalesced := targetCoalesced sourceAsTarget targetIndex
          sourceGetTarget targetGet
        calc
          sourceRaw sourceIndex = targetRaw sourceAsTarget := by
            simpa [mappedBack] using (rawEq sourceAsTarget).symm
          _ = targetRaw targetIndex := coalesced)
    have sourceRawDenotes := semantic .backward sourceRaw targetRaw PUnit.unit agrees
      targetRawDenotes
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) (extendWireEnv outer sourceLocal) PUnit.unit
      sourceItems).2
    exact sourceRawDenotes

end AnchoredWireContractSoundness

end VisualProof.Rule
