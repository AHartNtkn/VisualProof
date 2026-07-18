import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRootRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

theorem rootChildKernel_of_inherited_anchor_source
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
    (anchorWire localWire : Fin input.val.wireCount)
    (wirePair :
      (anchorWire = sourceWire ∧ localWire = targetWire) ∨
      (anchorWire = targetWire ∧ localWire = sourceWire))
    (deep : Fin input.val.regionCount)
    (anchorWireVisible : input.val.Encloses
      (input.val.wires anchorWire).scope input.val.root)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope deep)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope deep)
    (deepEnclosesEndpoint : input.val.Encloses deep
      (input.val.nodes endpoint.node).region)
    (anchorWitness localWitness : Fin input.val.nodeCount)
    (anchorWitnessRegion localWitnessRegion : Fin input.val.regionCount)
    (anchorTerm localTerm : Lambda.Term 0 (Fin 0))
    (anchorWitnessShape : input.val.nodes anchorWitness =
      .term anchorWitnessRegion 0 anchorTerm)
    (localWitnessShape : input.val.nodes localWitness =
      .term localWitnessRegion 0 localTerm)
    (anchorWitnessOccurs : input.val.EndpointOccurs anchorWire
      { node := anchorWitness, port := .output })
    (localWitnessOccurs : input.val.EndpointOccurs localWire
      { node := localWitness, port := .output })
    (localWitnessNe : ({ node := localWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {anchorWitnessPath localWitnessPath routePath : List Nat}
    (anchorWitnessRoute : Diagram.Splice.RegionRoute input.val input.val.root
      anchorWitnessRegion anchorWitnessPath)
    (anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0)
    (localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
      localWitnessRegion localWitnessPath)
    (localWitnessZero : localWitnessRoute.HasCutDepth 0)
    {child : Fin input.val.regionCount}
    (route : Diagram.Splice.RegionRoute input.val child deep routePath)
    (termValues : ∀ model : Lambda.LambdaModel,
      model.eval anchorTerm Fin.elim0 = model.eval localTerm Fin.elim0)
    (sourceItems : ItemSeq signature
      (endpointMoveSourceOpen input boundary).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      (endpointMoveSourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetItems : ItemSeq signature
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires.length []) :
    RootChildSemanticKernel input sourceWire targetWire endpoint child
      (endpointMoveSourceOpen input boundary).rootWires
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires
      (fun model named sourceEnv _ =>
        denoteItemSeq (relCtx := []) model named sourceEnv PUnit.unit
          sourceItems) := by
  let source := endpointMoveSourceOpen input boundary
  have sourceWellFormed := endpointMoveSourceOpen_wellFormed input boundary
    boundaryRoot
  let sourceChecked : CheckedOpenDiagram signature := ⟨source, sourceWellFormed⟩
  have rootExact := OpenConcreteDiagram.rootWires_exact source sourceWellFormed
  obtain ⟨anchorIndex, anchorGet⟩ :=
    List.get_of_mem ((rootExact.mem_iff anchorWire).2 anchorWireVisible)
  intro rels fuel context sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    sourceBody targetBody sourceBodyCompiled targetBodyCompiled model named
    sourceEnv targetEnv relEnv outerAgrees sourceRootDenotes
  have anchorValue :=
    AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
      sourceChecked anchorWire anchorWitness anchorWitnessRegion anchorTerm
      anchorWitnessShape anchorWitnessOccurs anchorWitnessRoute anchorWitnessZero
      sourceItems (by simpa [sourceChecked, source] using sourceCompiled) model
      named sourceEnv sourceRootDenotes anchorIndex anchorGet
  exact compileRegion_moveEndpoint_route_equiv_of_inherited input sourceWire
    targetWire endpoint distinct sourceOccurs targetWellFormed anchorWire localWire
    wirePair deep sourceWireVisible targetWireVisible deepEnclosesEndpoint
    localWitness localWitnessRegion localTerm localWitnessShape localWitnessOccurs
    localWitnessNe localWitnessRoute localWitnessZero route fuel source.rootWires
    (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary).rootWires
    context sourceBinders targetBinders binderWitness sourceCover targetCover
    sourceEnumeration targetEnumeration sourceExact targetExact anchorIndex
    anchorGet sourceBody targetBody sourceBodyCompiled targetBodyCompiled model
    named sourceEnv targetEnv relEnv outerAgrees
    (anchorValue.trans (termValues model))

theorem rootChildKernel_of_inherited_anchor_target
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
    (anchorWire localWire : Fin input.val.wireCount)
    (wirePair :
      (anchorWire = sourceWire ∧ localWire = targetWire) ∨
      (anchorWire = targetWire ∧ localWire = sourceWire))
    (deep : Fin input.val.regionCount)
    (anchorWireVisible : input.val.Encloses
      (input.val.wires anchorWire).scope input.val.root)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope deep)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope deep)
    (deepEnclosesEndpoint : input.val.Encloses deep
      (input.val.nodes endpoint.node).region)
    (anchorWitness localWitness : Fin input.val.nodeCount)
    (anchorWitnessRegion localWitnessRegion : Fin input.val.regionCount)
    (anchorTerm localTerm : Lambda.Term 0 (Fin 0))
    (anchorWitnessShape : input.val.nodes anchorWitness =
      .term anchorWitnessRegion 0 anchorTerm)
    (localWitnessShape : input.val.nodes localWitness =
      .term localWitnessRegion 0 localTerm)
    (anchorWitnessOccurs : input.val.EndpointOccurs anchorWire
      { node := anchorWitness, port := .output })
    (localWitnessOccurs : input.val.EndpointOccurs localWire
      { node := localWitness, port := .output })
    (anchorWitnessNe : ({ node := anchorWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    (localWitnessNe : ({ node := localWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {anchorWitnessPath localWitnessPath routePath : List Nat}
    (anchorWitnessRoute : Diagram.Splice.RegionRoute input.val input.val.root
      anchorWitnessRegion anchorWitnessPath)
    (anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0)
    (localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
      localWitnessRegion localWitnessPath)
    (localWitnessZero : localWitnessRoute.HasCutDepth 0)
    {child : Fin input.val.regionCount}
    (route : Diagram.Splice.RegionRoute input.val child deep routePath)
    (termValues : ∀ model : Lambda.LambdaModel,
      model.eval anchorTerm Fin.elim0 = model.eval localTerm Fin.elim0)
    (sourceItems : ItemSeq signature
      (endpointMoveSourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires.length [])
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.regionCount)
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.root) = some targetItems) :
    RootChildSemanticKernel input sourceWire targetWire endpoint child
      (endpointMoveSourceOpen input boundary).rootWires
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires
      (fun model named _ targetEnv =>
        denoteItemSeq (relCtx := []) model named targetEnv PUnit.unit
          targetItems) := by
  let source := endpointMoveSourceOpen input boundary
  let target := endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
  have sourceWellFormed := endpointMoveSourceOpen_wellFormed input boundary
    boundaryRoot
  have targetWellFormedOpen := endpointMoveTargetOpen_wellFormed input sourceWire
    targetWire endpoint boundary boundaryRoot targetWellFormed
  let targetChecked : CheckedOpenDiagram signature :=
    ⟨target, targetWellFormedOpen⟩
  have sourceRootExact := OpenConcreteDiagram.rootWires_exact source
    sourceWellFormed
  obtain ⟨anchorIndex, anchorGet⟩ :=
    List.get_of_mem ((sourceRootExact.mem_iff anchorWire).2 anchorWireVisible)
  let movedAnchorRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint anchorWitnessRoute
  have movedAnchorZero : movedAnchorRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      anchorWitnessRoute anchorWitnessZero
  have movedAnchorOccurs : targetChecked.val.diagram.EndpointOccurs anchorWire
      { node := anchorWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := anchorWitness, port := .output } anchorWitnessNe anchorWire).2
        anchorWitnessOccurs
  intro rels fuel context sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    sourceBody targetBody sourceBodyCompiled targetBodyCompiled model named
    sourceEnv targetEnv relEnv outerAgrees targetRootDenotes
  let targetAnchorIndex := Fin.cast
    (congrArg List.length context.contexts_eq) anchorIndex
  have targetAnchorGet : target.rootWires.get targetAnchorIndex = anchorWire := by
    have transported := List.get_of_eq context.contexts_eq anchorIndex
    exact transported.symm.trans anchorGet
  have targetAnchorValue :=
    AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
      targetChecked anchorWire anchorWitness anchorWitnessRegion anchorTerm
      (by simpa [targetChecked, target] using anchorWitnessShape)
      movedAnchorOccurs movedAnchorRoute movedAnchorZero targetItems
      (by simpa [targetChecked, target] using targetCompiled) model named
      targetEnv targetRootDenotes targetAnchorIndex targetAnchorGet
  have sourceAnchorValue : sourceEnv anchorIndex =
      model.eval anchorTerm Fin.elim0 := by
    exact (outerAgrees anchorIndex targetAnchorIndex (by rfl)).trans
      targetAnchorValue
  exact compileRegion_moveEndpoint_route_equiv_of_inherited input sourceWire
    targetWire endpoint distinct sourceOccurs targetWellFormed anchorWire localWire
    wirePair deep sourceWireVisible targetWireVisible deepEnclosesEndpoint
    localWitness localWitnessRegion localTerm localWitnessShape localWitnessOccurs
    localWitnessNe localWitnessRoute localWitnessZero route fuel source.rootWires
    target.rootWires context sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    anchorIndex anchorGet sourceBody targetBody sourceBodyCompiled
    targetBodyCompiled model named sourceEnv targetEnv relEnv outerAgrees
    (sourceAnchorValue.trans (termValues model))

end AnchoredWireContractSoundness

end VisualProof.Rule
