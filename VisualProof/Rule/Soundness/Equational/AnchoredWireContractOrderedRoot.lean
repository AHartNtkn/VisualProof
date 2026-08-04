import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRootAnchor

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- The oriented two-anchor kernel lifted through the authoritative
exposed-then-hidden root compiler, including a root anchor and same-site roots. -/
theorem finishRoot_moveEndpoint_equiv_of_ordered_anchors
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
    (shallow deep : Fin input.val.regionCount)
    (anchorWireVisible : input.val.Encloses
      (input.val.wires anchorWire).scope shallow)
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
    {anchorWitnessPath localWitnessPath routePath rootPath : List Nat}
    (anchorWitnessRoute : Diagram.Splice.RegionRoute input.val shallow
      anchorWitnessRegion anchorWitnessPath)
    (anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0)
    (localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
      localWitnessRegion localWitnessPath)
    (localWitnessZero : localWitnessRoute.HasCutDepth 0)
    (route : Diagram.Splice.RegionRoute input.val shallow deep routePath)
    (rootRoute : Diagram.Splice.RegionRoute input.val input.val.root shallow
      rootPath)
    (termValues : ∀ model : Lambda.LambdaModel,
      model.eval anchorTerm Fin.elim0 = model.eval localTerm Fin.elim0)
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
      model.Carrier) :
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
  cases rootRoute with
  | @step _ child _ rest parentEq position positionEq tail =>
      have childEnclosesEndpoint := ConcreteElaboration.checked_encloses_trans
        input.property (regionRoute_encloses input.val input.property tail)
        (ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property route)
          deepEnclosesEndpoint)
      let sourceKernel : RootChildSemanticKernel input sourceWire targetWire
          endpoint child (endpointMoveSourceOpen input boundary).rootWires
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).rootWires
          (fun currentModel currentNamed sourceEnv _ =>
            denoteItemSeq (relCtx := []) currentModel currentNamed sourceEnv
              PUnit.unit sourceItems) :=
        rootChildKernel_of_route_kernel input sourceWire
        targetWire endpoint targetWellFormed shallow
        (ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property route)
          deepEnclosesEndpoint)
        (finishRegion_moveEndpoint_equiv_of_ordered_anchors input sourceWire
          targetWire endpoint distinct sourceOccurs targetWellFormed anchorWire
          localWire wirePair shallow deep anchorWireVisible sourceWireVisible
          targetWireVisible deepEnclosesEndpoint anchorWitness localWitness
          anchorWitnessRegion localWitnessRegion anchorTerm localTerm
          anchorWitnessShape localWitnessShape anchorWitnessOccurs
          localWitnessOccurs anchorWitnessNe localWitnessNe anchorWitnessRoute
          anchorWitnessZero localWitnessRoute localWitnessZero route termValues)
        tail (endpointMoveSourceOpen input boundary).rootWires
        (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
          ).rootWires
        (fun currentModel currentNamed sourceEnv _ =>
          denoteItemSeq (relCtx := []) currentModel currentNamed sourceEnv
            PUnit.unit sourceItems)
      let targetKernel : RootChildSemanticKernel input sourceWire targetWire
          endpoint child (endpointMoveSourceOpen input boundary).rootWires
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).rootWires
          (fun currentModel currentNamed _ targetEnv =>
            denoteItemSeq (relCtx := []) currentModel currentNamed targetEnv
              PUnit.unit targetItems) :=
        rootChildKernel_of_route_kernel input sourceWire
        targetWire endpoint targetWellFormed shallow
        (ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property route)
          deepEnclosesEndpoint)
        (finishRegion_moveEndpoint_equiv_of_ordered_anchors input sourceWire
          targetWire endpoint distinct sourceOccurs targetWellFormed anchorWire
          localWire wirePair shallow deep anchorWireVisible sourceWireVisible
          targetWireVisible deepEnclosesEndpoint anchorWitness localWitness
          anchorWitnessRegion localWitnessRegion anchorTerm localTerm
          anchorWitnessShape localWitnessShape anchorWitnessOccurs
          localWitnessOccurs anchorWitnessNe localWitnessNe anchorWitnessRoute
          anchorWitnessZero localWitnessRoute localWitnessZero route termValues)
        tail (endpointMoveSourceOpen input boundary).rootWires
        (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
          ).rootWires
        (fun currentModel currentNamed _ targetEnv =>
          denoteItemSeq (relCtx := []) currentModel currentNamed targetEnv
            PUnit.unit targetItems)
      exact finishRoot_moveEndpoint_route_step_equiv_of_kernel input boundary
        boundaryRoot sourceWire targetWire endpoint targetWellFormed child
        parentEq position positionEq childEnclosesEndpoint sourceItems targetItems
        sourceCompiled targetCompiled sourceKernel targetKernel model named outer
  | here =>
      cases route with
      | here =>
          rcases wirePair with pair | pair
          · exact finishRoot_moveEndpoint_equiv_of_two_anchors input boundary
              boundaryRoot sourceWire targetWire endpoint distinct sourceOccurs
              targetWellFormed sourceWireVisible targetWireVisible anchorWitness
              localWitness anchorWitnessRegion localWitnessRegion anchorTerm
              localTerm anchorWitnessShape localWitnessShape
              (pair.1 ▸ anchorWitnessOccurs) (pair.2 ▸ localWitnessOccurs)
              anchorWitnessNe localWitnessNe anchorWitnessRoute localWitnessRoute
              anchorWitnessZero localWitnessZero sourceItems targetItems
              sourceCompiled targetCompiled model named outer (termValues model)
          · exact finishRoot_moveEndpoint_equiv_of_two_anchors input boundary
              boundaryRoot sourceWire targetWire endpoint distinct sourceOccurs
              targetWellFormed sourceWireVisible targetWireVisible localWitness
              anchorWitness localWitnessRegion anchorWitnessRegion localTerm
              anchorTerm localWitnessShape anchorWitnessShape
              (pair.2 ▸ localWitnessOccurs) (pair.1 ▸ anchorWitnessOccurs)
              localWitnessNe anchorWitnessNe localWitnessRoute anchorWitnessRoute
              localWitnessZero anchorWitnessZero sourceItems targetItems
              sourceCompiled targetCompiled model named outer
              (termValues model).symm
      | @step _ child _ rest parentEq position positionEq tail =>
          let sourceKernel : RootChildSemanticKernel input sourceWire targetWire
              endpoint child (endpointMoveSourceOpen input boundary).rootWires
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).rootWires
              (fun currentModel currentNamed sourceEnv _ =>
                denoteItemSeq (relCtx := []) currentModel currentNamed sourceEnv
                  PUnit.unit sourceItems) :=
            rootChildKernel_of_inherited_anchor_source input
            boundary boundaryRoot sourceWire targetWire endpoint distinct
            sourceOccurs targetWellFormed anchorWire localWire wirePair deep
            anchorWireVisible sourceWireVisible targetWireVisible
            deepEnclosesEndpoint anchorWitness localWitness anchorWitnessRegion
            localWitnessRegion anchorTerm localTerm anchorWitnessShape
            localWitnessShape anchorWitnessOccurs localWitnessOccurs localWitnessNe
            anchorWitnessRoute anchorWitnessZero localWitnessRoute localWitnessZero
            tail termValues sourceItems sourceCompiled targetItems
          let targetKernel : RootChildSemanticKernel input sourceWire targetWire
              endpoint child (endpointMoveSourceOpen input boundary).rootWires
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).rootWires
              (fun currentModel currentNamed _ targetEnv =>
                denoteItemSeq (relCtx := []) currentModel currentNamed targetEnv
                  PUnit.unit targetItems) :=
            rootChildKernel_of_inherited_anchor_target input
            boundary boundaryRoot sourceWire targetWire endpoint distinct
            sourceOccurs targetWellFormed anchorWire localWire wirePair deep
            anchorWireVisible sourceWireVisible targetWireVisible
            deepEnclosesEndpoint anchorWitness localWitness anchorWitnessRegion
            localWitnessRegion anchorTerm localTerm anchorWitnessShape
            localWitnessShape anchorWitnessOccurs localWitnessOccurs
            anchorWitnessNe localWitnessNe anchorWitnessRoute anchorWitnessZero
            localWitnessRoute localWitnessZero tail termValues sourceItems
            targetItems targetCompiled
          have childEnclosesEndpoint := ConcreteElaboration.checked_encloses_trans
            input.property (regionRoute_encloses input.val input.property tail)
            deepEnclosesEndpoint
          exact finishRoot_moveEndpoint_route_step_equiv_of_kernel input boundary
            boundaryRoot sourceWire targetWire endpoint targetWellFormed child
            parentEq position positionEq childEnclosesEndpoint sourceItems
            targetItems sourceCompiled targetCompiled sourceKernel targetKernel
            model named outer

end AnchoredWireContractSoundness

end VisualProof.Rule
