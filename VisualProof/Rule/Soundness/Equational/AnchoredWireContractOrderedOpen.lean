import VisualProof.Rule.Soundness.Equational.AnchoredWireContractOrderedRoot
import VisualProof.Rule.Soundness.Equational.AnchoredWireContractWellFormed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- All semantic data needed to compare one executor-certified endpoint move,
with the two anchor sites already oriented from shallow to deep. -/
structure OrderedEndpointAnchorData
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount) where
  anchorWire : Fin input.val.wireCount
  localWire : Fin input.val.wireCount
  wirePair :
    (anchorWire = sourceWire ∧ localWire = targetWire) ∨
      (anchorWire = targetWire ∧ localWire = sourceWire)
  shallow : Fin input.val.regionCount
  deep : Fin input.val.regionCount
  anchorWireVisible : input.val.Encloses
    (input.val.wires anchorWire).scope shallow
  sourceWireVisible : input.val.Encloses
    (input.val.wires sourceWire).scope deep
  targetWireVisible : input.val.Encloses
    (input.val.wires targetWire).scope deep
  deepEnclosesEndpoint : input.val.Encloses deep
    (input.val.nodes endpoint.node).region
  anchorWitness : Fin input.val.nodeCount
  localWitness : Fin input.val.nodeCount
  anchorWitnessRegion : Fin input.val.regionCount
  localWitnessRegion : Fin input.val.regionCount
  anchorTerm : Lambda.Term 0 (Fin 0)
  localTerm : Lambda.Term 0 (Fin 0)
  anchorWitnessShape : input.val.nodes anchorWitness =
    .term anchorWitnessRegion 0 anchorTerm
  localWitnessShape : input.val.nodes localWitness =
    .term localWitnessRegion 0 localTerm
  anchorWitnessOccurs : input.val.EndpointOccurs anchorWire
    { node := anchorWitness, port := .output }
  localWitnessOccurs : input.val.EndpointOccurs localWire
    { node := localWitness, port := .output }
  anchorWitnessNe : ({ node := anchorWitness, port := CPort.output } :
    CEndpoint input.val.nodeCount) ≠ endpoint
  localWitnessNe : ({ node := localWitness, port := CPort.output } :
    CEndpoint input.val.nodeCount) ≠ endpoint
  anchorWitnessPath : List Nat
  localWitnessPath : List Nat
  routePath : List Nat
  rootPath : List Nat
  anchorWitnessRoute : Diagram.Splice.RegionRoute input.val shallow
    anchorWitnessRegion anchorWitnessPath
  anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0
  localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
    localWitnessRegion localWitnessPath
  localWitnessZero : localWitnessRoute.HasCutDepth 0
  route : Diagram.Splice.RegionRoute input.val shallow deep routePath
  rootRoute : Diagram.Splice.RegionRoute input.val input.val.root shallow rootPath
  termValues : ∀ model : Lambda.LambdaModel,
    model.eval anchorTerm Fin.elim0 = model.eval localTerm Fin.elim0

/-- The successful contraction gates construct ordered anchor data for every
endpoint that the executor moves. -/
theorem contractEndpointAnchorData_exists
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (member : endpoint ∈ movedEndpoints input redundant drop)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (survivorShape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (survivorOccurs : input.val.EndpointOccurs keep
      { node := survivor, port := .output })
    (distinct : drop ≠ keep)
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (availability : AnchoredWireSoundness.SplitAvailability input keep
      survivorRegion (input.val.nodes endpoint.node).region)
    (termValues : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0) :
    Nonempty (OrderedEndpointAnchorData input drop keep endpoint) := by
  obtain ⟨redundantPath, redundantRoute, redundantZero⟩ :=
    redundant_zero_route input redundant redundantRegion redundantTerm drop
      redundantShape redundantOccurs sameDepth
  obtain ⟨survivorPath, survivorRoute, survivorZero⟩ :=
    availability.witness_zero_route
  have redundantNe := movedEndpoints_ne_redundant input redundant drop member
  have survivorNe := movedEndpoint_ne_survivor_output input redundant survivor
    drop keep endpoint member survivorOccurs distinct
  rcases movedEndpoint_scopes_comparable input redundant drop keep survivorRegion
      member availability with dropAbove | keepAbove
  · obtain ⟨routePath, ⟨route⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val
        (input.val.wires drop).scope availability.available dropAbove
    obtain ⟨rootPath, ⟨rootRoute⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val input.val.root
        (input.val.wires drop).scope
        (input.property.all_regions_reach_root (input.val.wires drop).scope)
    exact ⟨{
      anchorWire := drop
      localWire := keep
      wirePair := Or.inl ⟨rfl, rfl⟩
      shallow := (input.val.wires drop).scope
      deep := availability.available
      anchorWireVisible := ⟨0, rfl⟩
      sourceWireVisible := dropAbove
      targetWireVisible := availability.wire_encloses
      deepEnclosesEndpoint := availability.target_inside
      anchorWitness := redundant
      localWitness := survivor
      anchorWitnessRegion := redundantRegion
      localWitnessRegion := survivorRegion
      anchorTerm := redundantTerm
      localTerm := survivorTerm
      anchorWitnessShape := redundantShape
      localWitnessShape := survivorShape
      anchorWitnessOccurs := redundantOccurs
      localWitnessOccurs := survivorOccurs
      anchorWitnessNe := redundantNe.symm
      localWitnessNe := survivorNe
      anchorWitnessPath := redundantPath
      localWitnessPath := survivorPath
      routePath := routePath
      rootPath := rootPath
      anchorWitnessRoute := redundantRoute
      anchorWitnessZero := redundantZero
      localWitnessRoute := survivorRoute
      localWitnessZero := survivorZero
      route := route
      rootRoute := rootRoute
      termValues := termValues
    }⟩
  · obtain ⟨routePath, ⟨route⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val
        availability.available (input.val.wires drop).scope keepAbove
    obtain ⟨rootPath, ⟨rootRoute⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val input.val.root
        availability.available
        (input.property.all_regions_reach_root availability.available)
    have dropEnclosesEndpoint := input.property.wire_scopes_enclose drop endpoint
      (movedEndpoints_mem_occurs input redundant drop member)
    exact ⟨{
      anchorWire := keep
      localWire := drop
      wirePair := Or.inr ⟨rfl, rfl⟩
      shallow := availability.available
      deep := (input.val.wires drop).scope
      anchorWireVisible := availability.wire_encloses
      sourceWireVisible := ⟨0, rfl⟩
      targetWireVisible := ConcreteElaboration.checked_encloses_trans
        input.property availability.wire_encloses keepAbove
      deepEnclosesEndpoint := dropEnclosesEndpoint
      anchorWitness := survivor
      localWitness := redundant
      anchorWitnessRegion := survivorRegion
      localWitnessRegion := redundantRegion
      anchorTerm := survivorTerm
      localTerm := redundantTerm
      anchorWitnessShape := survivorShape
      localWitnessShape := redundantShape
      anchorWitnessOccurs := survivorOccurs
      localWitnessOccurs := redundantOccurs
      anchorWitnessNe := survivorNe
      localWitnessNe := redundantNe.symm
      anchorWitnessPath := survivorPath
      localWitnessPath := redundantPath
      routePath := routePath
      rootPath := rootPath
      anchorWitnessRoute := survivorRoute
      anchorWitnessZero := survivorZero
      localWitnessRoute := redundantRoute
      localWitnessZero := redundantZero
      route := route
      rootRoute := rootRoute
      termValues := fun model => (termValues model).symm
    }⟩

/-- One ordered endpoint move preserves the authoritative root compiler. -/
theorem compileRoot_moveEndpoint_equiv_of_anchor_data
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
    (data : OrderedEndpointAnchorData input sourceWire targetWire endpoint)
    (sourceBody : Region signature
      (endpointMoveSourceOpen input boundary).exposedWires.length [])
    (targetBody : Region signature
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).exposedWires.length [])
    (sourceCompiled : ConcreteElaboration.compileRoot? signature input.val
      (endpointMoveSourceOpen input boundary).exposedWires
      (endpointMoveSourceOpen input boundary).hiddenWires = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRoot? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).exposedWires
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).hiddenWires = some targetBody)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outer : Fin (endpointMoveSourceOpen input boundary).exposedWires.length →
      model.Carrier) :
    denoteRegion (relCtx := []) model named outer PUnit.unit sourceBody ↔
      denoteRegion (relCtx := []) model named outer PUnit.unit targetBody := by
  cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      ((endpointMoveSourceOpen input boundary).exposedWires ++
        (endpointMoveSourceOpen input boundary).hiddenWires)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) with
  | none =>
      have sourceNone : ConcreteElaboration.compileRoot? signature input.val
          (endpointMoveSourceOpen input boundary).exposedWires
          (endpointMoveSourceOpen input boundary).hiddenWires = none := by
        have bound := congrArg (fun result => result.bind fun items =>
          some (ConcreteElaboration.finishRoot
            (endpointMoveSourceOpen input boundary).exposedWires
            (endpointMoveSourceOpen input boundary).hiddenWires items))
          sourceItemsEq
        exact bound
      rw [sourceNone] at sourceCompiled
      contradiction
  | some sourceItems =>
      have sourceSome : ConcreteElaboration.compileRoot? signature input.val
          (endpointMoveSourceOpen input boundary).exposedWires
          (endpointMoveSourceOpen input boundary).hiddenWires =
          some (ConcreteElaboration.finishRoot
            (endpointMoveSourceOpen input boundary).exposedWires
            (endpointMoveSourceOpen input boundary).hiddenWires sourceItems) := by
        have bound := congrArg (fun result => result.bind fun items =>
          some (ConcreteElaboration.finishRoot
            (endpointMoveSourceOpen input boundary).exposedWires
            (endpointMoveSourceOpen input boundary).hiddenWires items))
          sourceItemsEq
        exact bound
      have sourceBodyEq := Option.some.inj (sourceSome.symm.trans sourceCompiled)
      subst sourceBody
      cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
          (moveEndpointRaw input.val sourceWire targetWire endpoint)
          (ConcreteElaboration.compileRegion? signature
            (moveEndpointRaw input.val sourceWire targetWire endpoint)
            input.val.regionCount)
          ((endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
              ).exposedWires ++
            (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
              ).hiddenWires) ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences
            (moveEndpointRaw input.val sourceWire targetWire endpoint)
            input.val.root) with
      | none =>
          have targetNone : ConcreteElaboration.compileRoot? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint)
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).exposedWires
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).hiddenWires = none := by
            have bound := congrArg (fun result => result.bind fun items =>
              some (ConcreteElaboration.finishRoot
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).exposedWires
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).hiddenWires items)) targetItemsEq
            exact bound
          rw [targetNone] at targetCompiled
          contradiction
      | some targetItems =>
          have targetSome : ConcreteElaboration.compileRoot? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint)
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).exposedWires
              (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
                ).hiddenWires =
              some (ConcreteElaboration.finishRoot
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).exposedWires
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).hiddenWires targetItems) := by
            have bound := congrArg (fun result => result.bind fun items =>
              some (ConcreteElaboration.finishRoot
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).exposedWires
                (endpointMoveTargetOpen input sourceWire targetWire endpoint
                  boundary).hiddenWires items)) targetItemsEq
            exact bound
          have targetBodyEq := Option.some.inj
            (targetSome.symm.trans targetCompiled)
          subst targetBody
          exact finishRoot_moveEndpoint_equiv_of_ordered_anchors input boundary
            boundaryRoot sourceWire targetWire endpoint distinct sourceOccurs
            targetWellFormed data.anchorWire data.localWire data.wirePair
            data.shallow data.deep data.anchorWireVisible
            data.sourceWireVisible data.targetWireVisible
            data.deepEnclosesEndpoint data.anchorWitness data.localWitness
            data.anchorWitnessRegion data.localWitnessRegion data.anchorTerm
            data.localTerm data.anchorWitnessShape data.localWitnessShape
            data.anchorWitnessOccurs data.localWitnessOccurs data.anchorWitnessNe
            data.localWitnessNe data.anchorWitnessRoute data.anchorWitnessZero
            data.localWitnessRoute data.localWitnessZero data.route data.rootRoute
            data.termValues sourceItems targetItems sourceItemsEq targetItemsEq
            model named outer

def endpointMoveSourceCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  ⟨endpointMoveSourceOpen input boundary,
    endpointMoveSourceOpen_wellFormed input boundary boundaryRoot⟩

def endpointMoveTargetCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature) : CheckedOpenDiagram signature :=
  ⟨endpointMoveTargetOpen input sourceWire targetWire endpoint boundary,
    endpointMoveTargetOpen_wellFormed input sourceWire targetWire endpoint
      boundary boundaryRoot targetWellFormed⟩

/-- One ordered endpoint move preserves denotation at the exact ordered open
boundary; repeated aliases use the same boundary-class assignment. -/
theorem moveEndpointOpen_denote_iff_of_anchor_data
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
    (data : OrderedEndpointAnchorData input sourceWire targetWire endpoint)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    (endpointMoveSourceCheckedOpen input boundary boundaryRoot).denote model
        named args ↔
      (endpointMoveTargetCheckedOpen input boundary boundaryRoot sourceWire
        targetWire endpoint targetWellFormed).denote model named args := by
  let source := endpointMoveSourceCheckedOpen input boundary boundaryRoot
  let target := endpointMoveTargetCheckedOpen input boundary boundaryRoot
    sourceWire targetWire endpoint targetWellFormed
  obtain ⟨sourceBody, sourceCompiled, sourceElaborated⟩ :=
    CheckedOpenDiagram.elaborate_body_computation source
  obtain ⟨targetBody, targetCompiled, targetElaborated⟩ :=
    CheckedOpenDiagram.elaborate_body_computation target
  have bodyEquiv := compileRoot_moveEndpoint_equiv_of_anchor_data input boundary
    boundaryRoot sourceWire targetWire endpoint distinct sourceOccurs
    targetWellFormed data sourceBody targetBody sourceCompiled targetCompiled
    model named
  change source.denote model named args ↔ target.denote model named args
  constructor
  · intro sourceDenotes
    change denoteOpen model named source.elaborate args at sourceDenotes
    rcases sourceDenotes with ⟨sourceAssignment, sourceArgs, sourceBodyDenotes⟩
    let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
      args := sourceAssignment.args
      classes := sourceAssignment.classes
      agrees := by
        intro position
        exact sourceAssignment.agrees position
    }
    refine ⟨targetAssignment, sourceArgs, ?_⟩
    rw [targetElaborated]
    apply (bodyEquiv sourceAssignment.classes).mp
    rw [sourceElaborated] at sourceBodyDenotes
    exact sourceBodyDenotes
  · intro targetDenotes
    change denoteOpen model named target.elaborate args at targetDenotes
    rcases targetDenotes with ⟨targetAssignment, targetArgs, targetBodyDenotes⟩
    let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
      args := targetAssignment.args
      classes := targetAssignment.classes
      agrees := by
        intro position
        exact targetAssignment.agrees position
    }
    refine ⟨sourceAssignment, targetArgs, ?_⟩
    rw [sourceElaborated]
    apply (bodyEquiv targetAssignment.classes).mpr
    rw [targetElaborated] at targetBodyDenotes
    exact targetBodyDenotes

end AnchoredWireContractSoundness

end VisualProof.Rule
