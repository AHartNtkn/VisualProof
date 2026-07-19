import VisualProof.Rule.Soundness.Equational.FusionSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FusionSoundness

theorem interface_image_origin
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (sourceWire : Fin input.val.wireCount)
    (targetWire : Fin (fusionWireDomain input.val consumedWire).count)
    (image : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).image? sourceWire = some targetWire) :
    sourceWire = (fusionWireDomain input.val consumedWire).origin targetWire := by
  unfold fusionInterfaceTransport InterfaceTransport.survivors
    InterfaceTransport.rootFiltered at image
  cases indexed : (fusionWireDomain input.val consumedWire).index? sourceWire with
  | none =>
      simp only [indexed, Option.map_none] at image
      change (none >>= fun mapped => if
        ((fusionRaw input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort).wires mapped).scope =
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire
              consumerWire consumedPort).root then some mapped else none) =
        some targetWire at image
      simp at image
  | some targetIndex =>
      simp only [indexed, Option.map_some] at image
      let mapped : Fin (fusionRaw input consumedWire producer consumer
          hdistinct consumerRegion producerTerm consumerTerm producerWire
          consumerWire consumedPort).wireCount :=
        Fin.cast (by rfl) targetIndex
      change (if ((fusionRaw input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort).wires mapped).scope =
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire
              consumerWire consumedPort).root then some mapped else none) =
        some targetWire at image
      by_cases rootScoped :
          ((fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort).wires mapped).scope =
              (fusionRaw input consumedWire producer consumer hdistinct
                consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort).root
      · rw [if_pos rootScoped] at image
        have targetEq : targetIndex = targetWire := by
          apply Fin.ext
          exact congrArg Fin.val (Option.some.inj image)
        subst targetWire
        exact ((fusionWireDomain input.val consumedWire).index?_eq_some_iff
          sourceWire targetIndex).mp indexed |>.symm
      · rw [if_neg rootScoped] at image
        contradiction

theorem interface_image_survivor
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (wire : Fin input.val.wireCount) (survives : wire ≠ consumedWire)
    (rootScoped : (input.val.wires wire).scope = input.val.root) :
    (fusionInterfaceTransport input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).image? wire = some
        ((fusionWireDomain input.val consumedWire).index wire (by
          simp [fusionWireDomain, survives])) := by
  let domain := fusionWireDomain input.val consumedWire
  have survives' : domain.survives wire = true := by
    simp [domain, fusionWireDomain, survives]
  change (do
    let mapped ← (domain.index? wire).map (Fin.cast (by rfl))
    if ((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).wires mapped).scope = input.val.root then some mapped
    else none) = some (domain.index wire survives')
  rw [domain.index?_index wire survives']
  let mapped : Fin (fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).wireCount := Fin.cast (by rfl) (domain.index wire survives')
  change (if ((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).wires mapped).scope = input.val.root then some mapped
    else none) = some (domain.index wire survives')
  have mappedEq : mapped = domain.index wire survives' := by
    apply Fin.ext
    rfl
  have origin := domain.origin_index wire survives'
  have mappedRoot : ((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).wires mapped).scope = input.val.root := by
    rw [fusionRaw_wire_scope, mappedEq]
    change (input.val.wires (domain.origin (domain.index wire survives'))).scope =
      input.val.root
    rw [origin]
    exact rootScoped
  rw [if_pos mappedRoot, mappedEq]
  rfl

def sourceOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def targetOpen
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count)) :
    OpenConcreteDiagram where
  diagram := fusionRaw input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort
  boundary := mapped

def sourceCheckedOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  ⟨sourceOpen input boundary, input.property, sourceRoot⟩

def targetCheckedOpen
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature) : CheckedOpenDiagram signature :=
  ⟨targetOpen input consumedWire producer consumer hdistinct consumerRegion
    producerTerm consumerTerm producerWire consumerWire consumedPort mapped,
    targetWellFormed, by simpa using targetRoot⟩

theorem boundary_origin_mem
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped)
    (targetWire : Fin (fusionWireDomain input.val consumedWire).count)
    (member : targetWire ∈ mapped) :
    (fusionWireDomain input.val consumedWire).origin targetWire ∈ boundary := by
  obtain ⟨targetPosition, targetGet⟩ := List.mem_iff_get.mp member
  have lengthEq :=
    (fusionInterfaceTransport input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).transportBoundary_length transport
  let sourcePosition : Fin boundary.length := Fin.cast lengthEq targetPosition
  have image :=
    (fusionInterfaceTransport input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).transportBoundary_get transport sourcePosition
  have positionEq : Fin.cast lengthEq.symm sourcePosition = targetPosition := by
    apply Fin.ext
    rfl
  rw [positionEq] at image
  have image' :
      (fusionInterfaceTransport input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).image? (boundary.get sourcePosition) =
        some targetWire := image.trans (congrArg some targetGet)
  have origin := interface_image_origin input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort (boundary.get sourcePosition) targetWire image'
  rw [← origin]
  exact List.get_mem boundary sourcePosition

theorem boundary_image_mem
    (transport : InterfaceTransport source target)
    (boundary : List (Fin source.wireCount))
    (mapped : List (Fin target.wireCount))
    (htransport : transport.transportBoundary boundary = some mapped)
    (sourceWire : Fin source.wireCount) (targetWire : Fin target.wireCount)
    (sourceMember : sourceWire ∈ boundary)
    (image : transport.image? sourceWire = some targetWire) :
    targetWire ∈ mapped := by
  obtain ⟨sourcePosition, sourceGet⟩ := List.mem_iff_get.mp sourceMember
  have transported := transport.transportBoundary_get htransport sourcePosition
  rw [sourceGet] at transported
  have targetGet := Option.some.inj (transported.symm.trans image)
  rw [← targetGet]
  exact List.get_mem mapped _

noncomputable def exposedContext
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped) :
    Context input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort
      (sourceOpen input boundary).exposedWires
      (targetOpen input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
        mapped).exposedWires := by
  let source := sourceOpen input boundary
  let target := targetOpen input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort mapped
  let sourceIndex : Fin target.exposedWires.length →
      Fin source.exposedWires.length := fun targetIndex ↦
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((OpenConcreteDiagram.mem_exposedWires source
        ((fusionWireDomain input.val consumedWire).origin
          (target.exposedWires.get targetIndex))).2
        (boundary_origin_mem input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort boundary mapped transport
          (target.exposedWires.get targetIndex)
          ((OpenConcreteDiagram.mem_exposedWires target
            (target.exposedWires.get targetIndex)).1
            (List.get_mem target.exposedWires targetIndex)))))
  exact {
    sourceIndex := sourceIndex
    get := by
      intro targetIndex
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete
            ((OpenConcreteDiagram.mem_exposedWires source
              ((fusionWireDomain input.val consumedWire).origin
                (target.exposedWires.get targetIndex))).2
              (boundary_origin_mem input consumedWire producer consumer
                hdistinct consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort boundary mapped transport
                (target.exposedWires.get targetIndex)
                ((OpenConcreteDiagram.mem_exposedWires target
                  (target.exposedWires.get targetIndex)).1
                  (List.get_mem target.exposedWires targetIndex))))))
  }

theorem consumed_not_mem_boundary
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped) :
    consumedWire ∉ boundary := by
  intro member
  obtain ⟨position, get⟩ := List.mem_iff_get.mp member
  have image :=
    (fusionInterfaceTransport input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).transportBoundary_get transport position
  rw [get] at image
  unfold fusionInterfaceTransport InterfaceTransport.survivors
    InterfaceTransport.rootFiltered at image
  have absent : (fusionWireDomain input.val consumedWire).index? consumedWire =
      none := by simp [fusionWireDomain]
  simp only [absent, Option.map_none] at image
  change (none >>= fun mappedWire => if
      ((fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort).wires
        mappedWire).scope = input.val.root then some mappedWire else none) = _
    at image
  simp at image

private theorem rootExposedIndex_get (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.exposedWires.length) :
    openDiagram.rootWires.get
        (Splice.Input.TwoInputPresentation.rootExposedIndex openDiagram index) =
      openDiagram.exposedWires.get index := by
  simp [Splice.Input.TwoInputPresentation.rootExposedIndex,
    OpenConcreteDiagram.rootWires, List.get_eq_getElem,
    List.getElem_append_left]

private theorem rootHiddenIndex_get (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.hiddenWires.length) :
    openDiagram.rootWires.get
        (Splice.Input.TwoInputPresentation.rootHiddenIndex openDiagram index) =
      openDiagram.hiddenWires.get index := by
  simp [Splice.Input.TwoInputPresentation.rootHiddenIndex,
    OpenConcreteDiagram.rootWires, List.get_eq_getElem,
    List.getElem_append_right]

theorem rootEnvironment_forward
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (sourceOuter : Fin (sourceOpen input boundary).exposedWires.length → D)
    (targetOuter : Fin (targetOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped).exposedWires.length → D)
    (outerAgrees : ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      (exposedContext input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort boundary mapped transport).indexRelation
      sourceOuter targetOuter)
    (sourceLocal : Fin (sourceOpen input boundary).hiddenWires.length → D) :
    ∃ targetLocal : Fin (targetOpen input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort mapped).hiddenWires.length → D,
      let source := sourceCheckedOpen input boundary sourceRoot
      let target := targetCheckedOpen input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort mapped targetRoot targetWellFormed
      let combined := Context.ofExact input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort input.val.root source.val.rootWires
        target.val.rootWires
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source)
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target)
      combined.indexRelation.EnvironmentsAgree
        (ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceLocal)
        (ConcreteElaboration.rootEnvironment target.val.exposedWires
          target.val.hiddenWires targetOuter targetLocal) := by
  let source := sourceCheckedOpen input boundary sourceRoot
  let target := targetCheckedOpen input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort mapped targetRoot targetWellFormed
  let outer := exposedContext input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort boundary mapped transport
  let sourceExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  let targetExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  let combined := Context.ofExact input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort input.val.root source.val.rootWires
    target.val.rootWires sourceExact targetExact
  let sourceRaw := ConcreteElaboration.rootEnvironment source.val.exposedWires
    source.val.hiddenWires sourceOuter sourceLocal
  let targetRaw : Fin target.val.rootWires.length → D :=
    sourceRaw ∘ combined.sourceIndex
  let targetLocal : Fin target.val.hiddenWires.length → D := fun index ↦
    targetRaw
      (Splice.Input.TwoInputPresentation.rootHiddenIndex target.val index)
  refine ⟨targetLocal, ?_⟩
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    combined.sourceIndex _ _).mpr
  have outerEq : sourceOuter ∘ outer.sourceIndex = targetOuter := by
    simpa [outer, Context.indexRelation] using outerAgrees
  have exposedEq : (fun index ↦ targetRaw
      (Splice.Input.TwoInputPresentation.rootExposedIndex target.val index)) =
      targetOuter := by
    funext targetIndex
    let targetFull :=
      Splice.Input.TwoInputPresentation.rootExposedIndex target.val targetIndex
    let sourceIndex := outer.sourceIndex targetIndex
    let sourceFull :=
      Splice.Input.TwoInputPresentation.rootExposedIndex source.val sourceIndex
    have mappedEq : combined.sourceIndex targetFull = sourceFull := by
      apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
      have sourceGet : source.val.rootWires.get sourceFull =
          source.val.exposedWires.get sourceIndex := by
        simpa only [sourceFull] using rootExposedIndex_get source.val sourceIndex
      have targetGet : target.val.rootWires.get targetFull =
          target.val.exposedWires.get targetIndex := by
        simpa only [targetFull] using rootExposedIndex_get target.val targetIndex
      calc
        source.val.rootWires.get sourceFull =
            source.val.exposedWires.get sourceIndex := sourceGet
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.exposedWires.get targetIndex) := outer.get targetIndex
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.rootWires.get targetFull) :=
          congrArg (fusionWireDomain input.val consumedWire).origin targetGet.symm
    calc
      targetRaw targetFull = sourceRaw sourceFull := by
        simp only [targetRaw, Function.comp_apply, mappedEq]
      _ = sourceOuter sourceIndex := by
        exact Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
          source.val sourceOuter sourceLocal sourceIndex
      _ = targetOuter targetIndex := congrFun outerEq targetIndex
  have rebuilt := Splice.Input.TwoInputPresentation.rootEnvironment_of_complete
    target.val targetRaw
  rw [exposedEq] at rebuilt
  exact rebuilt.symm

theorem rootEnvironment_backward_regular
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (regular : input.val.root ≠ producerRegion)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (sourceOuter : Fin (sourceOpen input boundary).exposedWires.length → D)
    (targetOuter : Fin (targetOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped).exposedWires.length → D)
    (outerAgrees : ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      (exposedContext input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort boundary mapped transport).indexRelation
      sourceOuter targetOuter)
    (targetLocal : Fin (targetOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped).hiddenWires.length → D) :
    ∃ sourceLocal : Fin (sourceOpen input boundary).hiddenWires.length → D,
      let source := sourceCheckedOpen input boundary sourceRoot
      let target := targetCheckedOpen input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort mapped targetRoot targetWellFormed
      let combined := Context.ofExact input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort input.val.root source.val.rootWires
        target.val.rootWires
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source)
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target)
      combined.indexRelation.EnvironmentsAgree
        (ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceLocal)
        (ConcreteElaboration.rootEnvironment target.val.exposedWires
          target.val.hiddenWires targetOuter targetLocal) := by
  let source := sourceCheckedOpen input boundary sourceRoot
  let target := targetCheckedOpen input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort mapped targetRoot targetWellFormed
  let outer := exposedContext input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort boundary mapped transport
  let sourceExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  let targetExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  let combined := Context.ofExact input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort input.val.root source.val.rootWires
    target.val.rootWires sourceExact targetExact
  let targetRaw := ConcreteElaboration.rootEnvironment target.val.exposedWires
    target.val.hiddenWires targetOuter targetLocal
  have hiddenSurvives : ∀ index : Fin source.val.hiddenWires.length,
      source.val.hiddenWires.get index ≠ consumedWire := by
    intro index equality
    have rootScope := (OpenConcreteDiagram.mem_hiddenWires source.val
      (source.val.hiddenWires.get index)).1
      (List.get_mem source.val.hiddenWires index) |>.1
    rw [equality] at rootScope
    exact regular (scope.trans rootScope).symm
  let mappedHidden : Fin source.val.hiddenWires.length →
      Fin (fusionWireDomain input.val consumedWire).count := fun index ↦
    (fusionWireDomain input.val consumedWire).index
      (source.val.hiddenWires.get index) (by
        change decide
          ((show Fin input.val.wireCount from
            source.val.hiddenWires.get index) ≠ consumedWire) = true
        exact decide_eq_true (hiddenSurvives index))
  have mappedHiddenOrigin : ∀ index,
      (fusionWireDomain input.val consumedWire).origin (mappedHidden index) =
        source.val.hiddenWires.get index := by
    intro index
    exact (fusionWireDomain input.val consumedWire).origin_index _ (by
      change decide
        ((show Fin input.val.wireCount from
          source.val.hiddenWires.get index) ≠ consumedWire) = true
      exact decide_eq_true (hiddenSurvives index))
  have mappedHiddenRoot : ∀ index,
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires (mappedHidden index)).scope = input.val.root := by
    intro index
    rw [fusionRaw_wire_scope, mappedHiddenOrigin]
    exact (OpenConcreteDiagram.mem_hiddenWires source.val _).1
      (List.get_mem source.val.hiddenWires index) |>.1
  have mappedHiddenVisible : ∀ index,
      target.val.diagram.Encloses
        (target.val.diagram.wires (mappedHidden index)).scope
        target.val.diagram.root := by
    intro index
    have scopeRoot : (target.val.diagram.wires (mappedHidden index)).scope =
        target.val.diagram.root := by
      simpa [target, targetCheckedOpen, targetOpen] using mappedHiddenRoot index
    rw [scopeRoot]
    exact ConcreteDiagram.Encloses.refl _ _
  let targetIndex : Fin source.val.hiddenWires.length →
      Fin target.val.rootWires.length := fun index ↦
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((targetExact.mem_iff (mappedHidden index)).2
        (mappedHiddenVisible index)))
  have targetIndexGet : ∀ index,
      target.val.rootWires.get (targetIndex index) = mappedHidden index := by
    intro index
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
        ((targetExact.mem_iff (mappedHidden index)).2
          (mappedHiddenVisible index))))
  let sourceLocal : Fin source.val.hiddenWires.length → D := fun index ↦
    targetRaw (targetIndex index)
  refine ⟨sourceLocal, ?_⟩
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    combined.sourceIndex _ _).mpr
  have outerEq : sourceOuter ∘ outer.sourceIndex = targetOuter := by
    simpa [outer, Context.indexRelation] using outerAgrees
  funext targetFull
  let lengthEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split : Fin (target.val.exposedWires.length +
      target.val.hiddenWires.length) := Fin.cast lengthEq targetFull
  have recover : Fin.cast lengthEq.symm split = targetFull := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun targetExposed ↦ ?_)
    (fun targetHidden ↦ ?_) split
  · let targetAt :=
      Splice.Input.TwoInputPresentation.rootExposedIndex target.val
        targetExposed
    let sourceExposed := outer.sourceIndex targetExposed
    let sourceAt :=
      Splice.Input.TwoInputPresentation.rootExposedIndex source.val
        sourceExposed
    have combinedEq : combined.sourceIndex targetAt = sourceAt := by
      apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
      have sourceGet : source.val.rootWires.get sourceAt =
          source.val.exposedWires.get sourceExposed := by
        simpa only [sourceAt] using
          rootExposedIndex_get source.val sourceExposed
      have targetGet : target.val.rootWires.get targetAt =
          target.val.exposedWires.get targetExposed := by
        simpa only [targetAt] using
          rootExposedIndex_get target.val targetExposed
      calc
        source.val.rootWires.get sourceAt =
            source.val.exposedWires.get sourceExposed := sourceGet
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.exposedWires.get targetExposed) := outer.get targetExposed
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.rootWires.get targetAt) :=
          congrArg (fusionWireDomain input.val consumedWire).origin targetGet.symm
    change (ConcreteElaboration.rootEnvironment source.val.exposedWires
        source.val.hiddenWires sourceOuter sourceLocal ∘ combined.sourceIndex)
      targetAt = targetRaw targetAt
    rw [Function.comp_apply, combinedEq]
    exact (Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
      source.val sourceOuter sourceLocal sourceExposed).trans
        ((congrFun outerEq targetExposed).trans
          (Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
            target.val targetOuter targetLocal targetExposed).symm)
  · let targetAt :=
      Splice.Input.TwoInputPresentation.rootHiddenIndex target.val targetHidden
    let targetWire := target.val.hiddenWires.get targetHidden
    let sourceWire := (fusionWireDomain input.val consumedWire).origin targetWire
    have targetAtGet : target.val.rootWires.get targetAt = targetWire := by
      simpa only [targetAt, targetWire] using
        rootHiddenIndex_get target.val targetHidden
    have sourceWireRoot : (input.val.wires sourceWire).scope = input.val.root := by
      have targetWireRoot := (OpenConcreteDiagram.mem_hiddenWires target.val
        targetWire).1 (List.get_mem target.val.hiddenWires targetHidden) |>.1
      simpa only [fusionRaw_wire_scope, sourceWire] using targetWireRoot
    have sourceWireAbsent : sourceWire ∉ boundary := by
      intro sourceMember
      have sourceSurvives : sourceWire ≠ consumedWire := by
        have survives := (fusionWireDomain input.val consumedWire).origin_survives
          targetWire
        simpa [sourceWire, fusionWireDomain] using survives
      let mappedWire := (fusionWireDomain input.val consumedWire).index
        sourceWire (by simp [fusionWireDomain, sourceSurvives])
      have mappedEq : mappedWire = targetWire := by
        simpa [mappedWire, sourceWire] using
          (fusionWireDomain input.val consumedWire).index_origin targetWire
      have image := interface_image_survivor input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort sourceWire sourceSurvives sourceWireRoot
      have targetMember := boundary_image_mem
        (fusionInterfaceTransport input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort) boundary mapped transport sourceWire mappedWire
          sourceMember image
      rw [mappedEq] at targetMember
      exact (OpenConcreteDiagram.mem_hiddenWires target.val targetWire).1
        (List.get_mem target.val.hiddenWires targetHidden) |>.2
        ((OpenConcreteDiagram.mem_exposedWires target.val targetWire).2
          targetMember)
    have sourceHiddenMember : sourceWire ∈ source.val.hiddenWires :=
      (OpenConcreteDiagram.mem_hiddenWires source.val sourceWire).2
        ⟨sourceWireRoot,
          fun exposed ↦ sourceWireAbsent
            ((OpenConcreteDiagram.mem_exposedWires source.val sourceWire).1
              exposed)⟩
    obtain ⟨sourceHidden, sourceLookup⟩ :=
      ConcreteElaboration.WireContext.lookup?_complete sourceHiddenMember
    have sourceHiddenGet : source.val.hiddenWires.get sourceHidden = sourceWire :=
      ConcreteElaboration.WireContext.lookup?_sound sourceLookup
    let sourceAt :=
      Splice.Input.TwoInputPresentation.rootHiddenIndex source.val sourceHidden
    have sourceAtGet : source.val.rootWires.get sourceAt = sourceWire := by
      exact (rootHiddenIndex_get source.val sourceHidden).trans sourceHiddenGet
    have combinedEq : combined.sourceIndex targetAt = sourceAt := by
      apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
      calc
        source.val.rootWires.get sourceAt = sourceWire := sourceAtGet
        _ = (fusionWireDomain input.val consumedWire).origin targetWire := rfl
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.rootWires.get targetAt) := congrArg _ targetAtGet.symm
    have hiddenIndexEq : targetIndex sourceHidden = targetAt := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        have mappedEq : mappedHidden sourceHidden = targetWire := by
          apply (fusionWireDomain input.val consumedWire).origin_injective
          rw [mappedHiddenOrigin, sourceHiddenGet]
        exact (targetIndexGet sourceHidden).trans
          (mappedEq.trans targetAtGet.symm))
    change (ConcreteElaboration.rootEnvironment source.val.exposedWires
        source.val.hiddenWires sourceOuter sourceLocal ∘ combined.sourceIndex)
      targetAt = targetRaw targetAt
    rw [Function.comp_apply, combinedEq]
    calc
      ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceLocal sourceAt =
          sourceLocal sourceHidden :=
        Splice.Input.TwoInputPresentation.rootEnvironment_rootHiddenIndex
          source.val sourceOuter sourceLocal sourceHidden
      _ = targetRaw (targetIndex sourceHidden) := rfl
      _ = targetRaw targetAt := congrArg targetRaw hiddenIndexEq

noncomputable def focusedRootBackwardSourceLocal
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort.val }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort.val },
          { node := producer, port := CPort.output }])
    (rootSite : input.val.root = producerRegion)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (targetExact : ConcreteElaboration.WireContext.Exact
      (targetCheckedOpen input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort mapped targetRoot targetWellFormed).val.rootWires
      input.val.root)
    (model : Lambda.LambdaModel)
    (targetRaw : Fin (List.length
      (targetCheckedOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped targetRoot targetWellFormed).val.rootWires)
      → model.Carrier) :
    Fin (sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.length →
      model.Carrier := by
  let source := sourceCheckedOpen input boundary sourceRoot
  let target := targetCheckedOpen input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort mapped targetRoot targetWellFormed
  have targetExactAtProducer : ConcreteElaboration.WireContext.Exact
      target.val.rootWires producerRegion := by
    simpa [target, rootSite] using targetExact
  let producerTargetIndex : Fin producerPorts →
      Fin target.val.rootWires.length := fun port ↦
    targetIndexOfSurvivor input consumedWire producer consumer hdistinct
      producerRegion consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort target.val.rootWires targetExactAtProducer
      (producerWire port)
      (producerWire_ne_consumed input consumedWire producer consumer hdistinct
        producerPorts producerWire consumedPort.val producerResolved endpoints
        port)
      (producerWire_encloses_producer input producer producerRegion producerPorts
        producerTerm producerWire producerShape producerResolved port)
  let termValue := model.eval producerTerm (targetRaw ∘ producerTargetIndex)
  exact fun sourceHidden ↦
    let wire := source.val.hiddenWires.get sourceHidden
    if selected : wire = consumedWire then termValue
    else
      let targetIndex := targetIndexOfSurvivor input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort target.val.rootWires
        targetExactAtProducer wire selected (by
          have wireRoot := (OpenConcreteDiagram.mem_hiddenWires source.val wire).1
            (List.get_mem source.val.hiddenWires sourceHidden) |>.1
          have wireProducer : (input.val.wires wire).scope = producerRegion := by
            have wireRoot' : (input.val.wires wire).scope = input.val.root := by
              simpa [source] using wireRoot
            exact wireRoot'.trans rootSite
          rw [wireProducer]
          exact ConcreteDiagram.Encloses.refl input.val producerRegion)
      targetRaw targetIndex

theorem focusedRootBackwardWitness
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort.val }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort.val },
          { node := producer, port := CPort.output }])
    (rootSite : input.val.root = producerRegion)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (sourceOuter : Fin (sourceOpen input boundary).exposedWires.length →
      model.Carrier)
    (targetOuter : Fin (targetOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped).exposedWires.length → model.Carrier)
    (outerAgrees : ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      (exposedContext input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort boundary mapped transport).indexRelation
      sourceOuter targetOuter)
    (targetLocal : Fin (targetOpen input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort mapped).hiddenWires.length → model.Carrier)
    (consumedIndex : Fin (sourceOpen input boundary).rootWires.length)
    (consumedGet : (sourceOpen input boundary).rootWires.get consumedIndex =
      consumedWire)
    (producerIndex : Fin producerPorts →
      Fin (sourceOpen input boundary).rootWires.length)
    (producerGet : ∀ port,
      (sourceOpen input boundary).rootWires.get (producerIndex port) =
        producerWire port) :
    ∃ sourceLocal : Fin (sourceOpen input boundary).hiddenWires.length →
        model.Carrier,
      let source := sourceCheckedOpen input boundary sourceRoot
      let target := targetCheckedOpen input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort mapped targetRoot targetWellFormed
      let combined := Context.ofExact input consumedWire producer consumer
        hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort input.val.root source.val.rootWires
        target.val.rootWires
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source)
        (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target)
      let sourceRaw := ConcreteElaboration.rootEnvironment
        source.val.exposedWires source.val.hiddenWires sourceOuter sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment
        target.val.exposedWires target.val.hiddenWires targetOuter targetLocal
      combined.indexRelation.EnvironmentsAgree sourceRaw targetRaw ∧
        sourceRaw consumedIndex =
          model.eval producerTerm (sourceRaw ∘ producerIndex) := by
  let source := sourceCheckedOpen input boundary sourceRoot
  let target := targetCheckedOpen input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort mapped targetRoot targetWellFormed
  let outer := exposedContext input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort boundary mapped transport
  let sourceExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  let targetExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  have targetExactAtProducer : ConcreteElaboration.WireContext.Exact
      target.val.rootWires producerRegion := by
    simpa [target, targetCheckedOpen, targetOpen, rootSite] using targetExact
  let combined := Context.ofExact input consumedWire producer consumer
    hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort input.val.root source.val.rootWires
    target.val.rootWires sourceExact targetExact
  let targetRaw : Fin target.val.rootWires.length → model.Carrier :=
    ConcreteElaboration.rootEnvironment target.val.exposedWires
      target.val.hiddenWires targetOuter targetLocal
  let sourceLocal := focusedRootBackwardSourceLocal input consumedWire producer
    consumer hdistinct producerRegion consumerRegion producerPorts consumerPorts
    producerTerm consumerTerm producerWire consumerWire consumedPort
    producerShape scope producerResolved endpoints rootSite boundary mapped
    sourceRoot targetRoot targetWellFormed
    (by simpa [target] using targetExact) model (by simpa [target] using targetRaw)
  let sourceRaw : Fin source.val.rootWires.length → model.Carrier :=
    ConcreteElaboration.rootEnvironment source.val.exposedWires
      source.val.hiddenWires sourceOuter sourceLocal
  have outerEq : sourceOuter ∘ outer.sourceIndex = targetOuter := by
    simpa [outer, Context.indexRelation] using outerAgrees
  have agreement : combined.indexRelation.EnvironmentsAgree sourceRaw targetRaw := by
    apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
      combined.sourceIndex _ _).mpr
    funext targetFull
    let lengthEq : target.val.rootWires.length =
        target.val.exposedWires.length + target.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let split := Fin.cast lengthEq targetFull
    have recover : Fin.cast lengthEq.symm split = targetFull := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun targetExposed ↦ ?_)
      (fun targetHidden ↦ ?_) split
    · let targetAt :=
        Splice.Input.TwoInputPresentation.rootExposedIndex target.val
          targetExposed
      let sourceExposed := outer.sourceIndex targetExposed
      let sourceAt :=
        Splice.Input.TwoInputPresentation.rootExposedIndex source.val
          sourceExposed
      have combinedEq : combined.sourceIndex targetAt = sourceAt := by
        apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
        have sourceGet : source.val.rootWires.get sourceAt =
            source.val.exposedWires.get sourceExposed := by
          simpa only [sourceAt] using
            rootExposedIndex_get source.val sourceExposed
        have targetGet : target.val.rootWires.get targetAt =
            target.val.exposedWires.get targetExposed := by
          simpa only [targetAt] using
            rootExposedIndex_get target.val targetExposed
        calc
          source.val.rootWires.get sourceAt =
              source.val.exposedWires.get sourceExposed := sourceGet
          _ = (fusionWireDomain input.val consumedWire).origin
              (target.val.exposedWires.get targetExposed) := outer.get targetExposed
          _ = (fusionWireDomain input.val consumedWire).origin
              (target.val.rootWires.get targetAt) := congrArg _ targetGet.symm
      change (sourceRaw ∘ combined.sourceIndex) targetAt = targetRaw targetAt
      rw [Function.comp_apply, combinedEq]
      exact (Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
        source.val sourceOuter sourceLocal sourceExposed).trans
          ((congrFun outerEq targetExposed).trans
            (Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
              target.val targetOuter targetLocal targetExposed).symm)
    · let targetAt :=
        Splice.Input.TwoInputPresentation.rootHiddenIndex target.val targetHidden
      let targetWire := target.val.hiddenWires.get targetHidden
      let sourceWire := (fusionWireDomain input.val consumedWire).origin targetWire
      have targetAtGet : target.val.rootWires.get targetAt = targetWire := by
        simpa only [targetAt, targetWire] using
          rootHiddenIndex_get target.val targetHidden
      have sourceWireRoot : (input.val.wires sourceWire).scope = input.val.root := by
        have targetWireRoot := (OpenConcreteDiagram.mem_hiddenWires target.val
          targetWire).1 (List.get_mem target.val.hiddenWires targetHidden) |>.1
        simpa only [fusionRaw_wire_scope, sourceWire] using targetWireRoot
      have sourceWireSurvives : sourceWire ≠ consumedWire := by
        have survives := (fusionWireDomain input.val consumedWire).origin_survives
          targetWire
        simpa [sourceWire, fusionWireDomain] using survives
      have sourceWireAbsent : sourceWire ∉ boundary := by
        intro sourceMember
        let mappedWire := (fusionWireDomain input.val consumedWire).index
          sourceWire (by simp [fusionWireDomain, sourceWireSurvives])
        have mappedEq : mappedWire = targetWire := by
          simpa [mappedWire, sourceWire] using
            (fusionWireDomain input.val consumedWire).index_origin targetWire
        have image := interface_image_survivor input consumedWire producer
          consumer hdistinct consumerRegion producerTerm consumerTerm
          producerWire consumerWire consumedPort sourceWire sourceWireSurvives
          sourceWireRoot
        have targetMember := boundary_image_mem
          (fusionInterfaceTransport input consumedWire producer consumer
            hdistinct consumerRegion producerTerm consumerTerm producerWire
            consumerWire consumedPort) boundary mapped transport sourceWire
            mappedWire sourceMember image
        rw [mappedEq] at targetMember
        exact (OpenConcreteDiagram.mem_hiddenWires target.val targetWire).1
          (List.get_mem target.val.hiddenWires targetHidden) |>.2
          ((OpenConcreteDiagram.mem_exposedWires target.val targetWire).2
            targetMember)
      have sourceHiddenMember : sourceWire ∈ source.val.hiddenWires :=
        (OpenConcreteDiagram.mem_hiddenWires source.val sourceWire).2
          ⟨sourceWireRoot, fun exposed ↦ sourceWireAbsent
            ((OpenConcreteDiagram.mem_exposedWires source.val sourceWire).1
              exposed)⟩
      obtain ⟨sourceHidden, sourceLookup⟩ :=
        ConcreteElaboration.WireContext.lookup?_complete sourceHiddenMember
      have sourceHiddenGet : source.val.hiddenWires.get sourceHidden =
          sourceWire := ConcreteElaboration.WireContext.lookup?_sound sourceLookup
      let sourceAt :=
        Splice.Input.TwoInputPresentation.rootHiddenIndex source.val sourceHidden
      have sourceAtGet : source.val.rootWires.get sourceAt = sourceWire :=
        (rootHiddenIndex_get source.val sourceHidden).trans sourceHiddenGet
      have combinedEq : combined.sourceIndex targetAt = sourceAt := by
        apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
        calc
          source.val.rootWires.get sourceAt = sourceWire := sourceAtGet
          _ = (fusionWireDomain input.val consumedWire).origin targetWire := rfl
          _ = (fusionWireDomain input.val consumedWire).origin
              (target.val.rootWires.get targetAt) := congrArg _ targetAtGet.symm
      have sourceVisible : input.val.Encloses
          (input.val.wires sourceWire).scope producerRegion := by
        rw [sourceWireRoot, rootSite]
        exact ConcreteDiagram.Encloses.refl _ _
      let selectedTarget := targetIndexOfSurvivor input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort target.val.rootWires
        targetExactAtProducer sourceWire sourceWireSurvives sourceVisible
      have selectedTargetEq : selectedTarget = targetAt := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          apply (fusionWireDomain input.val consumedWire).origin_injective
          have selectedOrigin := targetIndexOfSurvivor_origin_get input
            consumedWire producer consumer hdistinct producerRegion
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort target.val.rootWires targetExactAtProducer sourceWire
            sourceWireSurvives sourceVisible
          calc
            (fusionWireDomain input.val consumedWire).origin
                (target.val.rootWires.get selectedTarget) = sourceWire :=
              selectedOrigin
            _ = (fusionWireDomain input.val consumedWire).origin targetWire := rfl
            _ = (fusionWireDomain input.val consumedWire).origin
                (target.val.rootWires.get targetAt) := congrArg _ targetAtGet.symm)
      change (sourceRaw ∘ combined.sourceIndex) targetAt = targetRaw targetAt
      rw [Function.comp_apply, combinedEq]
      calc
        sourceRaw sourceAt = sourceLocal sourceHidden := by
          simpa only [sourceRaw, sourceAt] using
            Splice.Input.TwoInputPresentation.rootEnvironment_rootHiddenIndex
              source.val sourceOuter sourceLocal sourceHidden
        _ = targetRaw selectedTarget := by
          simp only [sourceLocal, focusedRootBackwardSourceLocal]
          have sourceHiddenGetOpen :
              (sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
                sourceHidden =
                sourceWire := by
            simpa [source] using sourceHiddenGet
          have sourceHiddenNe :
              (sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
                sourceHidden ≠ consumedWire := by
            rw [sourceHiddenGetOpen]
            exact sourceWireSurvives
          rw [dif_neg sourceHiddenNe]
          have actualVisible : input.val.Encloses
              (input.val.wires
                ((sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
                  sourceHidden)).scope producerRegion := by
            exact (congrArg (fun wire ↦ input.val.Encloses
              (input.val.wires wire).scope producerRegion)
              sourceHiddenGetOpen).mpr sourceVisible
          let actualTarget := targetIndexOfSurvivor input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerTerm
            consumerTerm producerWire consumerWire consumedPort
            target.val.rootWires targetExactAtProducer
            ((sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
              sourceHidden) sourceHiddenNe actualVisible
          change targetRaw actualTarget = targetRaw selectedTarget
          apply congrArg targetRaw
          apply Fin.ext
          exact (List.getElem_inj (xs := target.val.rootWires)
            (i := actualTarget.val) (j := selectedTarget.val)
            (h₀ := actualTarget.isLt) (h₁ := selectedTarget.isLt)
            targetExact.nodup).mp (by
            apply (fusionWireDomain input.val consumedWire).origin_injective
            have actualOrigin := targetIndexOfSurvivor_origin_get input
              consumedWire producer consumer hdistinct producerRegion
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort target.val.rootWires targetExactAtProducer
              ((sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
                sourceHidden)
              sourceHiddenNe actualVisible
            have selectedOrigin := targetIndexOfSurvivor_origin_get input
              consumedWire producer consumer hdistinct producerRegion
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort target.val.rootWires targetExactAtProducer sourceWire
              sourceWireSurvives sourceVisible
            have originsEq := actualOrigin.trans
              (sourceHiddenGetOpen.trans selectedOrigin.symm)
            simpa [actualTarget, selectedTarget] using originsEq)
        _ = targetRaw targetAt := congrArg targetRaw selectedTargetEq
  have consumedRoot : (input.val.wires consumedWire).scope = input.val.root := by
    exact scope.symm.trans rootSite.symm
  have consumedAbsent := consumed_not_mem_boundary input consumedWire producer
    consumer hdistinct consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort boundary mapped transport
  have consumedHiddenMember : consumedWire ∈ source.val.hiddenWires :=
    (OpenConcreteDiagram.mem_hiddenWires source.val consumedWire).2
      ⟨consumedRoot, fun exposed ↦ consumedAbsent
        ((OpenConcreteDiagram.mem_exposedWires source.val consumedWire).1
          exposed)⟩
  obtain ⟨consumedHidden, consumedLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete consumedHiddenMember
  have consumedHiddenGet : source.val.hiddenWires.get consumedHidden =
      consumedWire := ConcreteElaboration.WireContext.lookup?_sound consumedLookup
  let consumedAt :=
    Splice.Input.TwoInputPresentation.rootHiddenIndex source.val consumedHidden
  have consumedAtGet : source.val.rootWires.get consumedAt = consumedWire :=
    (rootHiddenIndex_get source.val consumedHidden).trans consumedHiddenGet
  have consumedIndexEq : consumedIndex = consumedAt := by
    apply Fin.ext
    exact (List.getElem_inj sourceExact.nodup).mp
      (consumedGet.trans consumedAtGet.symm)
  have producerValues : ∀ port,
      sourceRaw (producerIndex port) = targetRaw
        (targetIndexOfSurvivor input consumedWire producer consumer hdistinct
          producerRegion consumerRegion producerTerm consumerTerm producerWire
          consumerWire consumedPort target.val.rootWires targetExactAtProducer
          (producerWire port)
          (producerWire_ne_consumed input consumedWire producer consumer
            hdistinct producerPorts producerWire consumedPort.val
            producerResolved endpoints port)
          (producerWire_encloses_producer input producer producerRegion
            producerPorts producerTerm producerWire producerShape
            producerResolved port)) := by
    intro port
    let targetIndex := targetIndexOfSurvivor input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort target.val.rootWires
      targetExactAtProducer (producerWire port)
      (producerWire_ne_consumed input consumedWire producer consumer hdistinct
        producerPorts producerWire consumedPort.val producerResolved endpoints
        port)
      (producerWire_encloses_producer input producer producerRegion producerPorts
        producerTerm producerWire producerShape producerResolved port)
    have combinedEq : combined.sourceIndex targetIndex = producerIndex port := by
      apply Context.sourceIndex_eq_of_get combined sourceExact.nodup
      have producerGet' : source.val.rootWires.get (producerIndex port) =
          producerWire port := by
        simpa [source, sourceCheckedOpen] using producerGet port
      calc
        source.val.rootWires.get (producerIndex port) = producerWire port :=
          producerGet'
        _ = (fusionWireDomain input.val consumedWire).origin
            (target.val.rootWires.get targetIndex) :=
          (targetIndexOfSurvivor_origin_get input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerTerm
            consumerTerm producerWire consumerWire consumedPort
            target.val.rootWires targetExactAtProducer (producerWire port)
            (producerWire_ne_consumed input consumedWire producer consumer
              hdistinct producerPorts producerWire consumedPort.val
              producerResolved endpoints port)
            (producerWire_encloses_producer input producer producerRegion
              producerPorts producerTerm producerWire producerShape
              producerResolved port)).symm
    have agreementEq : sourceRaw ∘ combined.sourceIndex = targetRaw := by
      simpa [combined, Context.indexRelation] using agreement
    calc
      sourceRaw (producerIndex port) =
          sourceRaw (combined.sourceIndex targetIndex) :=
        congrArg sourceRaw combinedEq.symm
      _ = targetRaw targetIndex := congrFun agreementEq targetIndex
  refine ⟨sourceLocal, agreement, ?_⟩
  rw [consumedIndexEq]
  have sourceRawConsumed : sourceRaw consumedAt = sourceLocal consumedHidden := by
    simpa only [sourceRaw, consumedAt] using
      Splice.Input.TwoInputPresentation.rootEnvironment_rootHiddenIndex
        source.val sourceOuter sourceLocal consumedHidden
  change sourceRaw consumedAt =
    model.eval producerTerm (sourceRaw ∘ producerIndex)
  rw [sourceRawConsumed]
  have consumedHiddenGetOpen :
      (sourceCheckedOpen input boundary sourceRoot).val.hiddenWires.get
        consumedHidden = consumedWire := by
    simpa [source] using consumedHiddenGet
  simp only [sourceLocal, focusedRootBackwardSourceLocal]
  rw [dif_pos consumedHiddenGetOpen]
  apply congrArg (model.eval producerTerm)
  funext port
  exact (producerValues port).symm

/-- At a focused root, the deleted producer equation is discharged by the
hidden consumed-wire existential.  Every remaining root occurrence is
transported by the same producer-frame simulation used below the root. -/
theorem focusedRootTransport
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (consumerResolved : resolveNodeFreeWires? input consumer consumerPorts =
      some consumerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort.val }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort.val },
          { node := producer, port := CPort.output }])
    (producerEnclosesConsumer : input.val.Encloses producerRegion consumerRegion)
    (rootSite : input.val.root = producerRegion)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (fusionWireDomain input.val consumedWire).count))
    (transport : (fusionInterfaceTransport input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort).transportBoundary boundary = some mapped)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetRoot : ∀ wire, wire ∈ mapped →
      ((fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort).wires wire).scope = input.val.root)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceItems : ItemSeq signature
      (sourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (targetOpen input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
        mapped).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) (sourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      (targetOpen input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
        mapped).rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire
          consumedPort).root) = some targetItems) :
    ConcreteElaboration.DirectionalRootTransport direction
      (sourceOpen input boundary).exposedWires
      (sourceOpen input boundary).hiddenWires
      (targetOpen input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
        mapped).exposedWires
      (targetOpen input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
        mapped).hiddenWires
      (exposedContext input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort boundary mapped transport).indexRelation
      model named sourceItems targetItems := by
  let source := sourceCheckedOpen input boundary sourceRoot
  let target := targetCheckedOpen input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort mapped targetRoot targetWellFormed
  let sourceContext := source.val.rootWires
  let targetContext := target.val.rootWires
  let context := Context.ofExact input consumedWire producer consumer hdistinct
    consumerRegion producerTerm consumerTerm producerWire consumerWire
    consumedPort input.val.root sourceContext targetContext
    (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source)
    (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target)
  have sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      producerRegion := by
    rw [← rootSite]
    simpa [sourceContext, source] using
      (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        source)
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      producerRegion := by
    rw [← rootSite]
    simpa [targetContext, target, fusionRaw] using
      (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        target)
  have sourceCompiledFocus : ConcreteElaboration.compileOccurrencesWith?
      signature input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val producerRegion) =
        some sourceItems := by
    simpa [sourceContext, source, rootSite] using sourceCompiled
  have targetCompiledFocus : ConcreteElaboration.compileOccurrencesWith?
      signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        producerRegion) = some targetItems := by
    simpa [targetContext, target, fusionRaw, rootSite] using targetCompiled
  have producerMember : ConcreteElaboration.LocalOccurrence.node producer ∈
      ConcreteElaboration.localOccurrences input.val producerRegion := by
    rw [ConcreteElaboration.mem_localOccurrences_node, producerShape]
    rfl
  obtain ⟨before, after, localEq⟩ := List.append_of_mem producerMember
  have decomposedNodup :
      (before ++ ConcreteElaboration.LocalOccurrence.node producer :: after).Nodup := by
    rw [← localEq]
    exact ConcreteElaboration.localOccurrences_nodup input.val producerRegion
  have producerNotBefore :
      ConcreteElaboration.LocalOccurrence.node producer ∉ before := by
    intro member
    have parts := List.nodup_append.mp decomposedNodup
    exact parts.2.2 _ member _ (by simp) rfl
  have producerNotAfter :
      ConcreteElaboration.LocalOccurrence.node producer ∉ after := by
    have parts := List.nodup_append.mp decomposedNodup
    exact (List.nodup_cons.mp parts.2.1).1
  have sourceFramed : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext ConcreteElaboration.BinderContext.empty
      (before ++ .node producer :: after) = some sourceItems := by
    rw [← localEq]
    exact sourceCompiledFocus
  obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
      sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      sourceContext ConcreteElaboration.BinderContext.empty before after
      (.node producer) sourceItems sourceFramed
  have targetLocalEq : ConcreteElaboration.localOccurrences
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      producerRegion =
        before.map (mapOccurrence input producer) ++
          after.map (mapOccurrence input producer) := by
    rw [fusionRaw_producer_localOccurrences input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerPorts consumerPorts
      producerTerm consumerTerm producerWire consumerWire consumedPort
      producerShape consumerShape, localEq, List.filter_append]
    have beforeFilter : before.filter (fun occurrence ↦
        decide (occurrence ≠
          ConcreteElaboration.LocalOccurrence.node producer)) = before := by
      apply List.filter_eq_self.mpr
      intro occurrence member
      simp only [decide_eq_true_eq]
      intro equality
      subst occurrence
      exact producerNotBefore member
    have afterFilter : after.filter (fun occurrence ↦
        decide (occurrence ≠
          ConcreteElaboration.LocalOccurrence.node producer)) = after := by
      apply List.filter_eq_self.mpr
      intro occurrence member
      simp only [decide_eq_true_eq]
      intro equality
      subst occurrence
      exact producerNotAfter member
    have focusFilter :
        (ConcreteElaboration.LocalOccurrence.node producer :: after).filter
          (fun occurrence ↦ decide (occurrence ≠
            ConcreteElaboration.LocalOccurrence.node producer)) = after := by
      rw [List.filter_cons]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact afterFilter
    rw [beforeFilter]
    rw [focusFilter, List.map_append]
  have targetFramed : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty
      (before.map (mapOccurrence input producer) ++
        after.map (mapOccurrence input producer)) = some targetItems := by
    rw [← targetLocalEq]
    exact targetCompiledFocus
  obtain ⟨targetBefore, targetAfter, targetBeforeCompiled,
      targetAfterCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty
      (before.map (mapOccurrence input producer))
      (after.map (mapOccurrence input producer)) targetItems targetFramed
  obtain ⟨consumedIndex, producerIndex, consumedGet, producerGet,
      sourceFocusEq⟩ := producerFocus_compiled input consumedWire producer
    consumer producerRegion producerPorts producerTerm producerWire
    consumedPort.val producerShape producerResolved endpoints sourceContext
    ConcreteElaboration.BinderContext.empty
    (ConcreteElaboration.compileRegion? signature input.val fuelSource)
    sourceFocus sourceFocusCompiled
  subst sourceFocus
  have beforeLocal : ∀ occurrence, occurrence ∈ before →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val
        producerRegion := by
    intro occurrence member
    rw [localEq]
    simp [member]
  have afterLocal : ∀ occurrence, occurrence ∈ after →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val
        producerRegion := by
    intro occurrence member
    rw [localEq]
    simp [member]
  rw [sourceItemsEq, targetItemsEq]
  intro sourceOuter targetOuter relEnv outerAgrees
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      obtain ⟨targetLocal, completeAgrees⟩ := rootEnvironment_forward input
        consumedWire producer consumer hdistinct consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort boundary mapped
        transport sourceRoot targetRoot targetWellFormed sourceOuter targetOuter
        outerAgrees sourceLocal
      let sourceRaw := ConcreteElaboration.rootEnvironment
        (sourceOpen input boundary).exposedWires
        (sourceOpen input boundary).hiddenWires sourceOuter sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment
        (targetOpen input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort
          mapped).exposedWires
        (targetOpen input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort
          mapped).hiddenWires targetOuter targetLocal
      change denoteItemSeq model named sourceRaw relEnv
        (sourceBefore.append
          (.cons (.equation consumedIndex (producerTerm.mapFree producerIndex))
            sourceAfter)) at sourceDenotes
      have sourceParts := (denoteItemSeq_frame model named sourceRaw relEnv
        sourceBefore sourceAfter
        (.equation consumedIndex (producerTerm.mapFree producerIndex))).mp
          sourceDenotes
      rcases sourceParts with
        ⟨sourceBeforeDenotes, producerEquation, sourceAfterDenotes⟩
      have producerEquationRaw : sourceRaw consumedIndex =
          model.eval producerTerm (sourceRaw ∘ producerIndex) := by
        simpa [sourceRaw, denoteItem_equation, model.eval_mapFree] using
          producerEquation
      have beforeDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .forward fuelSource fuelTarget sourceContext targetContext
        context sourceExact targetExact ConcreteElaboration.BinderContext.empty
        before beforeLocal producerNotBefore consumedIndex consumedGet
        producerIndex producerGet sourceBefore targetBefore sourceBeforeCompiled
        targetBeforeCompiled sourceRaw targetRaw relEnv completeAgrees
        producerEquationRaw sourceBeforeDenotes
      have afterDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .forward fuelSource fuelTarget sourceContext targetContext
        context sourceExact targetExact ConcreteElaboration.BinderContext.empty
        after afterLocal producerNotAfter consumedIndex consumedGet producerIndex
        producerGet sourceAfter targetAfter sourceAfterCompiled
        targetAfterCompiled sourceRaw targetRaw relEnv completeAgrees
        producerEquationRaw sourceAfterDenotes
      refine ⟨targetLocal, ?_⟩
      change denoteItemSeq model named targetRaw relEnv
        (targetBefore.append targetAfter)
      exact (denoteItemSeq_append model named targetRaw relEnv targetBefore
        targetAfter).mpr ⟨beforeDenotes, afterDenotes⟩
  | backward =>
      intro targetLocal targetDenotes
      obtain ⟨sourceLocal, completeAgrees, producerEquation⟩ :=
        focusedRootBackwardWitness input consumedWire producer consumer hdistinct
          producerRegion consumerRegion producerPorts consumerPorts producerTerm
          consumerTerm producerWire consumerWire consumedPort producerShape scope
          producerResolved endpoints rootSite boundary mapped transport sourceRoot
          targetRoot targetWellFormed model sourceOuter targetOuter outerAgrees
          targetLocal consumedIndex consumedGet producerIndex producerGet
      let sourceRaw := ConcreteElaboration.rootEnvironment
        (sourceOpen input boundary).exposedWires
        (sourceOpen input boundary).hiddenWires sourceOuter sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment
        (targetOpen input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort
          mapped).exposedWires
        (targetOpen input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort
          mapped).hiddenWires targetOuter targetLocal
      change denoteItemSeq model named targetRaw relEnv
        (targetBefore.append targetAfter) at targetDenotes
      have targetParts := (denoteItemSeq_append model named targetRaw relEnv
        targetBefore targetAfter).mp targetDenotes
      rcases targetParts with ⟨targetBeforeDenotes, targetAfterDenotes⟩
      have beforeDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .backward fuelSource fuelTarget sourceContext targetContext
        context sourceExact targetExact ConcreteElaboration.BinderContext.empty
        before beforeLocal producerNotBefore consumedIndex consumedGet
        producerIndex producerGet sourceBefore targetBefore sourceBeforeCompiled
        targetBeforeCompiled sourceRaw targetRaw relEnv completeAgrees
        producerEquation targetBeforeDenotes
      have afterDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .backward fuelSource fuelTarget sourceContext targetContext
        context sourceExact targetExact ConcreteElaboration.BinderContext.empty
        after afterLocal producerNotAfter consumedIndex consumedGet producerIndex
        producerGet sourceAfter targetAfter sourceAfterCompiled
        targetAfterCompiled sourceRaw targetRaw relEnv completeAgrees
        producerEquation targetAfterDenotes
      refine ⟨sourceLocal, ?_⟩
      change denoteItemSeq model named sourceRaw relEnv
        (sourceBefore.append
          (.cons (.equation consumedIndex (producerTerm.mapFree producerIndex))
            sourceAfter))
      have producerDenotes : denoteItem model named sourceRaw relEnv
          (.equation consumedIndex (producerTerm.mapFree producerIndex)) := by
        simpa [denoteItem_equation, model.eval_mapFree] using producerEquation
      exact (denoteItemSeq_frame model named sourceRaw relEnv sourceBefore
        sourceAfter
        (.equation consumedIndex (producerTerm.mapFree producerIndex))).mpr
          ⟨beforeDenotes, producerDenotes, afterDenotes⟩

end FusionSoundness

end VisualProof.Rule
