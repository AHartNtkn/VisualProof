import VisualProof.Rule.Soundness.Equational.FusionRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FusionSoundness

private theorem filterFin_survivor_origin_at_focus
    (domain : SurvivorDomain size)
    (sourceP : Fin size → Bool)
    (targetP : domain.Carrier → Bool)
    (predicateEq : ∀ index, targetP index = sourceP (domain.origin index))
    (subset : ∀ original, sourceP original = true →
      domain.survives original = true) :
    (filterFin targetP).map domain.origin = filterFin sourceP := by
  have enumerationEq :
      (allFin domain.count).map domain.origin = domain.enumeration := by
    rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
    change List.ofFn (fun index ↦ domain.enumeration.get index) =
      domain.enumeration
    exact List.ofFn_getElem
  unfold filterFin
  have filterEq :
      List.filter targetP (allFin domain.count) =
        List.filter (sourceP ∘ domain.origin) (allFin domain.count) := by
    apply congrArg (fun predicate ↦
      List.filter predicate (allFin domain.count))
    funext index
    exact predicateEq index
  rw [filterEq, ← List.filter_map, enumerationEq]
  change List.filter sourceP
      (List.filter domain.survives (allFin size)) =
    List.filter sourceP (allFin size)
  rw [List.filter_filter]
  apply congrArg (fun predicate ↦ List.filter predicate (allFin size))
  funext original
  cases selected : sourceP original with
  | false => simp [selected]
  | true => simp [selected, subset original selected]

/-- At the focused producer site, the target occurrence order is exactly the
source order with the producer removed and every survivor compacted. -/
theorem fusionRaw_producer_localOccurrences
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
      .term consumerRegion consumerPorts consumerTerm) :
    ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        producerRegion =
      ((ConcreteElaboration.localOccurrences input.val producerRegion).filter
        fun occurrence ↦ decide (occurrence ≠
          ConcreteElaboration.LocalOccurrence.node producer)).map
        (mapOccurrence input producer) := by
  let domain := fusionNodeDomain input.val producer
  let sourceP : Fin input.val.nodeCount → Bool := fun node ↦
    decide ((input.val.nodes node).region = producerRegion)
  let survivingP : Fin input.val.nodeCount → Bool := fun node ↦
    sourceP node && domain.survives node
  let targetP : Fin domain.count → Bool := fun node ↦
    decide (((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).nodes node).region = producerRegion)
  have predicateEq : ∀ node,
      targetP node = survivingP (domain.origin node) := by
    intro node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true, targetP, survivingP, sourceP]
    constructor
    · intro targetRegion
      constructor
      · rw [fusionRaw_node_region input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerPorts consumerTerm producerWire
          consumerWire consumedPort consumerShape] at targetRegion
        exact targetRegion
      · exact domain.origin_survives node
    · rintro ⟨sourceRegion, _⟩
      rw [fusionRaw_node_region input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerPorts consumerTerm producerWire
        consumerWire consumedPort consumerShape]
      exact sourceRegion
  have subset : ∀ node, survivingP node = true →
      domain.survives node = true := by
    intro node selected
    simp only [survivingP, Bool.and_eq_true] at selected
    exact selected.2
  have origins := filterFin_survivor_origin_at_focus domain survivingP targetP
    predicateEq subset
  have sourceFilter : filterFin survivingP =
      (filterFin sourceP).filter fun node ↦ decide (node ≠ producer) := by
    unfold filterFin survivingP sourceP domain fusionNodeDomain
    rw [List.filter_filter]
    apply congrArg (fun predicate ↦ List.filter predicate (allFin input.val.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp [and_comm]
  have mappedOrigins :
      (filterFin targetP).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := input.val.regionCount)) =
        ((filterFin sourceP).filter fun node ↦ decide (node ≠ producer)).map
          (mapOccurrence input producer ∘
            ConcreteElaboration.LocalOccurrence.node) := by
    rw [← sourceFilter, ← origins, List.map_map]
    apply List.map_congr_left
    intro targetNode member
    change ConcreteElaboration.LocalOccurrence.node targetNode =
      mapOccurrence input producer
        (.node (domain.origin targetNode))
    rw [mapOccurrence_node input producer (domain.origin targetNode) (by
      have survives := domain.origin_survives targetNode
      simpa [domain, fusionNodeDomain] using survives)]
    congr 1
    exact (domain.index_origin targetNode).symm
  let children := filterFin fun child : Fin input.val.regionCount ↦
    decide ((input.val.regions child).parent? = some producerRegion)
  unfold ConcreteElaboration.localOccurrences
  change (filterFin targetP).map
      (ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount)) ++
      children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := domain.count)) = _
  rw [mappedOrigins, List.filter_append, List.map_append]
  have nodeFilter :
      (((filterFin sourceP).map
        (ConcreteElaboration.LocalOccurrence.node
          (regions := input.val.regionCount))).filter fun occurrence ↦
            decide (occurrence ≠
              ConcreteElaboration.LocalOccurrence.node producer)) =
        ((filterFin sourceP).filter fun node ↦ decide (node ≠ producer)).map
          ConcreteElaboration.LocalOccurrence.node := by
    rw [List.filter_map]
    apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg (fun predicate ↦ List.filter predicate (filterFin sourceP))
    funext node
    simp
  have childFilter :
      (children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := input.val.nodeCount))).filter (fun occurrence ↦
          decide (occurrence ≠
            ConcreteElaboration.LocalOccurrence.node producer)) =
        children.map ConcreteElaboration.LocalOccurrence.child := by
    apply List.filter_eq_self.mpr
    intro occurrence member
    rcases List.mem_map.mp member with ⟨child, _, rfl⟩
    simp
  rw [nodeFilter, childFilter, List.map_map]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro child _
  rfl

theorem producerWire_ne_consumed
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerPorts : Nat)
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumedPort : Nat)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort },
          { node := producer, port := CPort.output }])
    (port : Fin producerPorts) :
    producerWire port ≠ consumedWire := by
  intro equality
  have occurs := resolvedFreePort_occurs input producer producerPorts
    producerWire producerResolved port
  rw [equality] at occurs
  rcases endpoints with forward | backward
  · simp [ConcreteDiagram.EndpointOccurs, forward] at occurs
    exact hdistinct occurs.1
  · simp [ConcreteDiagram.EndpointOccurs, backward, hdistinct,
      Ne.symm hdistinct] at occurs

theorem producerWire_encloses_producer
    (input : CheckedDiagram signature)
    (producer : Fin input.val.nodeCount)
    (producerRegion : Fin input.val.regionCount)
    (producerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (port : Fin producerPorts) :
    input.val.Encloses (input.val.wires (producerWire port)).scope
      producerRegion := by
  have encloses := input.property.wire_scopes_enclose (producerWire port)
    { node := producer, port := .free port }
    (resolvedFreePort_occurs input producer producerPorts producerWire
      producerResolved port)
  simpa [producerShape] using encloses

noncomputable def targetIndexOfSurvivor
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
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (targetExact : target.Exact producerRegion)
    (wire : Fin input.val.wireCount)
    (survives : wire ≠ consumedWire)
    (visible : input.val.Encloses (input.val.wires wire).scope producerRegion) :
    Fin target.length :=
  let domain := fusionWireDomain input.val consumedWire
  let mapped := domain.index wire (by
    simp [domain, fusionWireDomain, survives])
  visibleIndex
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort)
    target producerRegion targetExact mapped (by
      have targetEncloses := (fusionRaw_encloses_iff input consumedWire producer
        consumer hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort (input.val.wires wire).scope
        producerRegion).mpr visible
      have mappedOrigin : (fusionWireDomain input.val consumedWire).origin
          mapped = wire := by
        simpa [domain] using domain.origin_index wire (by
          simp [domain, fusionWireDomain, survives])
      simpa only [fusionRaw_wire_scope, mappedOrigin] using targetEncloses)

theorem targetIndexOfSurvivor_origin_get
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
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (targetExact : target.Exact producerRegion)
    (wire : Fin input.val.wireCount)
    (survives : wire ≠ consumedWire)
    (visible : input.val.Encloses (input.val.wires wire).scope producerRegion) :
    (fusionWireDomain input.val consumedWire).origin
        (target.get (targetIndexOfSurvivor input consumedWire producer consumer
          hdistinct producerRegion consumerRegion producerTerm consumerTerm
          producerWire consumerWire consumedPort target targetExact wire survives
          visible)) = wire := by
  let domain := fusionWireDomain input.val consumedWire
  let mapped := domain.index wire (by
    simp [domain, fusionWireDomain, survives])
  have getMapped := visibleIndex_get
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort)
    target producerRegion targetExact mapped (by
      have targetEncloses := (fusionRaw_encloses_iff input consumedWire producer
        consumer hdistinct consumerRegion producerTerm consumerTerm producerWire
        consumerWire consumedPort (input.val.wires wire).scope
        producerRegion).mpr visible
      have mappedOrigin : (fusionWireDomain input.val consumedWire).origin
          mapped = wire := by
        simpa [domain] using domain.origin_index wire (by
          simp [domain, fusionWireDomain, survives])
      simpa only [fusionRaw_wire_scope, mappedOrigin] using targetEncloses)
  rw [show targetIndexOfSurvivor input consumedWire producer consumer hdistinct
      producerRegion consumerRegion producerTerm consumerTerm producerWire
      consumerWire consumedPort target targetExact wire survives visible =
        visibleIndex
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) target producerRegion targetExact mapped (by
              have targetEncloses := (fusionRaw_encloses_iff input consumedWire
                producer consumer hdistinct consumerRegion producerTerm
                consumerTerm producerWire consumerWire consumedPort
                (input.val.wires wire).scope producerRegion).mpr visible
              have mappedOrigin : (fusionWireDomain input.val consumedWire).origin
                  mapped = wire := by
                simpa [domain] using domain.origin_index wire (by
                  simp [domain, fusionWireDomain, survives])
              simpa only [fusionRaw_wire_scope, mappedOrigin] using
                targetEncloses) by rfl,
    getMapped]
  exact domain.origin_index wire (by
    simp [domain, fusionWireDomain, survives])

noncomputable def focusedBackwardSourceLocal
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
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (targetExact : target.Exact producerRegion)
    (model : Lambda.LambdaModel)
    (targetEnv : Fin target.length → model.Carrier) :
    Fin (ConcreteElaboration.exactScopeWires input.val producerRegion).length →
      model.Carrier :=
  let termValue := model.eval producerTerm (fun port ↦
    targetEnv (targetIndexOfSurvivor input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort target targetExact
      (producerWire port)
      (producerWire_ne_consumed input consumedWire producer consumer hdistinct
        producerPorts producerWire consumedPort.val producerResolved endpoints
        port)
      (producerWire_encloses_producer input producer producerRegion producerPorts
        producerTerm producerWire producerShape producerResolved port)))
  fun localIndex ↦
    let wire := (ConcreteElaboration.exactScopeWires input.val
      producerRegion).get localIndex
    if selected : wire = consumedWire then termValue
    else targetEnv (targetIndexOfSurvivor input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort target targetExact wire selected (by
        have wireScope := (ConcreteElaboration.mem_exactScopeWires input.val
          producerRegion wire).mp (List.get_mem _ localIndex)
        rw [wireScope]
        exact ConcreteDiagram.Encloses.refl input.val producerRegion))

theorem focusedBackwardExtendedAgreement
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
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (sourceExact : (source.extend producerRegion).Exact producerRegion)
    (targetExact : (target.extend producerRegion).Exact producerRegion)
    (model : Lambda.LambdaModel)
    (sourceOuter : Fin source.length → model.Carrier)
    (targetOuter : Fin target.length → model.Carrier)
    (outerEq : sourceOuter ∘ context.sourceIndex = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      producerRegion).length → model.Carrier) :
    let sourceLocal := focusedBackwardSourceLocal input consumedWire producer
      consumer hdistinct producerRegion consumerRegion producerPorts
      consumerPorts producerTerm consumerTerm producerWire consumerWire
      consumedPort producerShape scope producerResolved endpoints
      (target.extend producerRegion) targetExact model
      (fusionExtendedEnv target producerRegion targetOuter targetLocal)
    ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      (context.extend producerRegion sourceExact targetExact).indexRelation
      (fusionExtendedEnv source producerRegion sourceOuter sourceLocal)
      (fusionExtendedEnv target producerRegion targetOuter targetLocal) := by
  dsimp only
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    (context.extend producerRegion sourceExact targetExact).sourceIndex _ _).mpr
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend target producerRegion)
    targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend target producerRegion).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outerIndex ↦ ?_) (fun targetLocalIndex ↦ ?_) split
  · have mapped := context.extend_sourceIndex_inherited producerRegion
      sourceExact targetExact outerIndex
    simp only [Function.comp_apply, fusionExtendedEnv,
      ConcreteElaboration.extendedEnvironment, extendWireEnv]
    rw [mapped]
    simpa [Function.comp_def] using congrFun outerEq outerIndex
  · let targetFull : Fin (target.extend producerRegion).length := Fin.cast
      (ConcreteElaboration.WireContext.length_extend target producerRegion).symm
      (Fin.natAdd target.length targetLocalIndex)
    let targetWire := (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      producerRegion).get targetLocalIndex
    let sourceWire := (fusionWireDomain input.val consumedWire).origin targetWire
    have targetGet : (target.extend producerRegion).get targetFull =
        targetWire := by
      simpa [targetFull] using
        (ConcreteElaboration.WireContext.extend_local target producerRegion
          targetLocalIndex)
    have sourceWireNe : sourceWire ≠ consumedWire := by
      have survives := (fusionWireDomain input.val consumedWire).origin_survives
        targetWire
      simpa [sourceWire, fusionWireDomain] using survives
    have targetWireScope :
        ((fusionRaw input consumedWire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort).wires targetWire).scope = producerRegion :=
      (ConcreteElaboration.mem_exactScopeWires
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        producerRegion targetWire).mp (List.get_mem _ targetLocalIndex)
    have sourceWireScope : (input.val.wires sourceWire).scope = producerRegion := by
      simpa only [fusionRaw_wire_scope, sourceWire] using targetWireScope
    have sourceLocalMember : sourceWire ∈
        ConcreteElaboration.exactScopeWires input.val producerRegion :=
      (ConcreteElaboration.mem_exactScopeWires input.val producerRegion
        sourceWire).mpr sourceWireScope
    obtain ⟨sourceLocalIndex, sourceLookup⟩ :=
      ConcreteElaboration.WireContext.lookup?_complete sourceLocalMember
    have sourceLocalGet :
        (ConcreteElaboration.exactScopeWires input.val producerRegion).get
          sourceLocalIndex = sourceWire :=
      ConcreteElaboration.WireContext.lookup?_sound sourceLookup
    let sourceFull : Fin (source.extend producerRegion).length := Fin.cast
      (ConcreteElaboration.WireContext.length_extend source producerRegion).symm
      (Fin.natAdd source.length sourceLocalIndex)
    have sourceFullGet : (source.extend producerRegion).get sourceFull =
        sourceWire := by
      have localGet := ConcreteElaboration.WireContext.extend_local source
        producerRegion sourceLocalIndex
      simpa [sourceFull] using localGet.trans sourceLocalGet
    have mappedEq :
        (context.extend producerRegion sourceExact targetExact).sourceIndex
          targetFull = sourceFull := by
      apply Context.sourceIndex_eq_of_get _ sourceExact.nodup
      rw [sourceFullGet, targetGet]
    have sourceVisible : input.val.Encloses
        (input.val.wires sourceWire).scope producerRegion := by
      rw [sourceWireScope]
      exact ConcreteDiagram.Encloses.refl input.val producerRegion
    have targetIndexEq : targetIndexOfSurvivor input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort
        (target.extend producerRegion) targetExact sourceWire sourceWireNe
        sourceVisible = targetFull := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          (show (target.extend producerRegion).get
              (targetIndexOfSurvivor input consumedWire producer consumer
                hdistinct producerRegion consumerRegion producerTerm
                consumerTerm producerWire consumerWire consumedPort
                (target.extend producerRegion) targetExact sourceWire
                sourceWireNe sourceVisible) = targetWire by
            have originGet := targetIndexOfSurvivor_origin_get input
              consumedWire producer consumer hdistinct producerRegion
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort (target.extend producerRegion) targetExact sourceWire
              sourceWireNe sourceVisible
            have targetOriginInjective :=
              (fusionWireDomain input.val consumedWire).origin_injective
            apply targetOriginInjective
            simpa [sourceWire] using originGet).trans targetGet.symm)
    change (fusionExtendedEnv source producerRegion sourceOuter
        (focusedBackwardSourceLocal input consumedWire producer consumer
          hdistinct producerRegion consumerRegion producerPorts consumerPorts
          producerTerm consumerTerm producerWire consumerWire consumedPort
          producerShape scope producerResolved endpoints
          (target.extend producerRegion) targetExact model
          (fusionExtendedEnv target producerRegion targetOuter targetLocal)) ∘
        (context.extend producerRegion sourceExact targetExact).sourceIndex)
      targetFull =
        fusionExtendedEnv target producerRegion targetOuter targetLocal targetFull
    rw [Function.comp_apply, mappedEq]
    simp only [fusionExtendedEnv, ConcreteElaboration.extendedEnvironment,
      Function.comp_apply, extendWireEnv]
    have sourceFullCast : Fin.cast
        (ConcreteElaboration.WireContext.length_extend source producerRegion)
        sourceFull = Fin.natAdd source.length sourceLocalIndex := by
      apply Fin.ext
      rfl
    rw [sourceFullCast, Fin.addCases_right]
    simp only [focusedBackwardSourceLocal, sourceLocalGet, sourceWireNe,
      dite_false]
    rw [targetIndexEq]
    have targetFullCast : Fin.cast
        (ConcreteElaboration.WireContext.length_extend target producerRegion)
        targetFull = Fin.natAdd target.length targetLocalIndex := by
      apply Fin.ext
      rfl
    simp [Function.comp_apply, targetFullCast, extendWireEnv]

theorem focusedBackwardProducerEquation
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
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (sourceExact : (source.extend producerRegion).Exact producerRegion)
    (targetExact : (target.extend producerRegion).Exact producerRegion)
    (model : Lambda.LambdaModel)
    (sourceOuter : Fin source.length → model.Carrier)
    (targetOuter : Fin target.length → model.Carrier)
    (outerEq : sourceOuter ∘ context.sourceIndex = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      producerRegion).length → model.Carrier)
    (consumedIndex : Fin (source.extend producerRegion).length)
    (consumedGet : (source.extend producerRegion).get consumedIndex =
      consumedWire)
    (producerIndex : Fin producerPorts →
      Fin (source.extend producerRegion).length)
    (producerGet : ∀ port,
      (source.extend producerRegion).get (producerIndex port) =
        producerWire port) :
    let targetRaw := fusionExtendedEnv target producerRegion targetOuter
      targetLocal
    let sourceLocal := focusedBackwardSourceLocal input consumedWire producer
      consumer hdistinct producerRegion consumerRegion producerPorts
      consumerPorts producerTerm consumerTerm producerWire consumerWire
      consumedPort producerShape scope producerResolved endpoints
      (target.extend producerRegion) targetExact model targetRaw
    let sourceRaw := fusionExtendedEnv source producerRegion sourceOuter
      sourceLocal
    sourceRaw consumedIndex =
      model.eval producerTerm (sourceRaw ∘ producerIndex) := by
  dsimp only
  let targetRaw := fusionExtendedEnv target producerRegion targetOuter targetLocal
  let sourceLocal := focusedBackwardSourceLocal input consumedWire producer
    consumer hdistinct producerRegion consumerRegion producerPorts consumerPorts
    producerTerm consumerTerm producerWire consumerWire consumedPort producerShape
    scope producerResolved endpoints (target.extend producerRegion) targetExact
    model targetRaw
  let sourceRaw := fusionExtendedEnv source producerRegion sourceOuter sourceLocal
  have environments := focusedBackwardExtendedAgreement input consumedWire
    producer consumer hdistinct producerRegion consumerRegion producerPorts
    consumerPorts producerTerm consumerTerm producerWire consumerWire
    consumedPort producerShape scope producerResolved endpoints source target
    context sourceExact targetExact model sourceOuter targetOuter outerEq targetLocal
  have consumedMember : consumedWire ∈
      ConcreteElaboration.exactScopeWires input.val producerRegion :=
    (ConcreteElaboration.mem_exactScopeWires input.val producerRegion
      consumedWire).mpr scope.symm
  obtain ⟨consumedLocalIndex, consumedLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete consumedMember
  have consumedLocalGet :
      (ConcreteElaboration.exactScopeWires input.val producerRegion).get
        consumedLocalIndex = consumedWire :=
    ConcreteElaboration.WireContext.lookup?_sound consumedLookup
  let consumedFull : Fin (source.extend producerRegion).length := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source producerRegion).symm
    (Fin.natAdd source.length consumedLocalIndex)
  have consumedFullGet : (source.extend producerRegion).get consumedFull =
      consumedWire := by
    have localGet := ConcreteElaboration.WireContext.extend_local source
      producerRegion consumedLocalIndex
    simpa [consumedFull] using localGet.trans consumedLocalGet
  have consumedIndexEq : consumedIndex = consumedFull := by
    apply Fin.ext
    exact (List.getElem_inj sourceExact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        consumedGet.trans consumedFullGet.symm)
  rw [consumedIndexEq]
  have consumedFullCast : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source producerRegion)
      consumedFull = Fin.natAdd source.length consumedLocalIndex := by
    apply Fin.ext
    rfl
  change sourceRaw consumedFull =
    model.eval producerTerm (sourceRaw ∘ producerIndex)
  have consumedValue : sourceRaw consumedFull = model.eval producerTerm
      (fun port ↦ targetRaw (targetIndexOfSurvivor input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort
        (target.extend producerRegion) targetExact (producerWire port)
        (producerWire_ne_consumed input consumedWire producer consumer hdistinct
          producerPorts producerWire consumedPort.val producerResolved endpoints
          port)
        (producerWire_encloses_producer input producer producerRegion
          producerPorts producerTerm producerWire producerShape producerResolved
          port))) := by
    rw [show sourceRaw consumedFull = sourceLocal consumedLocalIndex by
      simp [sourceRaw, fusionExtendedEnv,
        ConcreteElaboration.extendedEnvironment, consumedFullCast, extendWireEnv]]
    dsimp [sourceLocal, focusedBackwardSourceLocal]
    split
    · rfl
    · rename_i notConsumed
      exact False.elim (notConsumed (by
        simpa only [List.get_eq_getElem] using consumedLocalGet))
  rw [consumedValue]
  apply congrArg (model.eval producerTerm)
  funext port
  let survives := producerWire_ne_consumed input consumedWire producer consumer
    hdistinct producerPorts producerWire consumedPort.val producerResolved
    endpoints port
  let visible := producerWire_encloses_producer input producer producerRegion
    producerPorts producerTerm producerWire producerShape producerResolved port
  let targetIndex := targetIndexOfSurvivor input consumedWire producer consumer
    hdistinct producerRegion consumerRegion producerTerm consumerTerm producerWire
    consumerWire consumedPort (target.extend producerRegion) targetExact
    (producerWire port) survives visible
  have sourceIndexEq :
      (context.extend producerRegion sourceExact targetExact).sourceIndex
        targetIndex = producerIndex port := by
    apply Context.sourceIndex_eq_of_get _ sourceExact.nodup
    rw [producerGet]
    exact (targetIndexOfSurvivor_origin_get input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort (target.extend producerRegion)
      targetExact (producerWire port) survives visible).symm
  have agreed := environments
    ((context.extend producerRegion sourceExact targetExact).sourceIndex
      targetIndex) targetIndex rfl
  simp only [Function.comp_apply]
  rw [← sourceIndexEq]
  exact agreed.symm

/-- Compiling the producer occurrence exposes exactly the equation carried by
the consumed output wire and the producer's resolved free wires. -/
theorem producerFocus_compiled
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (producerRegion : Fin input.val.regionCount)
    (producerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumedPort : Nat)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort },
          { node := producer, port := CPort.output }])
    (context : ConcreteElaboration.WireContext input.val)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val rels →
      Option (Region signature context.length rels))
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrenceWith? signature input.val
      recurse context binders (.node producer) = some item) :
    ∃ (consumedIndex : Fin context.length)
      (producerIndex : Fin producerPorts → Fin context.length),
      context.get consumedIndex = consumedWire ∧
      (∀ port, context.get (producerIndex port) = producerWire port) ∧
      item = .equation consumedIndex (producerTerm.mapFree producerIndex) := by
  simp only [ConcreteElaboration.compileOccurrenceWith?] at compiled
  unfold ConcreteElaboration.compileNode? at compiled
  rw [producerShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort? input.val context
      producer .output with
  | none => simp [outputResult] at compiled
  | some outputIndex =>
      cases freeResult : ConcreteElaboration.resolvePorts? input.val context
          producer producerPorts (fun port ↦ .free port) with
      | none => simp [outputResult, freeResult] at compiled
      | some freeIndex =>
          simp [outputResult, freeResult] at compiled
          subst item
          refine ⟨outputIndex, freeIndex, ?_, ?_, rfl⟩
          · obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
              ConcreteElaboration.resolvePort?_sound outputResult
            have ownerEq : owner = consumedWire :=
              ConcreteElaboration.endpoint_wire_unique
                input.property.wire_endpoints_are_disjoint ownerOccurs
                (fusionEndpoints_producer_occurs input consumedWire producer
                  consumer consumedPort endpoints)
            exact ownerGet.trans ownerEq
          · intro port
            have resolvedPort := sequenceFin_sound freeResult port
            obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
              ConcreteElaboration.resolvePort?_sound resolvedPort
            have ownerEq : owner = producerWire port :=
              ConcreteElaboration.endpoint_wire_unique
                input.property.wire_endpoints_are_disjoint ownerOccurs
                (resolvedFreePort_occurs input producer producerPorts
                  producerWire producerResolved port)
            exact ownerGet.trans ownerEq

/-- Fuel only bounds traversal.  Whenever two fuel choices both successfully
compile the same region presentation, they produce the same intrinsic region. -/
theorem compileRegion?_fuel_unique
    (d : ConcreteDiagram) (fuelSource : Nat) :
    ∀ {rels : RelCtx} (fuelTarget : Nat) (region : Fin d.regionCount)
      (context : ConcreteElaboration.WireContext d)
      (binders : ConcreteElaboration.BinderContext d rels)
      (sourceBody targetBody : Region signature context.length rels),
      ConcreteElaboration.compileRegion? signature d fuelSource region context
          binders = some sourceBody →
      ConcreteElaboration.compileRegion? signature d fuelTarget region context
          binders = some targetBody →
      sourceBody = targetBody := by
  intro rels
  induction fuelSource generalizing rels with
  | zero =>
      intro fuelTarget region context binders sourceBody targetBody sourceResult
      simp [ConcreteElaboration.compileRegion?] at sourceResult
  | succ sourceFuel ih =>
      intro fuelTarget region context binders sourceBody targetBody sourceResult
        targetResult
      cases fuelTarget with
      | zero => simp [ConcreteElaboration.compileRegion?] at targetResult
      | succ targetFuel =>
          cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
              signature d (ConcreteElaboration.compileRegion? signature d
                sourceFuel) (context.extend region) binders
              (ConcreteElaboration.localOccurrences d region) with
          | none =>
              simp [ConcreteElaboration.compileRegion?, sourceItemsResult]
                at sourceResult
          | some sourceItems =>
              simp [ConcreteElaboration.compileRegion?, sourceItemsResult]
                at sourceResult
              subst sourceBody
              cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith?
                  signature d (ConcreteElaboration.compileRegion? signature d
                    targetFuel) (context.extend region) binders
                  (ConcreteElaboration.localOccurrences d region) with
              | none =>
                  simp [ConcreteElaboration.compileRegion?, targetItemsResult]
                    at targetResult
              | some targetItems =>
                  simp [ConcreteElaboration.compileRegion?, targetItemsResult]
                    at targetResult
                  subst targetBody
                  have occurrencesUnique : ∀
                      (occurrences : List (ConcreteElaboration.LocalOccurrence
                        d.regionCount d.nodeCount))
                      (sourceItems targetItems : ItemSeq signature
                        (context.extend region).length rels),
                      ConcreteElaboration.compileOccurrencesWith? signature d
                          (ConcreteElaboration.compileRegion? signature d
                            sourceFuel) (context.extend region) binders
                          occurrences = some sourceItems →
                      ConcreteElaboration.compileOccurrencesWith? signature d
                          (ConcreteElaboration.compileRegion? signature d
                            targetFuel) (context.extend region) binders
                          occurrences = some targetItems →
                      sourceItems = targetItems := by
                    intro occurrences
                    induction occurrences with
                    | nil =>
                        intro sourceItems targetItems sourceCompiled targetCompiled
                        simp [ConcreteElaboration.compileOccurrencesWith?]
                          at sourceCompiled targetCompiled
                        subst sourceItems
                        subst targetItems
                        rfl
                    | cons occurrence tail tailIH =>
                        intro sourceItems targetItems sourceCompiled targetCompiled
                        simp only [ConcreteElaboration.compileOccurrencesWith?]
                          at sourceCompiled targetCompiled
                        cases occurrence with
                        | node node =>
                            cases focusResult : ConcreteElaboration.compileNode?
                                signature d (context.extend region) binders node with
                            | none =>
                                simp [ConcreteElaboration.compileOccurrenceWith?,
                                  focusResult] at sourceCompiled
                            | some focus =>
                                simp [ConcreteElaboration.compileOccurrenceWith?,
                                  focusResult] at sourceCompiled targetCompiled
                                cases sourceTailResult :
                                    ConcreteElaboration.compileOccurrencesWith?
                                      signature d
                                      (ConcreteElaboration.compileRegion?
                                        signature d sourceFuel)
                                      (context.extend region) binders tail with
                                | none => simp [sourceTailResult] at sourceCompiled
                                | some sourceTail =>
                                    simp [sourceTailResult] at sourceCompiled
                                    subst sourceItems
                                    cases targetTailResult :
                                        ConcreteElaboration.compileOccurrencesWith?
                                          signature d
                                          (ConcreteElaboration.compileRegion?
                                            signature d targetFuel)
                                          (context.extend region) binders tail with
                                    | none => simp [targetTailResult] at targetCompiled
                                    | some targetTail =>
                                        simp [targetTailResult] at targetCompiled
                                        subst targetItems
                                        rw [tailIH sourceTail targetTail
                                          sourceTailResult targetTailResult]
                        | child child =>
                            cases childShape : d.regions child with
                            | sheet =>
                                simp [ConcreteElaboration.compileOccurrenceWith?,
                                  childShape] at sourceCompiled
                            | cut parent =>
                                cases sourceChildResult :
                                    ConcreteElaboration.compileRegion? signature d
                                      sourceFuel child (context.extend region)
                                      binders with
                                | none =>
                                    simp [ConcreteElaboration.compileOccurrenceWith?,
                                      childShape, sourceChildResult]
                                      at sourceCompiled
                                | some sourceChild =>
                                    cases targetChildResult :
                                        ConcreteElaboration.compileRegion? signature
                                          d targetFuel child
                                          (context.extend region) binders with
                                    | none =>
                                        simp [ConcreteElaboration.compileOccurrenceWith?,
                                          childShape, targetChildResult]
                                          at targetCompiled
                                    | some targetChild =>
                                        have childEq := ih targetFuel child
                                          (context.extend region) binders sourceChild
                                          targetChild sourceChildResult
                                          targetChildResult
                                        subst targetChild
                                        simp [ConcreteElaboration.compileOccurrenceWith?,
                                          childShape, sourceChildResult,
                                          targetChildResult] at sourceCompiled targetCompiled
                                        cases sourceTailResult :
                                            ConcreteElaboration.compileOccurrencesWith?
                                              signature d
                                              (ConcreteElaboration.compileRegion?
                                                signature d sourceFuel)
                                              (context.extend region) binders tail with
                                        | none =>
                                            simp [sourceTailResult] at sourceCompiled
                                        | some sourceTail =>
                                            simp [sourceTailResult] at sourceCompiled
                                            subst sourceItems
                                            cases targetTailResult :
                                                ConcreteElaboration.compileOccurrencesWith?
                                                  signature d
                                                  (ConcreteElaboration.compileRegion?
                                                    signature d targetFuel)
                                                  (context.extend region) binders
                                                  tail with
                                            | none =>
                                                simp [targetTailResult]
                                                  at targetCompiled
                                            | some targetTail =>
                                                simp [targetTailResult]
                                                  at targetCompiled
                                                subst targetItems
                                                rw [tailIH sourceTail targetTail
                                                  sourceTailResult targetTailResult]
                            | bubble parent arity =>
                                cases sourceChildResult :
                                    ConcreteElaboration.compileRegion? signature d
                                      sourceFuel child (context.extend region)
                                      (binders.push child arity) with
                                | none =>
                                    simp [ConcreteElaboration.compileOccurrenceWith?,
                                      childShape, sourceChildResult]
                                      at sourceCompiled
                                | some sourceChild =>
                                    cases targetChildResult :
                                        ConcreteElaboration.compileRegion? signature
                                          d targetFuel child
                                          (context.extend region)
                                          (binders.push child arity) with
                                    | none =>
                                        simp [ConcreteElaboration.compileOccurrenceWith?,
                                          childShape, targetChildResult]
                                          at targetCompiled
                                    | some targetChild =>
                                        have childEq := ih targetFuel child
                                          (context.extend region)
                                          (binders.push child arity) sourceChild
                                          targetChild sourceChildResult
                                          targetChildResult
                                        subst targetChild
                                        simp [ConcreteElaboration.compileOccurrenceWith?,
                                          childShape, sourceChildResult,
                                          targetChildResult] at sourceCompiled targetCompiled
                                        cases sourceTailResult :
                                            ConcreteElaboration.compileOccurrencesWith?
                                              signature d
                                              (ConcreteElaboration.compileRegion?
                                                signature d sourceFuel)
                                              (context.extend region) binders tail with
                                        | none =>
                                            simp [sourceTailResult] at sourceCompiled
                                        | some sourceTail =>
                                            simp [sourceTailResult] at sourceCompiled
                                            subst sourceItems
                                            cases targetTailResult :
                                                ConcreteElaboration.compileOccurrencesWith?
                                                  signature d
                                                  (ConcreteElaboration.compileRegion?
                                                    signature d targetFuel)
                                                  (context.extend region) binders
                                                  tail with
                                            | none =>
                                                simp [targetTailResult]
                                                  at targetCompiled
                                            | some targetTail =>
                                                simp [targetTailResult]
                                                  at targetCompiled
                                                subst targetItems
                                                rw [tailIH sourceTail targetTail
                                                  sourceTailResult targetTailResult]
                  have itemsEq := occurrencesUnique
                    (ConcreteElaboration.localOccurrences d region) sourceItems
                    targetItems sourceItemsResult targetItemsResult
                  subst targetItems
                  rfl

/-- The generic compiler simulation is used everywhere except strictly below
the producer scope.  The focused producer kernel owns that entire descendant
subtree, including the routed consumer rewrite. -/
def RegionAllowed (input : CheckedDiagram signature)
    (producerRegion region : Fin input.val.regionCount) : Prop :=
  ¬ (input.val.Encloses producerRegion region ∧ region ≠ producerRegion)

theorem regionAllowed_child
    (input : CheckedDiagram signature)
    (producerRegion parent child : Fin input.val.regionCount)
    (parentRegular : parent ≠ producerRegion)
    (parentAllowed : RegionAllowed input producerRegion parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    RegionAllowed input producerRegion child := by
  intro childStrict
  obtain ⟨producerEnclosesChild, childNeProducer⟩ := childStrict
  rcases ConcreteElaboration.encloses_direct_child childParent
      producerEnclosesChild with producerEq | producerEnclosesParent
  · exact childNeProducer producerEq.symm
  · exact parentAllowed ⟨producerEnclosesParent, parentRegular⟩

/-- Away from the producer scope, stable wire compaction gives the local
witness transport required by the authoritative recursive compiler. -/
theorem regularLocalSelection
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
    (direction : ConcreteElaboration.SimulationDirection)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (region : Fin input.val.regionCount)
    (regular : region ≠ producerRegion)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin source.length → model.Carrier)
      (targetOuter : Fin target.length → model.Carrier),
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (context.extend region sourceExact targetExact).indexRelation
                  (ConcreteElaboration.extendedEnvironment source region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment target region
                    targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (context.extend region sourceExact targetExact).indexRelation
                  (ConcreteElaboration.extendedEnvironment source region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment target region
                    targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter ∘ context.sourceIndex = targetOuter := by
    simpa [Context.indexRelation] using outerAgrees
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := fusionTargetLocalEnv context region sourceExact
        targetExact sourceOuter sourceLocal
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
          (context.extend region sourceExact targetExact).sourceIndex _ _).mpr
      simpa [Context.indexRelation, fusionExtendedEnv, targetLocal, outerEq] using
        (fusionExtendedEnv_forward context region sourceExact targetExact
          sourceOuter sourceLocal)
  | backward =>
      intro targetLocal
      let sourceLocal := fusionSourceLocalEnvOfNe input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerTerm
        consumerTerm producerWire consumerWire consumedPort scope region regular
        targetLocal
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
          (context.extend region sourceExact targetExact).sourceIndex _ _).mpr
      simpa [Context.indexRelation, fusionExtendedEnv, sourceLocal] using
        (fusionExtendedEnv_backward_of_ne context producerRegion scope region
          regular sourceExact targetExact sourceOuter targetOuter outerEq
          targetLocal)

/-- Package the selected producer-to-consumer route as the child item owned by
the focused producer frame. -/
theorem childOccurrence_routeSimulation
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
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (child : Fin input.val.regionCount)
    (childParent : (input.val.regions child).parent? = some producerRegion)
    (path : List Nat)
    (route : Diagram.Splice.RegionRoute input.val child consumerRegion path)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceExact : (source.extend child).Exact child)
    (targetExact : (target.extend child).Exact child)
    (consumedIndex : Fin source.length)
    (consumedGet : source.get consumedIndex = consumedWire)
    (producerIndex : Fin producerPorts → Fin source.length)
    (producerGet : ∀ port, source.get (producerIndex port) = producerWire port)
    (sourceItem : Item signature source.length rels)
    (targetItem : Item signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      source binders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuelTarget)
      target binders (.child child) = some targetItem) :
    ∀ (sourceEnv : Fin source.length → model.Carrier)
      (targetEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      context.indexRelation.EnvironmentsAgree sourceEnv targetEnv →
      sourceEnv consumedIndex =
        model.eval producerTerm (sourceEnv ∘ producerIndex) →
      direction.Entails
        (denoteItem model named sourceEnv relEnv sourceItem)
        (denoteItem model named targetEnv relEnv targetItem) := by
  have producerEnclosesChild : input.val.Encloses producerRegion child :=
    directChild_encloses childParent
  have childNeProducer : child ≠ producerRegion := by
    intro equality
    subst child
    exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
      input.property childParent)
      (ConcreteDiagram.Encloses.refl input.val producerRegion)
  cases kind : input.val.regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, kind] at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = producerRegion := by
        rw [kind] at childParent
        exact Option.some.inj childParent
      subst actualParent
      simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
        fusionRaw_regions] at sourceCompiled targetCompiled
      cases sourceResult : ConcreteElaboration.compileRegion? signature input.val
          fuelSource child source binders with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuelTarget child target binders with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have sourceFuelNe : fuelSource ≠ 0 := by
            intro equality
            subst fuelSource
            simp [ConcreteElaboration.compileRegion?] at sourceResult
          have targetFuelNe : fuelTarget ≠ 0 := by
            intro equality
            subst fuelTarget
            simp [ConcreteElaboration.compileRegion?] at targetResult
          obtain ⟨sourceChildFuel, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero sourceFuelNe
          obtain ⟨targetChildFuel, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero targetFuelNe
          intro sourceEnv targetEnv relEnv environments equation
          have bodies := compileRegion_route_entails input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerPorts
            consumerPorts producerTerm consumerTerm producerWire consumerWire
            consumedPort producerShape consumerShape scope producerResolved
            consumerResolved endpoints targetWellFormed model named route
            producerEnclosesChild childNeProducer direction.flip sourceChildFuel
            targetChildFuel source
            target context binders sourceExact targetExact consumedIndex
            consumedGet producerIndex producerGet sourceBody targetBody
            sourceResult targetResult sourceEnv targetEnv relEnv environments
            equation
          simp only [cut_denotes_negation]
          cases direction with
          | forward =>
              exact fun sourceNot targetDenotes ↦
                sourceNot (bodies targetDenotes)
          | backward =>
              exact fun targetNot sourceDenotes ↦
                targetNot (bodies sourceDenotes)
  | bubble actualParent arity =>
      have actualParentEq : actualParent = producerRegion := by
        rw [kind] at childParent
        exact Option.some.inj childParent
      subst actualParent
      simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
        fusionRaw_regions] at sourceCompiled targetCompiled
      cases sourceResult : ConcreteElaboration.compileRegion? signature input.val
          fuelSource child source (binders.push child arity) with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        change (ConcreteElaboration.compileRegion? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) fuelTarget child target (binders.push child arity)).bind
              (fun body ↦ some (Item.bubble arity body)) =
                some targetItem at targetCompiled
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuelTarget child target (binders.push child arity) with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have sourceFuelNe : fuelSource ≠ 0 := by
            intro equality
            subst fuelSource
            simp [ConcreteElaboration.compileRegion?] at sourceResult
          have targetFuelNe : fuelTarget ≠ 0 := by
            intro equality
            subst fuelTarget
            simp [ConcreteElaboration.compileRegion?] at targetResult
          obtain ⟨sourceChildFuel, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero sourceFuelNe
          obtain ⟨targetChildFuel, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero targetFuelNe
          intro sourceEnv targetEnv relEnv environments equation
          simp only [bubble_denotes_exists]
          cases direction with
          | forward =>
              rintro ⟨relationValue, sourceDenotes⟩
              exact ⟨relationValue,
                compileRegion_route_entails input consumedWire producer consumer
                  hdistinct producerRegion consumerRegion producerPorts
                  consumerPorts producerTerm consumerTerm producerWire
                  consumerWire consumedPort producerShape consumerShape scope
                  producerResolved consumerResolved endpoints targetWellFormed
                  model named route producerEnclosesChild childNeProducer .forward
                  sourceChildFuel targetChildFuel source target context
                  (binders.push child arity)
                  sourceExact targetExact consumedIndex consumedGet producerIndex
                  producerGet sourceBody targetBody sourceResult targetResult
                  sourceEnv targetEnv (relationValue, relEnv) environments equation
                  sourceDenotes⟩
          | backward =>
              rintro ⟨relationValue, targetDenotes⟩
              exact ⟨relationValue,
                compileRegion_route_entails input consumedWire producer consumer
                  hdistinct producerRegion consumerRegion producerPorts
                  consumerPorts producerTerm consumerTerm producerWire
                  consumerWire consumedPort producerShape consumerShape scope
                  producerResolved consumerResolved endpoints targetWellFormed
                  model named route producerEnclosesChild childNeProducer .backward
                  sourceChildFuel targetChildFuel source target context
                  (binders.push child arity)
                  sourceExact targetExact consumedIndex consumedGet producerIndex
                  producerGet sourceBody targetBody sourceResult targetResult
                  sourceEnv targetEnv (relationValue, relEnv) environments equation
                  targetDenotes⟩

/-- Semantic transport for any producer-site frame that excludes the producer
occurrence itself.  A same-site consumer is rewritten pointwise; a descendant
consumer is reached through its unique direct-child route. -/
theorem producerFrame_entails
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
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (sourceExact : source.Exact producerRegion)
    (targetExact : target.Exact producerRegion)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (frame : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (localMembership : ∀ occurrence, occurrence ∈ frame →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val
        producerRegion)
    (noProducer : ConcreteElaboration.LocalOccurrence.node producer ∉ frame)
    (consumedIndex : Fin source.length)
    (consumedGet : source.get consumedIndex = consumedWire)
    (producerIndex : Fin producerPorts → Fin source.length)
    (producerGet : ∀ port, source.get (producerIndex port) = producerWire port)
    (sourceItems : ItemSeq signature source.length rels)
    (targetItems : ItemSeq signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      source binders frame = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuelTarget)
      target binders (frame.map (mapOccurrence input producer)) =
        some targetItems)
    (sourceEnv : Fin source.length → model.Carrier)
    (targetEnv : Fin target.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (environments : context.indexRelation.EnvironmentsAgree sourceEnv targetEnv)
    (producerEquation : sourceEnv consumedIndex =
      model.eval producerTerm (sourceEnv ∘ producerIndex)) :
    direction.Entails
      (denoteItemSeq model named sourceEnv relEnv sourceItems)
      (denoteItemSeq model named targetEnv relEnv targetItems) := by
  induction frame generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileOccurrencesWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      cases direction <;> intro _ <;> trivial
  | cons occurrence tail ih =>
      have occurrenceLocal := localMembership occurrence (by simp)
      have tailLocal : ∀ current, current ∈ tail →
          current ∈ ConcreteElaboration.localOccurrences input.val
            producerRegion := by
        intro current member
        exact localMembership current (by simp [member])
      have occurrenceNeProducer : occurrence ≠ .node producer := by
        intro equality
        subst occurrence
        exact noProducer (by simp)
      have tailNoProducer : ConcreteElaboration.LocalOccurrence.node producer ∉
          tail := by
        intro member
        exact noProducer (by simp [member])
      simp only [ConcreteElaboration.compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceFocusResult : ConcreteElaboration.compileOccurrenceWith?
          signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          source binders occurrence with
      | none => simp [sourceFocusResult] at sourceCompiled
      | some sourceFocus =>
        simp [sourceFocusResult] at sourceCompiled
        cases sourceTailResult : ConcreteElaboration.compileOccurrencesWith?
            signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuelSource)
            source binders tail with
        | none => simp [sourceTailResult] at sourceCompiled
        | some sourceTail =>
          simp [sourceTailResult] at sourceCompiled
          subst sourceItems
          cases targetFocusResult : ConcreteElaboration.compileOccurrenceWith?
              signature
              (fusionRaw input consumedWire producer consumer hdistinct
                consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort)
              (ConcreteElaboration.compileRegion? signature
                (fusionRaw input consumedWire producer consumer hdistinct
                  consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort) fuelTarget)
              target binders (mapOccurrence input producer occurrence) with
          | none => simp [targetFocusResult] at targetCompiled
          | some targetFocus =>
            simp [targetFocusResult] at targetCompiled
            cases targetTailResult : ConcreteElaboration.compileOccurrencesWith?
                signature
                (fusionRaw input consumedWire producer consumer hdistinct
                  consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort)
                (ConcreteElaboration.compileRegion? signature
                  (fusionRaw input consumedWire producer consumer hdistinct
                    consumerRegion producerTerm consumerTerm producerWire
                    consumerWire consumedPort) fuelTarget)
                target binders (tail.map (mapOccurrence input producer)) with
            | none => simp [targetTailResult] at targetCompiled
            | some targetTail =>
              simp [targetTailResult] at targetCompiled
              subst targetItems
              have tailEntails := ih tailLocal tailNoProducer sourceTail
                targetTail sourceTailResult targetTailResult
              have focusEntails : direction.Entails
                  (denoteItem model named sourceEnv relEnv sourceFocus)
                  (denoteItem model named targetEnv relEnv targetFocus) := by
                cases occurrence with
                | node node =>
                    have nodeRegion :=
                      (ConcreteElaboration.mem_localOccurrences_node input.val
                        producerRegion node).mp occurrenceLocal
                    have nodeNeProducer : node ≠ producer := by
                      intro equality
                      subst node
                      exact occurrenceNeProducer rfl
                    by_cases nodeIsConsumer : node = consumer
                    · subst node
                      have consumerRegionEq : consumerRegion = producerRegion := by
                        rw [consumerShape] at nodeRegion
                        exact nodeRegion
                      subst consumerRegion
                      have consumedVisible := consumedWire_encloses_consumer input
                        consumedWire producer consumer consumedPort.val
                        producerRegion consumerPorts consumerTerm consumerShape
                        endpoints
                      have consumedIndexEq := index_eq_visibleIndex_of_get input.val
                        source producerRegion sourceExact consumedWire
                        consumedVisible consumedIndex consumedGet
                      have visibleEquation : sourceEnv
                          (visibleIndex input.val source producerRegion sourceExact
                            consumedWire consumedVisible) =
                          model.eval producerTerm (fun port ↦ sourceEnv
                            (visibleIndex input.val source producerRegion
                              sourceExact (producerWire port)
                              (producerWire_encloses_consumer input consumedWire
                                producer consumer consumedPort.val producerRegion
                                producerRegion producerPorts consumerPorts
                                producerTerm consumerTerm producerWire
                                producerShape consumerShape scope producerResolved
                                endpoints port))) := by
                        rw [← consumedIndexEq, producerEquation]
                        apply congrArg (model.eval producerTerm)
                        funext port
                        have producerIndexEq := index_eq_visibleIndex_of_get
                          input.val source producerRegion sourceExact
                          (producerWire port)
                          (producerWire_encloses_consumer input consumedWire
                            producer consumer consumedPort.val producerRegion
                            producerRegion producerPorts consumerPorts producerTerm
                            consumerTerm producerWire producerShape consumerShape
                            scope producerResolved endpoints port)
                          (producerIndex port) (producerGet port)
                        simp only [Function.comp_apply]
                        rw [producerIndexEq]
                      have equivalence := consumerItem_denote_iff input
                        consumedWire producer consumer hdistinct producerRegion
                        producerRegion producerPorts consumerPorts producerTerm
                        consumerTerm producerWire consumerWire consumedPort
                        producerShape consumerShape scope producerResolved
                        consumerResolved endpoints targetWellFormed source target
                        sourceExact targetExact context binders binders sourceFocus
                        targetFocus (by
                          simpa only [ConcreteElaboration.compileOccurrenceWith?]
                            using sourceFocusResult) (by
                          simpa [ConcreteElaboration.compileOccurrenceWith?,
                            mapOccurrence, hdistinct.symm] using targetFocusResult)
                        model named sourceEnv targetEnv relEnv environments
                        visibleEquation
                      cases direction with
                      | forward => exact equivalence.mp
                      | backward => exact equivalence.mpr
                    · have simulation := unchangedNode_itemSimulation input
                        consumedWire producer consumer node hdistinct
                        nodeNeProducer nodeIsConsumer consumerRegion producerTerm
                        consumerTerm producerWire consumerWire consumedPort source
                        target context sourceExact.nodup binders sourceFocus
                        targetFocus (by
                          simpa only [ConcreteElaboration.compileOccurrenceWith?]
                            using sourceFocusResult) (by
                          simpa [ConcreteElaboration.compileOccurrenceWith?,
                            mapOccurrence_node input producer node nodeNeProducer]
                            using targetFocusResult) model named direction
                      exact simulation sourceEnv targetEnv relEnv environments
                | child child =>
                    have childParent :=
                      (ConcreteElaboration.mem_localOccurrences_child input.val
                        producerRegion child).mp occurrenceLocal
                    have sourceChildExact := sourceExact.extend_child
                      input.property childParent
                    have targetParent :
                        ((fusionRaw input consumedWire producer consumer hdistinct
                          consumerRegion producerTerm consumerTerm producerWire
                          consumerWire consumedPort).regions child).parent? =
                            some producerRegion := by
                      simpa only [fusionRaw_regions] using childParent
                    have targetChildExact := targetExact.extend_child
                      targetWellFormed targetParent
                    by_cases childEnclosesConsumer :
                        input.val.Encloses child consumerRegion
                    · obtain ⟨path, ⟨route⟩⟩ :=
                        Diagram.Splice.regionRoute_complete_of_encloses input.val
                          child consumerRegion childEnclosesConsumer
                      exact childOccurrence_routeSimulation input consumedWire
                        producer consumer hdistinct producerRegion consumerRegion
                        producerPorts consumerPorts producerTerm consumerTerm
                        producerWire consumerWire consumedPort producerShape
                        consumerShape scope producerResolved consumerResolved
                        endpoints targetWellFormed model named direction fuelSource
                        fuelTarget child
                        childParent path route source target context binders
                        sourceChildExact targetChildExact consumedIndex consumedGet
                        producerIndex producerGet sourceFocus targetFocus
                        sourceFocusResult (by
                          simpa only [mapOccurrence_child] using targetFocusResult)
                        sourceEnv targetEnv relEnv environments producerEquation
                    · have producerAway : ¬ input.val.Encloses child
                          producerRegion :=
                        ConcreteElaboration.checked_direct_child_not_encloses_parent
                          input.property childParent
                      have simulation := childOccurrence_awaySimulation input
                        consumedWire producer consumer hdistinct producerRegion
                        consumerRegion producerPorts consumerPorts producerTerm
                        consumerTerm producerWire consumerWire consumedPort
                        producerShape consumerShape scope targetWellFormed model
                        named direction fuelSource fuelTarget producerRegion child
                        source target
                        context binders childParent producerAway
                        childEnclosesConsumer sourceChildExact targetChildExact
                        sourceFocus targetFocus sourceFocusResult (by
                          simpa only [mapOccurrence_child] using targetFocusResult)
                      exact simulation sourceEnv targetEnv relEnv environments
              simpa only [denoteItemSeq] using
                direction.entails_and focusEntails tailEntails

/-- The focused producer region discharges the deleted producer equation by
choosing the consumed wire existential in the backward direction, and carries
that equation to the rewritten consumer in both directions. -/
theorem focusedProducerLocalTransport
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
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceExact : (source.extend producerRegion).Exact producerRegion)
    (targetExact : (target.extend producerRegion).Exact producerRegion)
    (sourceItems : ItemSeq signature
      (source.extend producerRegion).length rels)
    (targetItems : ItemSeq signature
      (target.extend producerRegion).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) (source.extend producerRegion) binders
      (ConcreteElaboration.localOccurrences input.val producerRegion) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      (target.extend producerRegion) binders
      (ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        producerRegion) = some targetItems) :
    ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport direction source
      target producerRegion producerRegion context.indexRelation model named
      relEnv sourceItems targetItems := by
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
        fuelSource) (source.extend producerRegion) binders
      (before ++ .node producer :: after) = some sourceItems := by
    rw [← localEq]
    exact sourceCompiled
  obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
      sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (source.extend producerRegion) binders before after (.node producer)
      sourceItems sourceFramed
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
      (target.extend producerRegion) binders
      (before.map (mapOccurrence input producer) ++
        after.map (mapOccurrence input producer)) = some targetItems := by
    rw [← targetLocalEq]
    exact targetCompiled
  obtain ⟨targetBefore, targetAfter, targetBeforeCompiled,
      targetAfterCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        fuelTarget)
      (target.extend producerRegion) binders
      (before.map (mapOccurrence input producer))
      (after.map (mapOccurrence input producer)) targetItems targetFramed
  obtain ⟨consumedIndex, producerIndex, consumedGet, producerGet,
      sourceFocusEq⟩ := producerFocus_compiled input consumedWire producer
    consumer producerRegion producerPorts producerTerm producerWire
    consumedPort.val producerShape producerResolved endpoints
    (source.extend producerRegion) binders
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
  intro relEnv sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter ∘ context.sourceIndex = targetOuter := by
    simpa [Context.indexRelation] using outerAgrees
  let extendedContext := context.extend producerRegion sourceExact targetExact
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      let targetLocal := fusionTargetLocalEnv context producerRegion sourceExact
        targetExact sourceOuter sourceLocal
      let sourceRaw := fusionExtendedEnv source producerRegion sourceOuter
        sourceLocal
      let targetRaw := fusionExtendedEnv target producerRegion targetOuter
        targetLocal
      have extendedAgrees : extendedContext.indexRelation.EnvironmentsAgree
          sourceRaw targetRaw := by
        simpa [extendedContext, Context.indexRelation, sourceRaw, targetRaw,
          targetLocal, outerEq] using
          (fusionExtendedEnv_forward context producerRegion sourceExact
            targetExact sourceOuter sourceLocal)
      rw [denoteItemSeq_frame] at sourceDenotes
      rcases sourceDenotes with
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
        model named .forward fuelSource fuelTarget
        (source.extend producerRegion) (target.extend producerRegion)
        extendedContext sourceExact targetExact binders before beforeLocal
        producerNotBefore consumedIndex consumedGet producerIndex producerGet
        sourceBefore targetBefore sourceBeforeCompiled targetBeforeCompiled
        sourceRaw targetRaw relEnv extendedAgrees producerEquationRaw
        sourceBeforeDenotes
      have afterDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .forward fuelSource fuelTarget
        (source.extend producerRegion) (target.extend producerRegion)
        extendedContext sourceExact targetExact binders after afterLocal
        producerNotAfter consumedIndex consumedGet producerIndex producerGet
        sourceAfter targetAfter sourceAfterCompiled targetAfterCompiled
        sourceRaw targetRaw relEnv extendedAgrees producerEquationRaw
        sourceAfterDenotes
      refine ⟨targetLocal, ?_⟩
      simpa [denoteItemSeq_append, sourceRaw, targetRaw] using
        And.intro beforeDenotes afterDenotes
  | backward =>
      intro targetLocal targetDenotes
      let targetRaw := fusionExtendedEnv target producerRegion targetOuter
        targetLocal
      let sourceLocal := focusedBackwardSourceLocal input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape scope producerResolved endpoints
        (target.extend producerRegion) targetExact model targetRaw
      let sourceRaw := fusionExtendedEnv source producerRegion sourceOuter
        sourceLocal
      have extendedAgrees : extendedContext.indexRelation.EnvironmentsAgree
          sourceRaw targetRaw := by
        simpa [extendedContext, sourceRaw, targetRaw, sourceLocal] using
          (focusedBackwardExtendedAgreement input consumedWire producer consumer
            hdistinct producerRegion consumerRegion producerPorts consumerPorts
            producerTerm consumerTerm producerWire consumerWire consumedPort
            producerShape scope producerResolved endpoints source target context
            sourceExact targetExact model sourceOuter targetOuter outerEq
            targetLocal)
      have producerEquation : sourceRaw consumedIndex =
          model.eval producerTerm (sourceRaw ∘ producerIndex) := by
        simpa [sourceRaw, targetRaw, sourceLocal] using
          (focusedBackwardProducerEquation input consumedWire producer consumer
            hdistinct producerRegion consumerRegion producerPorts consumerPorts
            producerTerm consumerTerm producerWire consumerWire consumedPort
            producerShape scope producerResolved endpoints source target context
            sourceExact targetExact model sourceOuter targetOuter outerEq
            targetLocal consumedIndex consumedGet producerIndex producerGet)
      rw [denoteItemSeq_append] at targetDenotes
      rcases targetDenotes with ⟨targetBeforeDenotes, targetAfterDenotes⟩
      have beforeDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .backward fuelSource fuelTarget
        (source.extend producerRegion) (target.extend producerRegion)
        extendedContext sourceExact targetExact binders before beforeLocal
        producerNotBefore consumedIndex consumedGet producerIndex producerGet
        sourceBefore targetBefore sourceBeforeCompiled targetBeforeCompiled
        sourceRaw targetRaw relEnv extendedAgrees producerEquation
        targetBeforeDenotes
      have afterDenotes := producerFrame_entails input consumedWire producer
        consumer hdistinct producerRegion consumerRegion producerPorts
        consumerPorts producerTerm consumerTerm producerWire consumerWire
        consumedPort producerShape consumerShape scope producerResolved
        consumerResolved endpoints producerEnclosesConsumer targetWellFormed
        model named .backward fuelSource fuelTarget
        (source.extend producerRegion) (target.extend producerRegion)
        extendedContext sourceExact targetExact binders after afterLocal
        producerNotAfter consumedIndex consumedGet producerIndex producerGet
        sourceAfter targetAfter sourceAfterCompiled targetAfterCompiled
        sourceRaw targetRaw relEnv extendedAgrees producerEquation
        targetAfterDenotes
      refine ⟨sourceLocal, ?_⟩
      rw [denoteItemSeq_frame]
      have producerDenotes : denoteItem model named sourceRaw relEnv
          (.equation consumedIndex (producerTerm.mapFree producerIndex)) := by
        simpa [denoteItem_equation, model.eval_mapFree] using producerEquation
      exact ⟨beforeDenotes, producerDenotes, afterDenotes⟩

end FusionSoundness

end VisualProof.Rule
