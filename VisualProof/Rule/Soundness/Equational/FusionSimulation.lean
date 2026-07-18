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
    (fuel : Nat)
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
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      source binders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
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
          fuel child source binders with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuel child target binders with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have fuelNe : fuel ≠ 0 := by
            intro equality
            subst fuel
            simp [ConcreteElaboration.compileRegion?] at sourceResult
          obtain ⟨childFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero fuelNe
          intro sourceEnv targetEnv relEnv environments equation
          have bodies := compileRegion_route_entails input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerPorts
            consumerPorts producerTerm consumerTerm producerWire consumerWire
            consumedPort producerShape consumerShape scope producerResolved
            consumerResolved endpoints targetWellFormed model named route
            producerEnclosesChild childNeProducer direction.flip childFuel source
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
          fuel child source (binders.push child arity) with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        change (ConcreteElaboration.compileRegion? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) fuel child target (binders.push child arity)).bind
              (fun body ↦ some (Item.bubble arity body)) =
                some targetItem at targetCompiled
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuel child target (binders.push child arity) with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have fuelNe : fuel ≠ 0 := by
            intro equality
            subst fuel
            simp [ConcreteElaboration.compileRegion?] at sourceResult
          obtain ⟨childFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero fuelNe
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
                  childFuel source target context (binders.push child arity)
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
                  childFuel source target context (binders.push child arity)
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
    (fuel : Nat)
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
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      source binders frame = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
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
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          source binders occurrence with
      | none => simp [sourceFocusResult] at sourceCompiled
      | some sourceFocus =>
        simp [sourceFocusResult] at sourceCompiled
        cases sourceTailResult : ConcreteElaboration.compileOccurrencesWith?
            signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
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
                  consumerWire consumedPort) fuel)
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
                    consumerWire consumedPort) fuel)
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
                        endpoints targetWellFormed model named direction fuel child
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
                        named direction fuel producerRegion child source target
                        context binders childParent producerAway
                        childEnclosesConsumer sourceChildExact targetChildExact
                        sourceFocus targetFocus sourceFocusResult (by
                          simpa only [mapOccurrence_child] using targetFocusResult)
                      exact simulation sourceEnv targetEnv relEnv environments
              simpa only [denoteItemSeq] using
                direction.entails_and focusEntails tailEntails

end FusionSoundness

end VisualProof.Rule
