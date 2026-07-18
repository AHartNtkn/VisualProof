import VisualProof.Rule.Soundness.Equational.FusionRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FusionSoundness

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

end FusionSoundness

end VisualProof.Rule
