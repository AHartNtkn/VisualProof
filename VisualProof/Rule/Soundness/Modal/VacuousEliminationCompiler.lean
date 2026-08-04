import VisualProof.Rule.Soundness.Modal.VacuousElimination

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem compileOccurrence_itemSimulation
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceParent : Fin trace.sourceDiagram.regionCount)
    (targetParent : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (contextWitness : PromotedContextWitness trace sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetExact : targetContext.Exact targetParent)
    (sourceBindersCover : sourceBinders.Covers sourceParent)
    (targetBindersCover : targetBinders.Covers targetParent)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders sourceParent)
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input targetBinders
        targetParent)
    (occurrence : ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount)
    (regionMap : Fin (vacuousRegionDomain input bubble).count →
      Fin input.regionCount)
    (nodeShape : ∀ node, occurrence = .node node →
      input.nodes node =
        match trace.sourceDiagram.nodes node with
        | .term owner freePorts term => .term (regionMap owner) freePorts term
        | .atom owner binder => .atom (regionMap owner) (trace.origin binder)
        | .named owner definition arity =>
            .named (regionMap owner) definition arity)
    (regionShape : ∀ child, occurrence = .child child →
      (trace.sourceDiagram.regions child).parent? = some sourceParent →
      input.regions (trace.origin child) =
        match trace.sourceDiagram.regions child with
        | .sheet => .sheet
        | .cut _ => .cut targetParent
        | .bubble _ arity => .bubble targetParent arity)
    (recurseAt : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin trace.sourceDiagram.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        trace.sourceDiagram childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        input childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
      (childTargetContext : ConcreteElaboration.WireContext input)
      (childContext : PromotedContextWitness trace childSourceContext
        childTargetContext),
      True → True →
      (childBinderWitness : MappedBinderWitness trace childSourceBinders
        childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (trace.origin child) →
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration input childTargetBinders
        (trace.origin child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend (trace.origin child)).Exact
        (trace.origin child) →
      ∀ (sourceBody : Region signature childSourceContext.length
          childSourceRels)
        (targetBody : Region signature childTargetContext.length
          childTargetRels),
      ConcreteElaboration.compileRegion? signature trace.sourceDiagram
          fuelSource child childSourceContext childSourceBinders =
        some sourceBody →
      ConcreteElaboration.compileRegion? signature input childFuelTarget
          (trace.origin child) childTargetContext childTargetBinders =
        some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences trace.sourceDiagram sourceParent)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature trace.sourceDiagram
        (ConcreteElaboration.compileRegion? signature trace.sourceDiagram
          fuelSource)
        sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuelTarget)
        targetContext targetBinders (trace.occurrenceMap occurrence) =
          some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      contextWitness.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      exact trace.compileNode_itemSimulation targetWellFormed model named
        direction sourceContext targetContext sourceBinders targetBinders
        binderWitness node regionMap (nodeShape node rfl) sourceItem targetItem
        sourceCompiled targetCompiled
  | child child =>
      have sourceParentEq :=
        (ConcreteElaboration.mem_localOccurrences_child trace.sourceDiagram
          sourceParent child).mp member
      have targetKind := regionShape child rfl sourceParentEq
      change
        ConcreteElaboration.compileOccurrenceWith? signature input
            (ConcreteElaboration.compileRegion? signature input fuelTarget)
            targetContext targetBinders (.child (trace.origin child)) =
          some targetItem at targetCompiled
      cases sourceKind : trace.sourceDiagram.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature trace.sourceDiagram
                fuelSource child sourceContext sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature input fuelTarget
                    (trace.origin child) targetContext targetBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKind, targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKind, targetResult] at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      (input.regions (trace.origin child)).parent? =
                        some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  have bodies := recurseAt
                    (childDirection := direction.flip)
                    fuelTarget sourceContext targetContext contextWitness
                    True.intro True.intro binderWitness
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.cutChild sourceWellFormed sourceKind)
                    (targetEnumeration.cutChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
                    sourceBody targetBody sourceResult targetResult
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment :=
                    bodies sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble actualParent arity =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          let sourcePushed := sourceBinders.push child arity
          let targetPushed := targetBinders.push (trace.origin child) arity
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature trace.sourceDiagram
                fuelSource child sourceContext sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature input fuelTarget
                    (trace.origin child) targetContext targetPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKind, targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKind, targetPushed, targetResult] at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      (input.regions (trace.origin child)).parent? =
                        some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  let pushedWitness :=
                    MappedBinderWitness.push binderWitness child arity
                  have bodies := recurseAt
                    (childDirection := direction)
                    fuelTarget sourceContext targetContext contextWitness
                    True.intro True.intro pushedWitness
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.bubbleChild sourceWellFormed sourceKind)
                    (targetEnumeration.bubbleChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
                    sourceBody targetBody sourceResult targetResult
                  have pushedMap :
                      (pushedWitness.relationMap :
                        RelationRenaming (arity :: sourceRels)
                          (arity :: targetRels)) =
                        (RelationRenaming.lift binderWitness.relationMap arity :
                          RelationRenaming (arity :: sourceRels)
                            (arity :: targetRels)) := by
                    simpa only [pushedWitness] using
                      MappedBinderWitness.relationMap_push binderWitness child
                        arity
                  rw [pushedMap] at bodies
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments targetDenotes⟩

end VisualProof.Rule.VacuousElimTrace
