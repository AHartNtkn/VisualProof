import VisualProof.Rule.Soundness.Modal.VacuousElimination

namespace VisualProof.Concrete.VacuousElimTrace

open VisualProof.Concrete
open VisualProof.Rule

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem compileOccurrence_itemSimulation
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed )
    (targetWellFormed : input.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceParent : Fin trace.sourceDiagram.regionCount)
    (targetParent : Fin input.regionCount)
    (sourceContext : Concrete.Elaboration.WireContext trace.sourceDiagram)
    (targetContext : Concrete.Elaboration.WireContext input)
    (contextWitness : PromotedContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext input targetRels)
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetExact : targetContext.Exact targetParent)
    (sourceBindersCover : sourceBinders.Covers sourceParent)
    (targetBindersCover : targetBinders.Covers targetParent)
    (sourceEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders sourceParent)
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input targetBinders
        targetParent)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount)
    (regionMap : Fin (vacuousRegionDomain input bubble).count →
      Fin input.regionCount)
    (nodeShape : ∀ node, occurrence = .node node →
      input.nodes node =
        match trace.sourceDiagram.nodes node with
        | .identity owner arity => .identity (regionMap owner) arity
        | .atom owner binder => .atom (regionMap owner) (trace.origin binder))
    (regionShape : ∀ child, occurrence = .child child →
      (trace.sourceDiagram.regions child).parent? = some sourceParent →
      input.regions (trace.origin child) =
        match trace.sourceDiagram.regions child with
        | .sheet => .sheet
        | .cut _ => .cut targetParent
        | .bubble _ arity => .bubble targetParent arity)
    (recurseAt : ∀
      {childDirection : Concrete.Elaboration.SimulationDirection}
      {child : Fin trace.sourceDiagram.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext
        trace.sourceDiagram childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        input childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : Concrete.Elaboration.WireContext trace.sourceDiagram)
      (childTargetContext : Concrete.Elaboration.WireContext input)
      (childContext : PromotedContextWitness trace childSourceContext
        childTargetContext),
      True → True →
      (childBinderWitness : MappedBinderWitness trace childSourceBinders
        childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (trace.origin child) →
      Concrete.Elaboration.BinderContext.Enumeration trace.sourceDiagram
        childSourceBinders child →
      Concrete.Elaboration.BinderContext.Enumeration input childTargetBinders
        (trace.origin child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend (trace.origin child)).Exact
        (trace.origin child) →
      ∀ (sourceBody : Region  childSourceContext.length
          childSourceRels)
        (targetBody : Region  childTargetContext.length
          childTargetRels),
      Concrete.Elaboration.compileRegion?  trace.sourceDiagram
          fuelSource child childSourceContext childSourceBinders =
        some sourceBody →
      Concrete.Elaboration.compileRegion?  input childFuelTarget
          (trace.origin child) childTargetContext childTargetBinders =
        some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (member : occurrence ∈
      Concrete.Elaboration.localOccurrences trace.sourceDiagram sourceParent)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrenceWith?  trace.sourceDiagram
        (Concrete.Elaboration.compileRegion?  trace.sourceDiagram
          fuelSource)
        sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrenceWith?  input
        (Concrete.Elaboration.compileRegion?  input fuelTarget)
        targetContext targetBinders (trace.occurrenceMap occurrence) =
          some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      contextWitness.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      exact trace.compileNode_itemSimulation targetWellFormed model
        direction sourceContext targetContext sourceBinders targetBinders
        binderWitness node regionMap (nodeShape node rfl) sourceItem targetItem
        sourceCompiled targetCompiled
  | child child =>
      have sourceParentEq :=
        (Concrete.Elaboration.mem_localOccurrences_child trace.sourceDiagram
          sourceParent child).mp member
      have targetKind := regionShape child rfl sourceParentEq
      change
        Concrete.Elaboration.compileOccurrenceWith?  input
            (Concrete.Elaboration.compileRegion?  input fuelTarget)
            targetContext targetBinders (.child (trace.origin child)) =
          some targetItem at targetCompiled
      cases sourceKind : trace.sourceDiagram.regions child with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult :
              Concrete.Elaboration.compileRegion?  trace.sourceDiagram
                fuelSource child sourceContext sourceBinders with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  Concrete.Elaboration.compileRegion?  input fuelTarget
                    (trace.origin child) targetContext targetBinders with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    targetKind, targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
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
                    (Concrete.Elaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.covers_cut_child
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
              Concrete.Elaboration.compileRegion?  trace.sourceDiagram
                fuelSource child sourceContext sourcePushed with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  Concrete.Elaboration.compileRegion?  input fuelTarget
                    (trace.origin child) targetContext targetPushed with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    targetKind, targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
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
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
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

end VisualProof.Concrete.VacuousElimTrace
