import VisualProof.Rule.Soundness.AttachmentAliasSemanticFactor

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

theorem childOccurrence_itemSimulation
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (sourceBinders : ConcreteElaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers spine.bodyContainer)
    (targetBindersCover : targetBinders.Covers spine.bodyContainer)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      pattern.val.diagram sourceBinders spine.bodyContainer)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetBinders spine.bodyContainer)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin pattern.val.diagram.regionCount}
      {childRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        pattern.val.diagram childRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer) childRels}
      {sourceBody : Region signature sourceContext.length childRels}
      {targetBody : Region signature targetContext.length childRels},
      (pattern.val.diagram.regions child).parent? = some spine.bodyContainer →
      ((materializedDiagram pattern.val attachment spine.bodyContainer).regions
        child).parent? = some spine.bodyContainer →
      True →
      HEq childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration pattern.val.diagram
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        childTargetBinders child →
      ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource
          child sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget child targetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
        sourceBody targetBody)
    (child : Fin pattern.val.diagram.regionCount)
    (parent : (pattern.val.diagram.regions child).parent? =
      some spine.bodyContainer)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature pattern.val.diagram
        fuelSource) sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget) targetContext targetBinders (.child child) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
      sourceItem targetItem := by
  have targetParent :
      ((materializedDiagram pattern.val attachment spine.bodyContainer).regions
        child).parent? = some spine.bodyContainer := parent
  cases sourceKind : pattern.val.diagram.regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
        at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = spine.bodyContainer := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind :
          (materializedDiagram pattern.val attachment spine.bodyContainer).regions
            child = .cut spine.bodyContainer := sourceKind
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          pattern.val.diagram fuelSource child sourceContext sourceBinders with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (materializedDiagram pattern.val attachment spine.bodyContainer)
              fuelTarget child targetContext targetBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                targetResult] at targetCompiled
              subst targetItem
              have bodies := recurse (childDirection := direction.flip)
                parent targetParent True.intro bindersEqual
                (ConcreteElaboration.BinderContext.covers_cut_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.covers_cut_child
                  targetBindersCover targetKind)
                (sourceEnumeration.cutChild pattern.property.diagram_well_formed
                  sourceKind)
                (targetEnumeration.cutChild targetWellFormed targetKind)
                sourceResult targetResult
              intro sourceEnv targetEnv relEnv environments
              have bodyEntailment := bodies sourceEnv targetEnv relEnv environments
              simp only [cut_denotes_negation]
              cases direction with
              | forward => exact fun sourceNot targetDenotes =>
                  sourceNot (bodyEntailment targetDenotes)
              | backward =>
                  exact fun targetNot sourceDenotes =>
                    targetNot <| bodyEntailment sourceDenotes
  | bubble actualParent arity =>
      have actualParentEq : actualParent = spine.bodyContainer := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind :
          (materializedDiagram pattern.val attachment spine.bodyContainer).regions
            child = .bubble spine.bodyContainer arity := sourceKind
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push child arity
      simp only [ConcreteElaboration.compileOccurrenceWith?] at targetCompiled
      rw [targetKind] at targetCompiled
      simp only at targetCompiled
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          pattern.val.diagram fuelSource child sourceContext sourcePushed with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (materializedDiagram pattern.val attachment spine.bodyContainer)
              fuelTarget child targetContext targetPushed with
          | none =>
              simp only [targetPushed] at targetResult
              simp [targetResult] at targetCompiled
          | some targetBody =>
              simp only [targetPushed] at targetResult
              simp [targetResult] at targetCompiled
              subst targetItem
              have pushedEqual : HEq sourcePushed targetPushed := by
                cases bindersEqual
                rfl
              have bodies := recurse (childDirection := direction)
                parent targetParent True.intro pushedEqual
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetBindersCover targetKind)
                (sourceEnumeration.bubbleChild
                  pattern.property.diagram_well_formed sourceKind)
                (targetEnumeration.bubbleChild targetWellFormed targetKind)
                sourceResult targetResult
              intro sourceEnv targetEnv relEnv environments
              simp only [bubble_denotes_exists]
              cases direction with
              | forward =>
                  rintro ⟨relationValue, sourceDenotes⟩
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments sourceDenotes⟩
              | backward =>
                  rintro ⟨relationValue, targetDenotes⟩
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments targetDenotes⟩

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
