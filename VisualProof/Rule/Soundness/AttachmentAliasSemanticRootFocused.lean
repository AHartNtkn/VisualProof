import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootContext

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- At a root-focused terminal body, the inserted alias block is exactly the
extra semantic factor between retained nodes and retained children. -/
theorem focusedRootItemsSimulation
    (mode : Mode)
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (sourceExact : sourceContext.Exact spine.bodyContainer)
    (targetExact : targetContext.Exact spine.bodyContainer)
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
      True → HEq childSourceBinders childTargetBinders →
      childSourceBinders.Covers child → childTargetBinders.Covers child →
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
        (indexRelation mode collapse) sourceBody targetBody)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (ConcreteElaboration.localOccurrences pattern.val.diagram
        spine.bodyContainer) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      (ConcreteElaboration.localOccurrences
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        spine.bodyContainer) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named mode.direction
      (indexRelation mode collapse) sourceItems targetItems := by
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer)
      (sourceChildOccurrences pattern.val spine.bodyContainer)
      sourceItems sourceCompiled
  rw [materialized_focused_localOccurrences] at targetCompiled
  have targetCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
          (liftOccurrence pattern.val attachment) ++
        (aliasOccurrences pattern.val attachment ++
          (sourceChildOccurrences pattern.val spine.bodyContainer).map
            (liftOccurrence pattern.val attachment))) = some targetItems := by
    simpa only [List.append_assoc] using targetCompiled
  obtain ⟨targetNodeItems, targetRestItems, targetNodeCompiled,
      targetRestCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment))
      (aliasOccurrences pattern.val attachment ++
        (sourceChildOccurrences pattern.val spine.bodyContainer).map
          (liftOccurrence pattern.val attachment)) targetItems targetCompiled'
  obtain ⟨aliasItems, targetChildItems, aliasCompiled, targetChildCompiled,
      targetRestItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  have childSimulation := childOccurrences_simulation pattern attachment spine
    targetWellFormed model named mode.direction fuelSource fuelTarget
    sourceContext targetContext (indexRelation mode collapse)
    sourceBinders targetBinders bindersEqual sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse sourceChildItems targetChildItems
    sourceChildCompiled targetChildCompiled
  subst sourceItems
  subst targetRestItems
  subst targetItems
  cases mode with
  | forward =>
      have nodeSimulation := oldNodeOccurrences_simulation_collapse pattern
        attachment spine model named
        (ConcreteElaboration.compileRegion? signature pattern.val.diagram
          fuelSource)
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget)
        sourceContext targetContext collapse sourceExact.nodup sourceBinders
        targetBinders bindersEqual sourceNodeItems targetNodeItems
        sourceNodeCompiled targetNodeCompiled
      intro sourceEnv targetEnv relEnv environments sourceDenotes
      simp only [denoteItemSeq_append] at sourceDenotes ⊢
      have targetNodes := nodeSimulation sourceEnv targetEnv relEnv environments
        sourceDenotes.1
      have targetChildren := childSimulation sourceEnv targetEnv relEnv
        environments sourceDenotes.2
      have envEq :=
        (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
          collapse.indexMap sourceEnv targetEnv).mp environments
      have targetAliases := aliasOccurrences_denote_of_collapse pattern attachment
        spine targetWellFormed targetContext sourceContext collapse
        sourceExact.nodup targetExact targetBinders
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget)
        aliasItems aliasCompiled model named sourceEnv targetEnv envEq.symm relEnv
      exact ⟨targetNodes, targetAliases, targetChildren⟩
  | backward =>
      have nodeSimulation := oldNodeOccurrences_simulation pattern attachment
        spine model named .backward
        (ConcreteElaboration.compileRegion? signature pattern.val.diagram
          fuelSource)
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget)
        sourceContext targetContext collapse targetExact.nodup sourceBinders
        targetBinders bindersEqual sourceNodeItems targetNodeItems
        sourceNodeCompiled targetNodeCompiled
      intro sourceEnv targetEnv relEnv environments targetDenotes
      simp only [denoteItemSeq_append] at targetDenotes ⊢
      have sourceNodes := nodeSimulation sourceEnv targetEnv relEnv environments
        targetDenotes.1
      have sourceChildren := childSimulation sourceEnv targetEnv relEnv
        environments targetDenotes.2.2
      exact ⟨sourceNodes, sourceChildren⟩

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
