import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootContext

namespace VisualProof.Concrete.Splice.AttachmentAliasMaterialization

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- At a root-focused terminal body, the inserted alias block is exactly the
extra semantic factor between retained nodes and retained children. -/
theorem focusedRootItemsSimulation
    (mode : Mode)
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (model : Model)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (sourceExact : sourceContext.Exact spine.bodyContainer)
    (targetExact : targetContext.Exact spine.bodyContainer)
    (sourceBinders : Concrete.Elaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers spine.bodyContainer)
    (targetBindersCover : targetBinders.Covers spine.bodyContainer)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      pattern.val.diagram sourceBinders spine.bodyContainer)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetBinders spine.bodyContainer)
    (recurse : ∀ {childDirection : Concrete.Elaboration.SimulationDirection}
      {child : Fin pattern.val.diagram.regionCount}
      {childRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext
        pattern.val.diagram childRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer) childRels}
      {sourceBody : Region  sourceContext.length childRels}
      {targetBody : Region  targetContext.length childRels},
      (pattern.val.diagram.regions child).parent? = some spine.bodyContainer →
      ((materializedDiagram pattern.val attachment spine.bodyContainer).regions
        child).parent? = some spine.bodyContainer →
      True → HEq childSourceBinders childTargetBinders →
      childSourceBinders.Covers child → childTargetBinders.Covers child →
      Concrete.Elaboration.BinderContext.Enumeration pattern.val.diagram
        childSourceBinders child →
      Concrete.Elaboration.BinderContext.Enumeration
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        childTargetBinders child →
      Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource
          child sourceContext childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion?
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget child targetContext childTargetBinders = some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        (indexRelation mode collapse) sourceBody targetBody)
    (sourceItems : ItemSeq  sourceContext.length rels)
    (targetItems : ItemSeq  targetContext.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram
      (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (Concrete.Elaboration.localOccurrences pattern.val.diagram
        spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      (Concrete.Elaboration.localOccurrences
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        spine.bodyContainer) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  mode.direction
      (indexRelation mode collapse) sourceItems targetItems := by
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer)
      (sourceChildOccurrences pattern.val spine.bodyContainer)
      sourceItems sourceCompiled
  rw [materialized_focused_localOccurrences] at targetCompiled
  have targetCompiled' : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      targetContext targetBinders
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  have childSimulation := childOccurrences_simulation pattern attachment spine
    targetWellFormed model  mode.direction fuelSource fuelTarget
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
        attachment spine model
        (Concrete.Elaboration.compileRegion?  pattern.val.diagram
          fuelSource)
        (Concrete.Elaboration.compileRegion?
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
        (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
          collapse.indexMap sourceEnv targetEnv).mp environments
      have targetAliases := aliasOccurrences_denote_of_collapse pattern attachment
        spine targetWellFormed targetContext sourceContext collapse
        sourceExact.nodup targetExact targetBinders
        (Concrete.Elaboration.compileRegion?
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget)
        aliasItems aliasCompiled model  sourceEnv targetEnv envEq.symm relEnv
      exact ⟨targetNodes, targetAliases, targetChildren⟩
  | backward =>
      have nodeSimulation := oldNodeOccurrences_simulation pattern attachment
        spine model  .backward
        (Concrete.Elaboration.compileRegion?  pattern.val.diagram
          fuelSource)
        (Concrete.Elaboration.compileRegion?
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

end VisualProof.Concrete.Splice.AttachmentAliasMaterialization
