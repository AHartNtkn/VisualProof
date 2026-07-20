import VisualProof.Rule.Soundness.AttachmentAliasSemanticFactor

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

@[simp] theorem item_renameRelations_identity
    (item : Item signature wires rels) :
    item.renameRelations
        (ConcreteElaboration.identityRelationRenaming rels) = item := by
  change item.renameRelations (fun relation => relation) = item
  exact Item.renameRelations_id item

@[simp] theorem items_renameRelations_identity
    (items : ItemSeq signature wires rels) :
    items.renameRelations
        (ConcreteElaboration.identityRelationRenaming rels) = items := by
  change items.renameRelations (fun relation => relation) = items
  exact ItemSeq.renameRelations_id items

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
    (relation : ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length)
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
        relation
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
      relation
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

theorem oldNodeOccurrences_simulation
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : ConcreteElaboration.WireContext pattern.val.diagram) →
      ConcreteElaboration.BinderContext pattern.val.diagram relations →
      Option (Region signature context.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : ConcreteElaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      ConcreteElaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        relations → Option (Region signature context.length relations))
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      pattern.val.diagram sourceRecurse sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetRecurse targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
      sourceItems targetItems := by
  have result := ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named direction sourceRecurse targetRecurse sourceContext targetContext
    sourceBinders targetBinders
    (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
    (ConcreteElaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceNodeOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceNodeOccurrences filterFin at member
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
      simp only [ConcreteElaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceOccurrence targetOccurrence
      have item := oldNode_itemSimulation_oldIndex pattern attachment spine
        sourceContext targetContext collapse targetNodup sourceBinders targetBinders
        bindersEqual node sourceItem targetItem sourceOccurrence targetOccurrence
        model named direction
      simpa [ConcreteElaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem oldNodeOccurrences_simulation_collapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : ConcreteElaboration.WireContext pattern.val.diagram) →
      ConcreteElaboration.BinderContext pattern.val.diagram relations →
      Option (Region signature context.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : ConcreteElaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      ConcreteElaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        relations → Option (Region signature context.length relations))
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      pattern.val.diagram sourceRecurse sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetRecurse targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named .forward
      (ConcreteElaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      sourceItems targetItems := by
  have result := ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named .forward sourceRecurse targetRecurse sourceContext targetContext
    sourceBinders targetBinders
    (ConcreteElaboration.ContextIndexRelation.backwardMap collapse.indexMap)
    (ConcreteElaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceNodeOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceNodeOccurrences filterFin at member
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
      simp only [ConcreteElaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceOccurrence targetOccurrence
      have item := oldNode_itemSimulation pattern attachment spine sourceContext
        targetContext collapse sourceNodup sourceBinders targetBinders bindersEqual
        node sourceItem targetItem sourceOccurrence targetOccurrence model named
        .forward
      simpa [ConcreteElaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem childOccurrences_simulation
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
    (relation : ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length)
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
        relation
        sourceBody targetBody)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (sourceChildOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget) targetContext targetBinders
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      relation
      sourceItems targetItems := by
  have result := ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named direction
    (ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource)
    (ConcreteElaboration.compileRegion? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer) fuelTarget)
    sourceContext targetContext sourceBinders targetBinders
      relation
    (ConcreteElaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceChildOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceChildOccurrences filterFin at member
      obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
      have parent := of_decide_eq_true (List.mem_filter.mp childMember).2
      have item := childOccurrence_itemSimulation pattern attachment spine
        targetWellFormed model named direction fuelSource fuelTarget sourceContext
        targetContext relation sourceBinders targetBinders bindersEqual
        sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
        recurse child parent sourceItem targetItem sourceOccurrence targetOccurrence
      simpa [ConcreteElaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem focusedLocalTransport_backward
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (bodyNeRoot : spine.bodyContainer ≠ pattern.val.diagram.root)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (fuelSource fuelTarget : Nat)
    (sourceOuterContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetOuterContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (outerCollapse : ContextCollapse pattern attachment spine targetOuterContext
      sourceOuterContext)
    (sourceExact : (sourceOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
    (targetExact : (targetOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
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
      {sourceBody : Region signature
        (sourceOuterContext.extend spine.bodyContainer).length childRels}
      {targetBody : Region signature
        (targetOuterContext.extend spine.bodyContainer).length childRels},
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
          child (sourceOuterContext.extend spine.bodyContainer)
          childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget child (targetOuterContext.extend spine.bodyContainer)
          childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (extendCollapse pattern attachment spine contract targetOuterContext
            sourceOuterContext outerCollapse spine.bodyContainer targetExact
            sourceExact).oldIndex)
        sourceBody targetBody)
    (sourceItems : ItemSeq signature
      (sourceOuterContext.extend spine.bodyContainer).length rels)
    (targetItems : ItemSeq signature
      (targetOuterContext.extend spine.bodyContainer).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (ConcreteElaboration.localOccurrences pattern.val.diagram
        spine.bodyContainer) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (ConcreteElaboration.localOccurrences
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        spine.bodyContainer) = some targetItems) :
    ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport .backward
      sourceOuterContext targetOuterContext spine.bodyContainer spine.bodyContainer
      (ConcreteElaboration.ContextIndexRelation.forwardMap outerCollapse.oldIndex)
      model named relEnv sourceItems targetItems := by
  let extendedCollapse := extendCollapse pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer)
      (sourceChildOccurrences pattern.val spine.bodyContainer)
      sourceItems sourceCompiled
  rw [materialized_focused_localOccurrences] at targetCompiled
  have targetCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
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
      (targetOuterContext.extend spine.bodyContainer) targetBinders
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
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  have nodeSimulation := oldNodeOccurrences_simulation pattern attachment spine
    model named .backward
    (ConcreteElaboration.compileRegion? signature pattern.val.diagram fuelSource)
    (ConcreteElaboration.compileRegion? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer) fuelTarget)
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer) extendedCollapse
    targetExact.nodup sourceBinders targetBinders bindersEqual sourceNodeItems
    targetNodeItems sourceNodeCompiled targetNodeCompiled
  have childSimulation := childOccurrences_simulation pattern attachment spine
    targetWellFormed model named .backward fuelSource fuelTarget
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer)
    (ConcreteElaboration.ContextIndexRelation.forwardMap extendedCollapse.oldIndex)
    sourceBinders
    targetBinders bindersEqual sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse sourceChildItems targetChildItems
    sourceChildCompiled targetChildCompiled
  intro relEnv sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter = targetOuter ∘ outerCollapse.oldIndex :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      outerCollapse.oldIndex sourceOuter targetOuter).mp outerAgrees
  subst sourceItems
  subst targetRestItems
  subst targetItems
  simp only [denoteItemSeq_append]
  intro targetLocalEnv targetDenotes
  let sourceLocalEnv := sourceLocal pattern attachment spine
    spine.bodyContainer bodyNeRoot targetLocalEnv
  refine ⟨sourceLocalEnv, ?_⟩
  have envOld := extendedEnv_oldIndex pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    bodyNeRoot targetExact sourceExact sourceOuter targetOuter outerEq
    targetLocalEnv
  have extendedAgrees :
      ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          extendedCollapse.oldIndex)
        (extendedEnv sourceOuterContext spine.bodyContainer sourceOuter
          sourceLocalEnv)
        (extendedEnv targetOuterContext spine.bodyContainer targetOuter
          targetLocalEnv) :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      extendedCollapse.oldIndex _ _).mpr envOld
  have sourceNodes := nodeSimulation _ _ relEnv extendedAgrees targetDenotes.1
  have sourceChildren := childSimulation _ _ relEnv extendedAgrees
    targetDenotes.2.2
  exact ⟨sourceNodes, sourceChildren⟩

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
