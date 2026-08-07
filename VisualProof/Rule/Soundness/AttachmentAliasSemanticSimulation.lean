import VisualProof.Rule.Soundness.AttachmentAliasSemanticFactor

namespace VisualProof.Concrete.Splice.AttachmentAliasMaterialization

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

@[simp] theorem item_renameRelations_identity
    (item : Item  wires rels) :
    item.renameRelations
        (Concrete.Elaboration.identityRelationRenaming rels) = item := by
  change item.renameRelations (fun relation => relation) = item
  exact Item.renameRelations_id item

@[simp] theorem items_renameRelations_identity
    (items : ItemSeq  wires rels) :
    items.renameRelations
        (Concrete.Elaboration.identityRelationRenaming rels) = items := by
  change items.renameRelations (fun relation => relation) = items
  exact ItemSeq.renameRelations_id items

theorem childOccurrence_itemSimulation
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (relation : Concrete.Elaboration.ContextIndexRelation
      sourceContext.length targetContext.length)
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
      True →
      HEq childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
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
        relation
        sourceBody targetBody)
    (child : Fin pattern.val.diagram.regionCount)
    (parent : (pattern.val.diagram.regions child).parent? =
      some spine.bodyContainer)
    (sourceItem : Item  sourceContext.length rels)
    (targetItem : Item  targetContext.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      pattern.val.diagram
      (Concrete.Elaboration.compileRegion?  pattern.val.diagram
        fuelSource) sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget) targetContext targetBinders (.child child) = some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      relation
      sourceItem targetItem := by
  have targetParent :
      ((materializedDiagram pattern.val attachment spine.bodyContainer).regions
        child).parent? = some spine.bodyContainer := parent
  cases sourceKind : pattern.val.diagram.regions child with
  | sheet =>
      simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind]
        at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = spine.bodyContainer := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind :
          (materializedDiagram pattern.val attachment spine.bodyContainer).regions
            child = .cut spine.bodyContainer := sourceKind
      cases sourceResult : Concrete.Elaboration.compileRegion?
          pattern.val.diagram fuelSource child sourceContext sourceBinders with
      | none =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : Concrete.Elaboration.compileRegion?
              (materializedDiagram pattern.val attachment spine.bodyContainer)
              fuelTarget child targetContext targetBinders with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                targetResult] at targetCompiled
          | some targetBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                targetResult] at targetCompiled
              subst targetItem
              have bodies := recurse (childDirection := direction.flip)
                parent targetParent True.intro bindersEqual
                (Concrete.Elaboration.BinderContext.covers_cut_child
                  sourceBindersCover sourceKind)
                (Concrete.Elaboration.BinderContext.covers_cut_child
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
      simp only [Concrete.Elaboration.compileOccurrenceWith?] at targetCompiled
      rw [targetKind] at targetCompiled
      simp only at targetCompiled
      cases sourceResult : Concrete.Elaboration.compileRegion?
          pattern.val.diagram fuelSource child sourceContext sourcePushed with
      | none =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : Concrete.Elaboration.compileRegion?
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
                (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                  sourceBindersCover sourceKind)
                (Concrete.Elaboration.BinderContext.push_covers_bubble_child
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
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : Concrete.Elaboration.WireContext pattern.val.diagram) →
      Concrete.Elaboration.BinderContext pattern.val.diagram relations →
      Option (Region  context.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : Concrete.Elaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      Concrete.Elaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        relations → Option (Region  context.length relations))
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : Concrete.Elaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceItems : ItemSeq  sourceContext.length rels)
    (targetItems : ItemSeq  targetContext.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram sourceRecurse sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetRecurse targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction
      (Concrete.Elaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
      sourceItems targetItems := by
  have result := Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model  direction sourceRecurse targetRecurse sourceContext targetContext
    sourceBinders targetBinders
    (Concrete.Elaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
    (Concrete.Elaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceNodeOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceNodeOccurrences filterFin at member
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
      simp only [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceOccurrence targetOccurrence
      have item := oldNode_itemSimulation_oldIndex pattern attachment spine
        sourceContext targetContext collapse targetNodup sourceBinders targetBinders
        bindersEqual node sourceItem targetItem sourceOccurrence targetOccurrence
        model  direction
      simpa [Concrete.Elaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem oldNodeOccurrences_simulation_collapse
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (model : Model)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : Concrete.Elaboration.WireContext pattern.val.diagram) →
      Concrete.Elaboration.BinderContext pattern.val.diagram relations →
      Option (Region  context.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (context : Concrete.Elaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      Concrete.Elaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        relations → Option (Region  context.length relations))
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : Concrete.Elaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceItems : ItemSeq  sourceContext.length rels)
    (targetItems : ItemSeq  targetContext.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram sourceRecurse sourceContext sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetRecurse targetContext targetBinders
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  .forward
      (Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      sourceItems targetItems := by
  have result := Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model  .forward sourceRecurse targetRecurse sourceContext targetContext
    sourceBinders targetBinders
    (Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap)
    (Concrete.Elaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceNodeOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceNodeOccurrences filterFin at member
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
      simp only [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceOccurrence targetOccurrence
      have item := oldNode_itemSimulation pattern attachment spine sourceContext
        targetContext collapse sourceNodup sourceBinders targetBinders bindersEqual
        node sourceItem targetItem sourceOccurrence targetOccurrence model
        .forward
      simpa [Concrete.Elaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem childOccurrences_simulation
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (relation : Concrete.Elaboration.ContextIndexRelation
      sourceContext.length targetContext.length)
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
        relation
        sourceBody targetBody)
    (sourceItems : ItemSeq  sourceContext.length rels)
    (targetItems : ItemSeq  targetContext.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram
      (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
      sourceContext sourceBinders
      (sourceChildOccurrences pattern.val spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget) targetContext targetBinders
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction
      relation
      sourceItems targetItems := by
  have result := Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model  direction
    (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
    (Concrete.Elaboration.compileRegion?
      (materializedDiagram pattern.val attachment spine.bodyContainer) fuelTarget)
    sourceContext targetContext sourceBinders targetBinders
      relation
    (Concrete.Elaboration.identityRelationRenaming rels)
    (liftOccurrence pattern.val attachment)
    (sourceChildOccurrences pattern.val spine.bodyContainer) (by
      intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
      unfold sourceChildOccurrences filterFin at member
      obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
      have parent := of_decide_eq_true (List.mem_filter.mp childMember).2
      have item := childOccurrence_itemSimulation pattern attachment spine
        targetWellFormed model  direction fuelSource fuelTarget sourceContext
        targetContext relation sourceBinders targetBinders bindersEqual
        sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
        recurse child parent sourceItem targetItem sourceOccurrence targetOccurrence
      simpa [Concrete.Elaboration.identityRelationRenaming] using item)
    sourceItems targetItems sourceCompiled targetCompiled
  simpa using result

theorem focusedLocalTransport_backward
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (model : Model)
    (fuelSource fuelTarget : Nat)
    (sourceOuterContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetOuterContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (outerCollapse : ContextCollapse pattern attachment spine targetOuterContext
      sourceOuterContext)
    (sourceExact : (sourceOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
    (targetExact : (targetOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
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
      {sourceBody : Region
        (sourceOuterContext.extend spine.bodyContainer).length childRels}
      {targetBody : Region
        (targetOuterContext.extend spine.bodyContainer).length childRels},
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
          child (sourceOuterContext.extend spine.bodyContainer)
          childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion?
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget child (targetOuterContext.extend spine.bodyContainer)
          childTargetBinders = some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        (Concrete.Elaboration.ContextIndexRelation.forwardMap
          (extendCollapse pattern attachment spine contract targetOuterContext
            sourceOuterContext outerCollapse spine.bodyContainer targetExact
            sourceExact).oldIndex)
        sourceBody targetBody)
    (sourceItems : ItemSeq
      (sourceOuterContext.extend spine.bodyContainer).length rels)
    (targetItems : ItemSeq
      (targetOuterContext.extend spine.bodyContainer).length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram
      (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (Concrete.Elaboration.localOccurrences pattern.val.diagram
        spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (Concrete.Elaboration.localOccurrences
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        spine.bodyContainer) = some targetItems) :
    ∀ relEnv, Concrete.Elaboration.DirectionalLocalTransport .backward
      sourceOuterContext targetOuterContext spine.bodyContainer spine.bodyContainer
      (Concrete.Elaboration.ContextIndexRelation.forwardMap outerCollapse.oldIndex)
      model  relEnv sourceItems targetItems := by
  let extendedCollapse := extendCollapse pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer)
      (sourceChildOccurrences pattern.val spine.bodyContainer)
      sourceItems sourceCompiled
  rw [materialized_focused_localOccurrences] at targetCompiled
  have targetCompiled' : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  have nodeSimulation := oldNodeOccurrences_simulation pattern attachment spine
    model  .backward
    (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
    (Concrete.Elaboration.compileRegion?
      (materializedDiagram pattern.val attachment spine.bodyContainer) fuelTarget)
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer) extendedCollapse
    targetExact.nodup sourceBinders targetBinders bindersEqual sourceNodeItems
    targetNodeItems sourceNodeCompiled targetNodeCompiled
  have childSimulation := childOccurrences_simulation pattern attachment spine
    targetWellFormed model  .backward fuelSource fuelTarget
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer)
    (Concrete.Elaboration.ContextIndexRelation.forwardMap extendedCollapse.oldIndex)
    sourceBinders
    targetBinders bindersEqual sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse sourceChildItems targetChildItems
    sourceChildCompiled targetChildCompiled
  intro relEnv sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter = targetOuter ∘ outerCollapse.oldIndex :=
    (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
      outerCollapse.oldIndex sourceOuter targetOuter).mp outerAgrees
  subst sourceItems
  subst targetRestItems
  subst targetItems
  simp only [denoteItemSeq_append]
  intro targetLocalEnv targetDenotes
  let sourceLocalEnv := oldIndexLocal pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact targetOuter targetLocalEnv
  refine ⟨sourceLocalEnv, ?_⟩
  have envOld := extendedEnv_oldIndex_general pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact sourceOuter targetOuter outerEq targetLocalEnv
  have extendedAgrees :
      Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
        (Concrete.Elaboration.ContextIndexRelation.forwardMap
          extendedCollapse.oldIndex)
        (extendedEnv sourceOuterContext spine.bodyContainer sourceOuter
          sourceLocalEnv)
        (extendedEnv targetOuterContext spine.bodyContainer targetOuter
          targetLocalEnv) :=
    (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
      extendedCollapse.oldIndex _ _).mpr envOld
  have sourceNodes := nodeSimulation _ _ relEnv extendedAgrees targetDenotes.1
  have sourceChildren := childSimulation _ _ relEnv extendedAgrees
    targetDenotes.2.2
  exact ⟨sourceNodes, sourceChildren⟩

theorem focusedLocalTransport_forward
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (model : Model)
    (fuelSource fuelTarget : Nat)
    (sourceOuterContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (targetOuterContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (outerCollapse : ContextCollapse pattern attachment spine targetOuterContext
      sourceOuterContext)
    (sourceExact : (sourceOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
    (targetExact : (targetOuterContext.extend spine.bodyContainer).Exact
      spine.bodyContainer)
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
      {sourceBody : Region
        (sourceOuterContext.extend spine.bodyContainer).length childRels}
      {targetBody : Region
        (targetOuterContext.extend spine.bodyContainer).length childRels},
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
          child (sourceOuterContext.extend spine.bodyContainer)
          childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion?
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          fuelTarget child (targetOuterContext.extend spine.bodyContainer)
          childTargetBinders = some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        (Concrete.Elaboration.ContextIndexRelation.backwardMap
          (extendCollapse pattern attachment spine contract targetOuterContext
            sourceOuterContext outerCollapse spine.bodyContainer targetExact
            sourceExact).indexMap)
        sourceBody targetBody)
    (sourceItems : ItemSeq
      (sourceOuterContext.extend spine.bodyContainer).length rels)
    (targetItems : ItemSeq
      (targetOuterContext.extend spine.bodyContainer).length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      pattern.val.diagram
      (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (Concrete.Elaboration.localOccurrences pattern.val.diagram
        spine.bodyContainer) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (Concrete.Elaboration.localOccurrences
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        spine.bodyContainer) = some targetItems) :
    ∀ relEnv, Concrete.Elaboration.DirectionalLocalTransport .forward
      sourceOuterContext targetOuterContext spine.bodyContainer spine.bodyContainer
      (Concrete.Elaboration.ContextIndexRelation.backwardMap outerCollapse.indexMap)
      model  relEnv sourceItems targetItems := by
  let extendedCollapse := extendCollapse pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        pattern.val.diagram fuelSource)
      (sourceOuterContext.extend spine.bodyContainer) sourceBinders
      (sourceNodeOccurrences pattern.val spine.bodyContainer)
      (sourceChildOccurrences pattern.val spine.bodyContainer)
      sourceItems sourceCompiled
  rw [materialized_focused_localOccurrences] at targetCompiled
  have targetCompiled' : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (fun {rels} => Concrete.Elaboration.compileRegion?
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        fuelTarget)
      (targetOuterContext.extend spine.bodyContainer) targetBinders
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  have nodeSimulation := oldNodeOccurrences_simulation_collapse pattern attachment
    spine model
    (Concrete.Elaboration.compileRegion?  pattern.val.diagram fuelSource)
    (Concrete.Elaboration.compileRegion?
      (materializedDiagram pattern.val attachment spine.bodyContainer) fuelTarget)
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer) extendedCollapse
    sourceExact.nodup sourceBinders targetBinders bindersEqual sourceNodeItems
    targetNodeItems sourceNodeCompiled targetNodeCompiled
  have childSimulation := childOccurrences_simulation pattern attachment spine
    targetWellFormed model  .forward fuelSource fuelTarget
    (sourceOuterContext.extend spine.bodyContainer)
    (targetOuterContext.extend spine.bodyContainer)
    (Concrete.Elaboration.ContextIndexRelation.backwardMap
      extendedCollapse.indexMap)
    sourceBinders targetBinders bindersEqual sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse sourceChildItems targetChildItems
    sourceChildCompiled targetChildCompiled
  intro relEnv sourceOuter targetOuter outerAgrees sourceLocal sourceDenotes
  have outerEq : sourceOuter ∘ outerCollapse.indexMap = targetOuter :=
    (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
      outerCollapse.indexMap sourceOuter targetOuter).mp outerAgrees
  let targetLocalEnv := targetLocal pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact sourceOuter sourceLocal
  refine ⟨targetLocalEnv, ?_⟩
  subst sourceItems
  subst targetRestItems
  subst targetItems
  simp only [denoteItemSeq_append] at sourceDenotes ⊢
  have envCollapse := extendedEnv_collapse pattern attachment spine contract
    targetOuterContext sourceOuterContext outerCollapse spine.bodyContainer
    targetExact sourceExact sourceOuter sourceLocal
  have extendedAgrees :
      Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
        (Concrete.Elaboration.ContextIndexRelation.backwardMap
          extendedCollapse.indexMap)
        (extendedEnv sourceOuterContext spine.bodyContainer sourceOuter
          sourceLocal)
        (extendedEnv targetOuterContext spine.bodyContainer targetOuter
          targetLocalEnv) :=
    (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
      extendedCollapse.indexMap _ _).mpr (by
        rw [← outerEq]
        exact envCollapse)
  have targetNodes := nodeSimulation _ _ relEnv extendedAgrees sourceDenotes.1
  have targetChildren := childSimulation _ _ relEnv extendedAgrees sourceDenotes.2
  have targetAliases := aliasOccurrences_denote_of_collapse pattern attachment
    spine targetWellFormed (targetOuterContext.extend spine.bodyContainer)
    (sourceOuterContext.extend spine.bodyContainer) extendedCollapse
    sourceExact.nodup targetExact targetBinders
    (Concrete.Elaboration.compileRegion?
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      fuelTarget)
    aliasItems aliasCompiled model
    (extendedEnv sourceOuterContext spine.bodyContainer sourceOuter sourceLocal)
    (extendedEnv targetOuterContext spine.bodyContainer targetOuter targetLocalEnv)
    (by
      rw [← outerEq]
      exact envCollapse.symm) relEnv
  exact ⟨targetNodes, targetAliases, targetChildren⟩

end Semantic

end VisualProof.Concrete.Splice.AttachmentAliasMaterialization
