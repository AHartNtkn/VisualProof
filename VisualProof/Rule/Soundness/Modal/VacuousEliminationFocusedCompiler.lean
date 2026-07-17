import VisualProof.Rule.Soundness.Modal.VacuousEliminationFocusedTransport

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

theorem focusedOccurrence_itemSimulation
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (targetParent : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (contextWitness : PromotedContextWitness trace sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact (trace.targetIndex targetWellFormed))
    (targetExact : targetContext.Exact targetParent)
    (sourceBindersCover :
      sourceBinders.Covers (trace.targetIndex targetWellFormed))
    (targetBindersCover : targetBinders.Covers targetParent)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input targetBinders
        targetParent)
    (occurrence : ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount)
    (nodeAtParent : ∀ node, occurrence = .node node →
      (input.nodes node).region = targetParent)
    (childAtParent : ∀ child, occurrence = .child child →
      (input.regions (trace.origin child)).parent? = some targetParent)
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
    (member : occurrence ∈ ConcreteElaboration.localOccurrences
      trace.sourceDiagram (trace.targetIndex targetWellFormed))
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
  apply trace.compileOccurrence_itemSimulation sourceWellFormed
    targetWellFormed model named direction fuelSource fuelTarget
    (trace.targetIndex targetWellFormed) targetParent sourceContext
    targetContext contextWitness sourceBinders targetBinders binderWitness
    sourceExact targetExact sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration occurrence (fun _ => targetParent)
  · intro node occurrenceEq
    have shape := trace.focused_nodeShape node targetParent
      (nodeAtParent node occurrenceEq)
    cases promotedNode : trace.promotion.nodes node <;>
      simp [VacuousElimTrace.sourceDiagram, PromoteDiagramTrace.diagram,
        promotedNode] at shape ⊢ <;>
      exact shape
  · intro child occurrenceEq _
    have shape := trace.focused_regionShape child targetParent
      (childAtParent child occurrenceEq)
    cases promotedRegion : trace.promotion.regions child <;>
      simp [VacuousElimTrace.sourceDiagram, PromoteDiagramTrace.diagram,
        promotedRegion] at shape ⊢ <;>
      exact shape
  · exact recurseAt
  · exact member
  · exact sourceCompiled
  · exact targetCompiled

theorem focusedItems_regionSimulation
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : RelCtx}
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex targetWellFormed)).Exact
        (trace.targetIndex targetWellFormed))
    (targetExact :
      (targetContext.extend trace.parent).Exact trace.parent)
    (sourceBindersCover :
      sourceBinders.Covers (trace.targetIndex targetWellFormed))
    (targetBindersCover : targetBinders.Covers trace.parent)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input targetBinders
        trace.parent)
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
    (sourceItems : ItemSeq signature
      (sourceContext.extend (trace.targetIndex targetWellFormed)).length
      sourceRels)
    (targetItems : ItemSeq signature
      (targetContext.extend trace.parent).length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        trace.sourceDiagram
        (ConcreteElaboration.compileRegion? signature trace.sourceDiagram
          fuelSource)
        (sourceContext.extend (trace.targetIndex targetWellFormed))
        sourceBinders
        (ConcreteElaboration.localOccurrences trace.sourceDiagram
          (trace.targetIndex targetWellFormed)) = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuelTarget)
        (targetContext.extend trace.parent) targetBinders
        (ConcreteElaboration.localOccurrences input trace.parent) =
          some targetItems) :
    ConcreteElaboration.RegionSimulation model named direction
      context.indexRelation
      ((ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
        (trace.targetIndex targetWellFormed) sourceItems).renameRelations
          binderWitness.relationMap)
      (ConcreteElaboration.finishRegion input targetContext trace.parent
        targetItems) := by
  let sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin trace.sourceDiagram.regionCount) →
      (context : ConcreteElaboration.WireContext trace.sourceDiagram) →
      ConcreteElaboration.BinderContext trace.sourceDiagram rels →
      Option (Region signature context.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature
      trace.sourceDiagram fuelSource
  let targetRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (context : ConcreteElaboration.WireContext input) →
      ConcreteElaboration.BinderContext input rels →
      Option (Region signature context.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature input fuelTarget
  obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
      (sourceContext.extend (trace.targetIndex targetWellFormed))
      sourceBinders
      (trace.keptOccurrences targetWellFormed ++
        trace.selectedOccurrences targetWellFormed)
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          trace.sourceDiagram sourceRecurse
          (sourceContext.extend (trace.targetIndex targetWellFormed))
          sourceBinders sourceCompiled
          ((trace.focusOccurrences_perm_partition
            targetWellFormed).mem_iff.mp member))
  obtain ⟨sourceKeptItems, sourceSelectedItems, sourceKeptCompiled,
      sourceSelectedCompiled, sourcePartitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split sourceRecurse
      (sourceContext.extend (trace.targetIndex targetWellFormed))
      sourceBinders (trace.keptOccurrences targetWellFormed)
      (trace.selectedOccurrences targetWellFormed) sourcePartitionItems
      sourcePartitionCompiled
  obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete targetRecurse
      (targetContext.extend trace.parent) targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap ++
        [ConcreteElaboration.LocalOccurrence.child bubble])
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          input targetRecurse (targetContext.extend trace.parent)
          targetBinders targetCompiled
          ((trace.targetFocusOccurrences_perm
            targetWellFormed).mem_iff.mp member))
  obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
      targetBubbleCompiled, targetPartitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
      (targetContext.extend trace.parent) targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap)
      [ConcreteElaboration.LocalOccurrence.child bubble]
      targetPartitionItems targetPartitionCompiled
  simp only [ConcreteElaboration.compileOccurrencesWith?] at targetBubbleCompiled
  dsimp only [targetRecurse] at targetBubbleCompiled
  simp only [ConcreteElaboration.compileOccurrenceWith?, trace.bubble_eq]
    at targetBubbleCompiled
  cases bubbleResult : ConcreteElaboration.compileRegion? signature input
      fuelTarget bubble (targetContext.extend trace.parent)
      (targetBinders.push bubble trace.arity) with
  | none => simp [bubbleResult] at targetBubbleCompiled
  | some bubbleBody =>
      simp [bubbleResult] at targetBubbleCompiled
      subst targetBubbleItems
      cases fuelTarget with
      | zero => simp [ConcreteElaboration.compileRegion?] at bubbleResult
      | succ bubbleFuel =>
          simp only [ConcreteElaboration.compileRegion?] at bubbleResult
          rw [trace.bubble_localOccurrences targetWellFormed] at bubbleResult
          obtain ⟨targetSelectedItems, targetSelectedCompiled,
              bubbleBodyEq⟩ := Option.bind_eq_some_iff.mp bubbleResult
          have bubbleBodyEq' :
              ConcreteElaboration.finishRegion input
                  (targetContext.extend trace.parent) bubble
                  targetSelectedItems = bubbleBody :=
            Option.some.inj bubbleBodyEq
          subst bubbleBody
          let focusedContext := context.extendFocused targetWellFormed
          let selectedContext := context.extendSelected targetWellFormed
          have targetBubbleCover :=
            ConcreteElaboration.BinderContext.push_covers_bubble_child
              targetBindersCover trace.bubble_eq
          have targetBubbleEnumeration :=
            targetEnumeration.bubbleChild targetWellFormed trace.bubble_eq
          have targetSelectedExact :=
            trace.targetSelected_exact targetWellFormed targetContext
              targetExact
          let bubbleBinderWitness :=
            MappedBinderWitness.intoBubble binderWitness trace.arity
          have keptPointwise : ∀ occurrence,
              occurrence ∈ trace.keptOccurrences targetWellFormed →
              ∀ sourceItem targetItem,
              ConcreteElaboration.compileOccurrenceWith? signature
                  trace.sourceDiagram sourceRecurse
                  (sourceContext.extend (trace.targetIndex targetWellFormed))
                  sourceBinders occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature input
                  targetRecurse (targetContext.extend trace.parent)
                  targetBinders (trace.occurrenceMap occurrence) =
                    some targetItem →
              ConcreteElaboration.ItemSimulation model named direction
                focusedContext.indexRelation
                (sourceItem.renameRelations binderWitness.relationMap)
                targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model named direction fuelSource
              (bubbleFuel + 1) trace.parent
              (sourceContext.extend (trace.targetIndex targetWellFormed))
              (targetContext.extend trace.parent) focusedContext
              sourceBinders targetBinders binderWitness sourceExact targetExact
              sourceBindersCover targetBindersCover sourceEnumeration
              targetEnumeration occurrence
            · intro node occurrenceEq
              cases occurrenceEq
              exact trace.kept_node_region targetWellFormed node member
            · intro child occurrenceEq
              cases occurrenceEq
              exact trace.kept_child_parent targetWellFormed child member
            · exact recurseAt
            · exact (List.mem_filter.mp member).1
            · simpa [sourceRecurse] using sourceOccurrence
            · simpa [targetRecurse] using targetOccurrence
          have selectedPointwise : ∀ occurrence,
              occurrence ∈ trace.selectedOccurrences targetWellFormed →
              ∀ sourceItem targetItem,
              ConcreteElaboration.compileOccurrenceWith? signature
                  trace.sourceDiagram sourceRecurse
                  (sourceContext.extend (trace.targetIndex targetWellFormed))
                  sourceBinders occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature input
                  (ConcreteElaboration.compileRegion? signature input
                    bubbleFuel)
                  ((targetContext.extend trace.parent).extend bubble)
                  (targetBinders.push bubble trace.arity)
                  (trace.occurrenceMap occurrence) = some targetItem →
              ConcreteElaboration.ItemSimulation model named direction
                selectedContext.indexRelation
                (sourceItem.renameRelations bubbleBinderWitness.relationMap)
                targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model named direction fuelSource bubbleFuel
              bubble
              (sourceContext.extend (trace.targetIndex targetWellFormed))
              ((targetContext.extend trace.parent).extend bubble)
              selectedContext sourceBinders
              (targetBinders.push bubble trace.arity) bubbleBinderWitness
              sourceExact targetSelectedExact sourceBindersCover
              targetBubbleCover sourceEnumeration targetBubbleEnumeration
              occurrence
            · intro node occurrenceEq
              cases occurrenceEq
              exact trace.selected_node_region targetWellFormed node member
            · intro child occurrenceEq
              cases occurrenceEq
              exact trace.selected_child_parent targetWellFormed child member
            · exact recurseAt
            · exact (List.mem_filter.mp member).1
            · simpa [sourceRecurse] using sourceOccurrence
            · exact targetOccurrence
          have keptSimulation :=
            ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model named direction sourceRecurse targetRecurse
              (sourceContext.extend (trace.targetIndex targetWellFormed))
              (targetContext.extend trace.parent) sourceBinders targetBinders
              focusedContext.indexRelation binderWitness.relationMap
              trace.occurrenceMap (trace.keptOccurrences targetWellFormed)
              keptPointwise sourceKeptItems targetKeptItems sourceKeptCompiled
              targetKeptCompiled
          have selectedSimulation :=
            ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model named direction sourceRecurse
              (ConcreteElaboration.compileRegion? signature input bubbleFuel)
              (sourceContext.extend (trace.targetIndex targetWellFormed))
              ((targetContext.extend trace.parent).extend bubble)
              sourceBinders (targetBinders.push bubble trace.arity)
              selectedContext.indexRelation bubbleBinderWitness.relationMap
              trace.occurrenceMap (trace.selectedOccurrences targetWellFormed)
              selectedPointwise sourceSelectedItems targetSelectedItems
              sourceSelectedCompiled targetSelectedCompiled
          have partitionSimulation :=
            trace.focusedPartition_regionSimulation targetWellFormed model
              named direction sourceContext targetContext context sourceExact
              targetSelectedExact.nodup binderWitness.relationMap
              sourceKeptItems sourceSelectedItems targetKeptItems
              targetSelectedItems keptSimulation selectedSimulation
          intro sourceEnvironment targetEnvironment targetRelations agreement
          let sourceRelations : RelEnv model.Carrier sourceRels :=
            RelEnv.pullback binderWitness.relationMap targetRelations
          have relationAgreement :
              RelEnv.Agrees binderWitness.relationMap sourceRelations
                targetRelations :=
            RelEnv.pullback_agrees binderWitness.relationMap targetRelations
          have sourceOriginalRename :
              denoteRegion model named sourceEnvironment targetRelations
                  ((ConcreteElaboration.finishRegion trace.sourceDiagram
                    sourceContext (trace.targetIndex targetWellFormed)
                    sourceItems).renameRelations binderWitness.relationMap) ↔
                denoteRegion model named sourceEnvironment sourceRelations
                  (ConcreteElaboration.finishRegion trace.sourceDiagram
                    sourceContext (trace.targetIndex targetWellFormed)
                    sourceItems) :=
            denoteRegion_renameRelations model named binderWitness.relationMap
              sourceRelations targetRelations relationAgreement
              sourceEnvironment _
          have sourcePartitionRename :
              denoteRegion model named sourceEnvironment targetRelations
                  ((ConcreteElaboration.finishRegion trace.sourceDiagram
                    sourceContext (trace.targetIndex targetWellFormed)
                    sourcePartitionItems).renameRelations
                      binderWitness.relationMap) ↔
                denoteRegion model named sourceEnvironment sourceRelations
                  (ConcreteElaboration.finishRegion trace.sourceDiagram
                    sourceContext (trace.targetIndex targetWellFormed)
                    sourcePartitionItems) :=
            denoteRegion_renameRelations model named binderWitness.relationMap
              sourceRelations targetRelations relationAgreement
              sourceEnvironment _
          have sourcePermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              trace.sourceDiagram sourceRecurse
              (sourceContext.extend (trace.targetIndex targetWellFormed))
              sourceBinders
              (trace.focusOccurrences_perm_partition targetWellFormed).symm
              sourceCompiled sourcePartitionCompiled model named
          have targetPermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              input targetRecurse (targetContext.extend trace.parent)
              targetBinders
              (trace.targetFocusOccurrences_perm targetWellFormed).symm
              targetCompiled targetPartitionCompiled model named
          rw [← sourcePartitionEq, ← targetPartitionEq] at partitionSimulation
          cases direction with
          | forward =>
              intro sourceDenotation
              obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                (finishRegion_denote_iff trace.sourceDiagram sourceContext
                  (trace.targetIndex targetWellFormed) sourceItems model named
                  sourceEnvironment sourceRelations).mp
                  (sourceOriginalRename.mp sourceDenotation)
              have sourcePartitionRaw :=
                (finishRegion_denote_iff trace.sourceDiagram sourceContext
                  (trace.targetIndex targetWellFormed) sourcePartitionItems
                  model named sourceEnvironment sourceRelations).mpr
                  ⟨sourceLocal,
                    (sourcePermutation
                      (ConcreteElaboration.extendedEnvironment sourceContext
                        (trace.targetIndex targetWellFormed)
                        sourceEnvironment sourceLocal)
                      sourceRelations).mp sourceItemsDenote⟩
              have targetPartitionDenote := partitionSimulation
                sourceEnvironment targetEnvironment targetRelations agreement
                (sourcePartitionRename.mpr sourcePartitionRaw)
              obtain ⟨targetLocal, targetPartitionItemsDenote⟩ :=
                (finishRegion_denote_iff input targetContext trace.parent
                  targetPartitionItems model named targetEnvironment
                  targetRelations).mp targetPartitionDenote
              apply (finishRegion_denote_iff input targetContext trace.parent
                targetItems model named targetEnvironment targetRelations).mpr
              exact ⟨targetLocal,
                (targetPermutation
                  (ConcreteElaboration.extendedEnvironment targetContext
                    trace.parent targetEnvironment targetLocal)
                  targetRelations).mpr targetPartitionItemsDenote⟩
          | backward =>
              intro targetDenotation
              obtain ⟨targetLocal, targetItemsDenote⟩ :=
                (finishRegion_denote_iff input targetContext trace.parent
                  targetItems model named targetEnvironment targetRelations).mp
                  targetDenotation
              have targetPartitionItemsDenote :=
                (targetPermutation
                  (ConcreteElaboration.extendedEnvironment targetContext
                    trace.parent targetEnvironment targetLocal)
                  targetRelations).mp targetItemsDenote
              have sourcePartitionDenote := partitionSimulation
                sourceEnvironment targetEnvironment targetRelations agreement
                ((finishRegion_denote_iff input targetContext trace.parent
                  targetPartitionItems model named targetEnvironment
                  targetRelations).mpr
                  ⟨targetLocal, targetPartitionItemsDenote⟩)
              have sourcePartitionRaw :=
                sourcePartitionRename.mp sourcePartitionDenote
              obtain ⟨sourceLocal, sourcePartitionItemsDenote⟩ :=
                (finishRegion_denote_iff trace.sourceDiagram sourceContext
                  (trace.targetIndex targetWellFormed) sourcePartitionItems
                  model named sourceEnvironment sourceRelations).mp
                  sourcePartitionRaw
              apply sourceOriginalRename.mpr
              apply (finishRegion_denote_iff trace.sourceDiagram sourceContext
                (trace.targetIndex targetWellFormed) sourceItems model named
                sourceEnvironment sourceRelations).mpr
              exact ⟨sourceLocal,
                (sourcePermutation
                  (ConcreteElaboration.extendedEnvironment sourceContext
                    (trace.targetIndex targetWellFormed)
                    sourceEnvironment sourceLocal)
                  sourceRelations).mpr sourcePartitionItemsDenote⟩

end VisualProof.Rule.VacuousElimTrace
