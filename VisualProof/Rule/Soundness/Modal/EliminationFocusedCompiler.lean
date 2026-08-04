import VisualProof.Rule.Soundness.Modal.EliminationFocusedTransport

namespace VisualProof.Rule.DoubleCutElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedOccurrence_itemSimulation
    (trace : DoubleCutElimTrace input outer raw)
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
    (binderWitness : PromotedBinderWitness trace sourceBinders targetBinders)
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
      (childBinderWitness : PromotedBinderWitness trace childSourceBinders
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
    exact trace.focused_nodeShape node targetParent
      (nodeAtParent node occurrenceEq)
  · intro child occurrenceEq _
    exact trace.focused_regionShape child targetParent
      (childAtParent child occurrenceEq)
  · exact recurseAt
  · exact member
  · exact sourceCompiled
  · exact targetCompiled

theorem focusedItems_regionSimulation
    (trace : DoubleCutElimTrace input outer raw)
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
    (binderWitness : PromotedBinderWitness trace sourceBinders targetBinders)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex targetWellFormed)).Exact
        (trace.targetIndex targetWellFormed))
    (targetExact :
      (targetContext.extend trace.target).Exact trace.target)
    (sourceBindersCover :
      sourceBinders.Covers (trace.targetIndex targetWellFormed))
    (targetBindersCover : targetBinders.Covers trace.target)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input targetBinders
        trace.target)
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
      (childBinderWitness : PromotedBinderWitness trace childSourceBinders
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
      (targetContext.extend trace.target).length targetRels)
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
        (targetContext.extend trace.target) targetBinders
        (ConcreteElaboration.localOccurrences input trace.target) =
          some targetItems) :
    ConcreteElaboration.RegionSimulation model named direction
      context.indexRelation
      ((ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
        (trace.targetIndex targetWellFormed) sourceItems).renameRelations
          binderWitness.relationMap)
      (ConcreteElaboration.finishRegion input targetContext trace.target
        targetItems) := by
  cases binderWitness.relationContexts_eq
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
      (targetContext.extend trace.target) targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap ++
        [ConcreteElaboration.LocalOccurrence.child outer])
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          input targetRecurse (targetContext.extend trace.target)
          targetBinders targetCompiled
          ((trace.targetFocusOccurrences_perm
            targetWellFormed).mem_iff.mp member))
  obtain ⟨targetKeptItems, targetOuterItems, targetKeptCompiled,
      targetOuterCompiled, targetPartitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
      (targetContext.extend trace.target) targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap)
      [ConcreteElaboration.LocalOccurrence.child outer]
      targetPartitionItems targetPartitionCompiled
  simp only [ConcreteElaboration.compileOccurrencesWith?] at targetOuterCompiled
  dsimp only [targetRecurse] at targetOuterCompiled
  simp only [ConcreteElaboration.compileOccurrenceWith?, trace.outer_eq]
    at targetOuterCompiled
  cases outerResult : ConcreteElaboration.compileRegion? signature input
      fuelTarget outer (targetContext.extend trace.target) targetBinders with
  | none => simp [outerResult] at targetOuterCompiled
  | some outerBody =>
      simp [outerResult] at targetOuterCompiled
      subst targetOuterItems
      cases fuelTarget with
      | zero =>
          simp [ConcreteElaboration.compileRegion?] at outerResult
      | succ outerFuel =>
          simp only [ConcreteElaboration.compileRegion?] at outerResult
          rw [trace.outer_localOccurrences] at outerResult
          obtain ⟨outerItems, outerItemsCompiled, outerBodyEq⟩ :=
            Option.bind_eq_some_iff.mp outerResult
          have outerBodyEq' :
              ConcreteElaboration.finishRegion input
                  (targetContext.extend trace.target) outer outerItems =
                outerBody := Option.some.inj outerBodyEq
          subst outerBody
          simp only [ConcreteElaboration.compileOccurrencesWith?] at outerItemsCompiled
          simp only [ConcreteElaboration.compileOccurrenceWith?, trace.inner_eq]
            at outerItemsCompiled
          cases innerResult : ConcreteElaboration.compileRegion? signature input
              outerFuel trace.inner
              ((targetContext.extend trace.target).extend outer)
              targetBinders with
          | none => simp [innerResult] at outerItemsCompiled
          | some innerBody =>
              simp [innerResult] at outerItemsCompiled
              subst outerItems
              cases outerFuel with
              | zero =>
                  simp [ConcreteElaboration.compileRegion?] at innerResult
              | succ innerFuel =>
                  simp only [ConcreteElaboration.compileRegion?] at innerResult
                  rw [trace.inner_localOccurrences targetWellFormed]
                    at innerResult
                  obtain ⟨targetSelectedItems, targetSelectedCompiled,
                      innerBodyEq⟩ := Option.bind_eq_some_iff.mp innerResult
                  have innerBodyEq' :
                      ConcreteElaboration.finishRegion input
                          ((targetContext.extend trace.target).extend outer)
                          trace.inner targetSelectedItems = innerBody :=
                    Option.some.inj innerBodyEq
                  subst innerBody
                  let focusedContext := context.extendFocused targetWellFormed
                  let selectedContext := context.extendSelected targetWellFormed
                  have targetOuterCover :=
                    ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover trace.outer_eq
                  have targetInnerCover :=
                    ConcreteElaboration.BinderContext.covers_cut_child
                      targetOuterCover trace.inner_eq
                  have targetOuterEnumeration :=
                    targetEnumeration.cutChild targetWellFormed trace.outer_eq
                  have targetInnerEnumeration :=
                    targetOuterEnumeration.cutChild targetWellFormed
                      trace.inner_eq
                  have targetSelectedExact :=
                    trace.targetSelected_exact targetWellFormed targetContext
                      targetExact
                  have keptPointwise : ∀ occurrence,
                      occurrence ∈ trace.keptOccurrences targetWellFormed →
                      ∀ sourceItem targetItem,
                      ConcreteElaboration.compileOccurrenceWith? signature
                          trace.sourceDiagram sourceRecurse
                          (sourceContext.extend
                            (trace.targetIndex targetWellFormed))
                          sourceBinders occurrence = some sourceItem →
                      ConcreteElaboration.compileOccurrenceWith? signature input
                          targetRecurse (targetContext.extend trace.target)
                          targetBinders (trace.occurrenceMap occurrence) =
                            some targetItem →
                      ConcreteElaboration.ItemSimulation model named direction
                        focusedContext.indexRelation
                        (sourceItem.renameRelations binderWitness.relationMap)
                        targetItem := by
                    intro occurrence member sourceItem targetItem
                      sourceOccurrence targetOccurrence
                    apply trace.focusedOccurrence_itemSimulation
                      sourceWellFormed targetWellFormed model named direction
                      fuelSource (innerFuel + 1 + 1) trace.target
                      (sourceContext.extend
                        (trace.targetIndex targetWellFormed))
                      (targetContext.extend trace.target) focusedContext
                      sourceBinders targetBinders binderWitness sourceExact
                      targetExact sourceBindersCover targetBindersCover
                      sourceEnumeration targetEnumeration occurrence
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
                      occurrence ∈ trace.selectedOccurrences
                        targetWellFormed →
                      ∀ sourceItem targetItem,
                      ConcreteElaboration.compileOccurrenceWith? signature
                          trace.sourceDiagram sourceRecurse
                          (sourceContext.extend
                            (trace.targetIndex targetWellFormed))
                          sourceBinders occurrence = some sourceItem →
                      ConcreteElaboration.compileOccurrenceWith? signature input
                          (ConcreteElaboration.compileRegion? signature input
                            innerFuel)
                          (((targetContext.extend trace.target).extend outer).extend
                            trace.inner)
                          targetBinders (trace.occurrenceMap occurrence) =
                            some targetItem →
                      ConcreteElaboration.ItemSimulation model named direction
                        selectedContext.indexRelation
                        (sourceItem.renameRelations binderWitness.relationMap)
                        targetItem := by
                    intro occurrence member sourceItem targetItem
                      sourceOccurrence targetOccurrence
                    apply trace.focusedOccurrence_itemSimulation
                      sourceWellFormed targetWellFormed model named direction
                      fuelSource innerFuel trace.inner
                      (sourceContext.extend
                        (trace.targetIndex targetWellFormed))
                      (((targetContext.extend trace.target).extend outer).extend
                        trace.inner)
                      selectedContext sourceBinders targetBinders binderWitness
                      sourceExact targetSelectedExact sourceBindersCover
                      targetInnerCover sourceEnumeration targetInnerEnumeration
                      occurrence
                    · intro node occurrenceEq
                      cases occurrenceEq
                      exact trace.selected_node_region targetWellFormed node member
                    · intro child occurrenceEq
                      cases occurrenceEq
                      exact trace.selected_child_parent targetWellFormed child
                        member
                    · exact recurseAt
                    · exact (List.mem_filter.mp member).1
                    · simpa [sourceRecurse] using sourceOccurrence
                    · exact targetOccurrence
                  have keptSimulation :=
                    ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model named direction sourceRecurse targetRecurse
                      (sourceContext.extend
                        (trace.targetIndex targetWellFormed))
                      (targetContext.extend trace.target) sourceBinders
                      targetBinders focusedContext.indexRelation
                      binderWitness.relationMap trace.occurrenceMap
                      (trace.keptOccurrences targetWellFormed) keptPointwise
                      sourceKeptItems targetKeptItems sourceKeptCompiled
                      targetKeptCompiled
                  have selectedSimulation :=
                    ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model named direction sourceRecurse
                      (ConcreteElaboration.compileRegion? signature input
                        innerFuel)
                      (sourceContext.extend
                        (trace.targetIndex targetWellFormed))
                      (((targetContext.extend trace.target).extend outer).extend
                        trace.inner)
                      sourceBinders targetBinders selectedContext.indexRelation
                      binderWitness.relationMap trace.occurrenceMap
                      (trace.selectedOccurrences targetWellFormed)
                      selectedPointwise sourceSelectedItems targetSelectedItems
                      sourceSelectedCompiled targetSelectedCompiled
                  have relationMapEq :
                      (binderWitness.relationMap :
                        RelationRenaming sourceRels sourceRels) =
                        (fun {arity} (relation : RelVar sourceRels arity) =>
                          relation) := rfl
                  rw [relationMapEq, ItemSeq.renameRelations_id]
                    at keptSimulation selectedSimulation
                  have partitionSimulation :=
                    trace.focusedPartition_regionSimulation targetWellFormed
                      model named direction sourceContext targetContext context
                      sourceExact targetSelectedExact.nodup sourceKeptItems
                      sourceSelectedItems targetKeptItems targetSelectedItems
                      keptSimulation selectedSimulation
                  rw [relationMapEq, Region.renameRelations_id]
                  intro sourceEnvironment targetEnvironment relations agreement
                  have sourcePermutation :=
                    VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                      trace.sourceDiagram sourceRecurse
                      (sourceContext.extend
                        (trace.targetIndex targetWellFormed))
                      sourceBinders
                      (trace.focusOccurrences_perm_partition
                        targetWellFormed).symm
                      sourceCompiled sourcePartitionCompiled model named
                  have targetPermutation :=
                    VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                      input targetRecurse (targetContext.extend trace.target)
                      targetBinders
                      (trace.targetFocusOccurrences_perm
                        targetWellFormed).symm
                      targetCompiled targetPartitionCompiled model named
                  rw [← sourcePartitionEq, ← targetPartitionEq]
                    at partitionSimulation
                  cases direction with
                  | forward =>
                      intro sourceDenotation
                      apply (finishRegion_denote_iff input targetContext
                        trace.target targetItems model named targetEnvironment
                        relations).mpr
                      obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                        (finishRegion_denote_iff trace.sourceDiagram
                          sourceContext (trace.targetIndex targetWellFormed)
                          sourceItems model named sourceEnvironment
                          relations).mp sourceDenotation
                      obtain ⟨targetLocal, targetPartitionDenote⟩ :=
                          (finishRegion_denote_iff input targetContext
                          trace.target targetPartitionItems model named
                          targetEnvironment relations).mp
                          (partitionSimulation sourceEnvironment
                            targetEnvironment relations agreement
                            ((finishRegion_denote_iff trace.sourceDiagram
                              sourceContext
                              (trace.targetIndex targetWellFormed)
                              sourcePartitionItems model named sourceEnvironment
                              relations).mpr
                              ⟨sourceLocal, sourcePermutation
                                (ConcreteElaboration.extendedEnvironment
                                  sourceContext
                                  (trace.targetIndex targetWellFormed)
                                  sourceEnvironment sourceLocal)
                                relations |>.mp sourceItemsDenote⟩))
                      exact ⟨targetLocal,
                        (targetPermutation
                          (ConcreteElaboration.extendedEnvironment targetContext
                            trace.target targetEnvironment targetLocal)
                          relations).mpr targetPartitionDenote⟩
                  | backward =>
                      intro targetDenotation
                      obtain ⟨targetLocal, targetItemsDenote⟩ :=
                        (finishRegion_denote_iff input targetContext
                          trace.target targetItems model named targetEnvironment
                          relations).mp targetDenotation
                      have targetPartitionDenote :=
                        (targetPermutation
                          (ConcreteElaboration.extendedEnvironment targetContext
                            trace.target targetEnvironment targetLocal)
                          relations).mp targetItemsDenote
                      obtain ⟨sourceLocal, sourcePartitionDenote⟩ :=
                        (finishRegion_denote_iff trace.sourceDiagram
                          sourceContext (trace.targetIndex targetWellFormed)
                          sourcePartitionItems model named sourceEnvironment
                          relations).mp
                          (partitionSimulation sourceEnvironment
                            targetEnvironment relations agreement
                            ((finishRegion_denote_iff input targetContext
                              trace.target targetPartitionItems model named
                              targetEnvironment relations).mpr
                              ⟨targetLocal, targetPartitionDenote⟩))
                      apply (finishRegion_denote_iff trace.sourceDiagram
                        sourceContext (trace.targetIndex targetWellFormed)
                        sourceItems model named sourceEnvironment relations).mpr
                      exact ⟨sourceLocal,
                        (sourcePermutation
                          (ConcreteElaboration.extendedEnvironment sourceContext
                            (trace.targetIndex targetWellFormed)
                            sourceEnvironment sourceLocal)
                          relations).mpr sourcePartitionDenote⟩

end VisualProof.Rule.DoubleCutElimTrace
