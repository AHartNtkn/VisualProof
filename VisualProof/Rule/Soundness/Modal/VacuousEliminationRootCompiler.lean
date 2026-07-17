import VisualProof.Rule.Soundness.Modal.VacuousEliminationFocusedCompiler
import VisualProof.Rule.Soundness.Modal.VacuousEliminationRootTransport

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedRootItems_transport
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram [])
    (targetBinders : ConcreteElaboration.BinderContext input [])
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact
        (trace.targetIndex targetWellFormed))
    (targetExact :
      (targetAmbient ++ targetLocals).Exact trace.parent)
    (sourceBindersCover :
      sourceBinders.Covers (trace.targetIndex targetWellFormed))
    (targetBindersCover : targetBinders.Covers trace.parent)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input targetBinders
        trace.parent)
    (targetAmbientSubset :
      ∀ wire, wire ∈ targetAmbient → wire ∈ sourceAmbient)
    (sourceAmbientSubset :
      ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
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
      (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq signature
      (targetAmbient ++ targetLocals).length [])
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        trace.sourceDiagram
        (ConcreteElaboration.compileRegion? signature trace.sourceDiagram
          fuelSource)
        (sourceAmbient ++ sourceLocals) sourceBinders
        (ConcreteElaboration.localOccurrences trace.sourceDiagram
          (trace.targetIndex targetWellFormed)) = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuelTarget)
        (targetAmbient ++ targetLocals) targetBinders
        (ConcreteElaboration.localOccurrences input trace.parent) =
          some targetItems) :
    ConcreteElaboration.DirectionalRootTransport direction
      sourceAmbient sourceLocals targetAmbient targetLocals
      (trace.wireIdentityRelation sourceAmbient targetAmbient)
      model named sourceItems targetItems := by
  let sourceRoot := sourceAmbient ++ sourceLocals
  let targetRoot := targetAmbient ++ targetLocals
  let sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin trace.sourceDiagram.regionCount) →
      (wireContext : ConcreteElaboration.WireContext trace.sourceDiagram) →
      ConcreteElaboration.BinderContext trace.sourceDiagram rels →
      Option (Region signature wireContext.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature
      trace.sourceDiagram fuelSource
  let targetRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (wireContext : ConcreteElaboration.WireContext input) →
      ConcreteElaboration.BinderContext input rels →
      Option (Region signature wireContext.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature input fuelTarget
  obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
      sourceRoot sourceBinders
      (trace.keptOccurrences targetWellFormed ++
        trace.selectedOccurrences targetWellFormed)
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
          sourceCompiled
          ((trace.focusOccurrences_perm_partition
            targetWellFormed).mem_iff.mp member))
  obtain ⟨sourceKeptItems, sourceSelectedItems, sourceKeptCompiled,
      sourceSelectedCompiled, sourcePartitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split sourceRecurse
      sourceRoot sourceBinders (trace.keptOccurrences targetWellFormed)
      (trace.selectedOccurrences targetWellFormed) sourcePartitionItems
      sourcePartitionCompiled
  obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete targetRecurse
      targetRoot targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap ++
        [ConcreteElaboration.LocalOccurrence.child bubble])
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          input targetRecurse targetRoot targetBinders targetCompiled
          ((trace.targetFocusOccurrences_perm
            targetWellFormed).mem_iff.mp member))
  obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
      targetBubbleCompiled, targetPartitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
      targetRoot targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap)
      [ConcreteElaboration.LocalOccurrence.child bubble]
      targetPartitionItems targetPartitionCompiled
  simp only [ConcreteElaboration.compileOccurrencesWith?] at targetBubbleCompiled
  dsimp only [targetRecurse] at targetBubbleCompiled
  simp only [ConcreteElaboration.compileOccurrenceWith?, trace.bubble_eq]
    at targetBubbleCompiled
  cases bubbleResult : ConcreteElaboration.compileRegion? signature input
      fuelTarget bubble targetRoot (targetBinders.push bubble trace.arity) with
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
              ConcreteElaboration.finishRegion input targetRoot bubble
                  targetSelectedItems = bubbleBody :=
            Option.some.inj bubbleBodyEq
          subst bubbleBody
          let selectedContext := context.extendRootSelected trace
            targetWellFormed sourceRoot targetRoot sourceExact
          have targetBubbleCover :=
            ConcreteElaboration.BinderContext.push_covers_bubble_child
              targetBindersCover trace.bubble_eq
          have targetBubbleEnumeration :=
            targetEnumeration.bubbleChild targetWellFormed trace.bubble_eq
          have targetSelectedExact :=
            trace.targetRootSelected_exact targetWellFormed targetRoot
              targetExact
          let bubbleBinderWitness :=
            MappedBinderWitness.intoBubble binderWitness trace.arity
          have keptPointwise : ∀ occurrence,
              occurrence ∈ trace.keptOccurrences targetWellFormed →
              ∀ sourceItem targetItem,
              ConcreteElaboration.compileOccurrenceWith? signature
                  trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
                  occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature input
                  targetRecurse targetRoot targetBinders
                  (trace.occurrenceMap occurrence) = some targetItem →
              ConcreteElaboration.ItemSimulation model named direction
                context.indexRelation
                (sourceItem.renameRelations binderWitness.relationMap)
                targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model named direction fuelSource
              (bubbleFuel + 1) trace.parent sourceRoot targetRoot context
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
                  trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
                  occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature input
                  (ConcreteElaboration.compileRegion? signature input
                    bubbleFuel)
                  (targetRoot.extend bubble)
                  (targetBinders.push bubble trace.arity)
                  (trace.occurrenceMap occurrence) = some targetItem →
              ConcreteElaboration.ItemSimulation model named direction
                selectedContext.indexRelation
                (sourceItem.renameRelations
                  bubbleBinderWitness.relationMap) targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model named direction fuelSource bubbleFuel
              bubble sourceRoot (targetRoot.extend bubble) selectedContext
              sourceBinders (targetBinders.push bubble trace.arity)
              bubbleBinderWitness sourceExact targetSelectedExact
              sourceBindersCover targetBubbleCover sourceEnumeration
              targetBubbleEnumeration occurrence
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
              model named direction sourceRecurse targetRecurse sourceRoot
              targetRoot sourceBinders targetBinders context.indexRelation
              binderWitness.relationMap trace.occurrenceMap
              (trace.keptOccurrences targetWellFormed) keptPointwise
              sourceKeptItems targetKeptItems sourceKeptCompiled
              targetKeptCompiled
          have selectedSimulation :=
            ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model named direction sourceRecurse
              (ConcreteElaboration.compileRegion? signature input bubbleFuel)
              sourceRoot (targetRoot.extend bubble) sourceBinders
              (targetBinders.push bubble trace.arity)
              selectedContext.indexRelation bubbleBinderWitness.relationMap
              trace.occurrenceMap (trace.selectedOccurrences targetWellFormed)
              selectedPointwise sourceSelectedItems targetSelectedItems
              sourceSelectedCompiled targetSelectedCompiled
          have baseMapEq :
              (binderWitness.relationMap : RelationRenaming [] []) =
                (fun {arity} (relation : RelVar [] arity) => relation) := by
            funext binderArity relation
            exact Fin.elim0 relation.index
          rw [baseMapEq, ItemSeq.renameRelations_id] at keptSimulation
          have partitionTransport := trace.focusedRootPartition_transport
            targetWellFormed model named direction sourceAmbient sourceLocals
            targetAmbient targetLocals context sourceExact
            targetSelectedExact.nodup targetAmbientSubset sourceAmbientSubset
            bubbleBinderWitness.relationMap sourceKeptItems sourceSelectedItems
            targetKeptItems targetSelectedItems keptSimulation
            selectedSimulation
          rw [← sourcePartitionEq, ← targetPartitionEq] at partitionTransport
          have sourcePermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
              (trace.focusOccurrences_perm_partition targetWellFormed).symm
              sourceCompiled sourcePartitionCompiled model named
          have targetPermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              input targetRecurse targetRoot targetBinders
              (trace.targetFocusOccurrences_perm targetWellFormed).symm
              targetCompiled targetPartitionCompiled model named
          intro sourceOuter targetOuter relations agreement
          cases direction with
          | forward =>
              intro sourceLocal sourceDenotation
              obtain ⟨targetLocal, targetPartitionDenotation⟩ :=
                partitionTransport sourceOuter targetOuter relations agreement
                  sourceLocal
                  ((sourcePermutation
                    (ConcreteElaboration.rootEnvironment sourceAmbient
                      sourceLocals sourceOuter sourceLocal) relations).mp
                    sourceDenotation)
              exact ⟨targetLocal,
                (targetPermutation
                  (ConcreteElaboration.rootEnvironment targetAmbient
                    targetLocals targetOuter targetLocal) relations).mpr
                  targetPartitionDenotation⟩
          | backward =>
              intro targetLocal targetDenotation
              obtain ⟨sourceLocal, sourcePartitionDenotation⟩ :=
                partitionTransport sourceOuter targetOuter relations agreement
                  targetLocal
                  ((targetPermutation
                    (ConcreteElaboration.rootEnvironment targetAmbient
                      targetLocals targetOuter targetLocal) relations).mp
                    targetDenotation)
              exact ⟨sourceLocal,
                (sourcePermutation
                  (ConcreteElaboration.rootEnvironment sourceAmbient
                    sourceLocals sourceOuter sourceLocal) relations).mpr
                  sourcePartitionDenotation⟩

end VisualProof.Rule.VacuousElimTrace
