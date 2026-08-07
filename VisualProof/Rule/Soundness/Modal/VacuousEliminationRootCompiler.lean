import VisualProof.Rule.Soundness.Modal.VacuousEliminationFocusedCompiler
import VisualProof.Rule.Soundness.Modal.VacuousEliminationRootTransport

namespace VisualProof.Concrete.VacuousElimTrace

open VisualProof.Concrete
open VisualProof.Rule

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedRootItems_transport
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed )
    (targetWellFormed : input.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceAmbient sourceLocals :
      Concrete.Elaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : Concrete.Elaboration.WireContext input)
    (freshForward : FreshRelationSelector trace targetWellFormed model)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceBinders : Concrete.Elaboration.BinderContext
      trace.sourceDiagram [])
    (targetBinders : Concrete.Elaboration.BinderContext input [])
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
      Concrete.Elaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input targetBinders
        trace.parent)
    (targetAmbientSubset :
      ∀ wire, wire ∈ targetAmbient → wire ∈ sourceAmbient)
    (sourceAmbientSubset :
      ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
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
    (sourceItems : ItemSeq
      (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq
      (targetAmbient ++ targetLocals).length [])
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrencesWith?
        trace.sourceDiagram
        (Concrete.Elaboration.compileRegion?  trace.sourceDiagram
          fuelSource)
        (sourceAmbient ++ sourceLocals) sourceBinders
        (Concrete.Elaboration.localOccurrences trace.sourceDiagram
          (trace.targetIndex targetWellFormed)) = some sourceItems)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input
        (Concrete.Elaboration.compileRegion?  input fuelTarget)
        (targetAmbient ++ targetLocals) targetBinders
        (Concrete.Elaboration.localOccurrences input trace.parent) =
          some targetItems) :
    Concrete.Elaboration.DirectionalRootTransport direction
      sourceAmbient sourceLocals targetAmbient targetLocals
      (trace.wireIdentityRelation sourceAmbient targetAmbient)
      model  sourceItems targetItems := by
  let sourceRoot := sourceAmbient ++ sourceLocals
  let targetRoot := targetAmbient ++ targetLocals
  let sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin trace.sourceDiagram.regionCount) →
      (wireContext : Concrete.Elaboration.WireContext trace.sourceDiagram) →
      Concrete.Elaboration.BinderContext trace.sourceDiagram rels →
      Option (Region  wireContext.length rels) :=
    fun {rels} => Concrete.Elaboration.compileRegion?
      trace.sourceDiagram fuelSource
  let targetRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (wireContext : Concrete.Elaboration.WireContext input) →
      Concrete.Elaboration.BinderContext input rels →
      Option (Region  wireContext.length rels) :=
    fun {rels} => Concrete.Elaboration.compileRegion?  input fuelTarget
  obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_complete sourceRecurse
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
    Concrete.Elaboration.compileOccurrencesWith?_append_split sourceRecurse
      sourceRoot sourceBinders (trace.keptOccurrences targetWellFormed)
      (trace.selectedOccurrences targetWellFormed) sourcePartitionItems
      sourcePartitionCompiled
  obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_complete targetRecurse
      targetRoot targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap ++
        [Concrete.Elaboration.LocalOccurrence.child bubble])
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          input targetRecurse targetRoot targetBinders targetCompiled
          ((trace.targetFocusOccurrences_perm
            targetWellFormed).mem_iff.mp member))
  obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
      targetBubbleCompiled, targetPartitionEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split targetRecurse
      targetRoot targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap)
      [Concrete.Elaboration.LocalOccurrence.child bubble]
      targetPartitionItems targetPartitionCompiled
  simp only [Concrete.Elaboration.compileOccurrencesWith?] at targetBubbleCompiled
  dsimp only [targetRecurse] at targetBubbleCompiled
  simp only [Concrete.Elaboration.compileOccurrenceWith?, trace.bubble_eq]
    at targetBubbleCompiled
  cases bubbleResult : Concrete.Elaboration.compileRegion?  input
      fuelTarget bubble targetRoot (targetBinders.push bubble trace.arity) with
  | none => simp [bubbleResult] at targetBubbleCompiled
  | some bubbleBody =>
      simp [bubbleResult] at targetBubbleCompiled
      subst targetBubbleItems
      cases fuelTarget with
      | zero => simp [Concrete.Elaboration.compileRegion?] at bubbleResult
      | succ bubbleFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at bubbleResult
          rw [trace.bubble_localOccurrences targetWellFormed] at bubbleResult
          obtain ⟨targetSelectedItems, targetSelectedCompiled,
              bubbleBodyEq⟩ := Option.bind_eq_some_iff.mp bubbleResult
          have bubbleBodyEq' :
              Concrete.Elaboration.finishRegion input targetRoot bubble
                  targetSelectedItems = bubbleBody :=
            Option.some.inj bubbleBodyEq
          subst bubbleBody
          let selectedContext := context.extendRootSelected trace
            targetWellFormed sourceRoot targetRoot sourceExact
          have targetBubbleCover :=
            Concrete.Elaboration.BinderContext.push_covers_bubble_child
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
              Concrete.Elaboration.compileOccurrenceWith?
                  trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
                  occurrence = some sourceItem →
              Concrete.Elaboration.compileOccurrenceWith?  input
                  targetRecurse targetRoot targetBinders
                  (trace.occurrenceMap occurrence) = some targetItem →
              Concrete.Elaboration.ItemSimulation model  direction
                context.indexRelation
                (sourceItem.renameRelations binderWitness.relationMap)
                targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model  direction fuelSource
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
              Concrete.Elaboration.compileOccurrenceWith?
                  trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
                  occurrence = some sourceItem →
              Concrete.Elaboration.compileOccurrenceWith?  input
                  (Concrete.Elaboration.compileRegion?  input
                    bubbleFuel)
                  (targetRoot.extend bubble)
                  (targetBinders.push bubble trace.arity)
                  (trace.occurrenceMap occurrence) = some targetItem →
              Concrete.Elaboration.ItemSimulation model  direction
                selectedContext.indexRelation
                (sourceItem.renameRelations
                  bubbleBinderWitness.relationMap) targetItem := by
            intro occurrence member sourceItem targetItem
              sourceOccurrence targetOccurrence
            apply trace.focusedOccurrence_itemSimulation sourceWellFormed
              targetWellFormed model  direction fuelSource bubbleFuel
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
            Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model  direction sourceRecurse targetRecurse sourceRoot
              targetRoot sourceBinders targetBinders context.indexRelation
              binderWitness.relationMap trace.occurrenceMap
              (trace.keptOccurrences targetWellFormed) keptPointwise
              sourceKeptItems targetKeptItems sourceKeptCompiled
              targetKeptCompiled
          have selectedSimulation :=
            Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model  direction sourceRecurse
              (Concrete.Elaboration.compileRegion?  input bubbleFuel)
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
            targetWellFormed model  direction sourceAmbient sourceLocals
            targetAmbient targetLocals
            (fun sourceEnvironment targetEnvironment sourceRelations
                targetRelations =>
              freshForward sourceRoot targetRoot sourceBinders targetBinders
                sourceExact targetSelectedExact sourceBindersCover
                targetBindersCover sourceEnumeration targetEnumeration
                binderWitness sourceEnvironment targetEnvironment
                sourceRelations targetRelations)
            context sourceExact
            targetSelectedExact.nodup targetAmbientSubset sourceAmbientSubset
            bubbleBinderWitness.relationMap sourceKeptItems sourceSelectedItems
            targetKeptItems targetSelectedItems keptSimulation
            selectedSimulation
          rw [← sourcePartitionEq, ← targetPartitionEq] at partitionTransport
          have sourcePermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              trace.sourceDiagram sourceRecurse sourceRoot sourceBinders
              (trace.focusOccurrences_perm_partition targetWellFormed).symm
              sourceCompiled sourcePartitionCompiled model
          have targetPermutation :=
            VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
              input targetRecurse targetRoot targetBinders
              (trace.targetFocusOccurrences_perm targetWellFormed).symm
              targetCompiled targetPartitionCompiled model
          intro sourceOuter targetOuter relations agreement
          cases direction with
          | forward =>
              intro sourceLocal sourceDenotation
              obtain ⟨targetLocal, targetPartitionDenotation⟩ :=
                partitionTransport sourceOuter targetOuter relations agreement
                  sourceLocal
                  ((sourcePermutation
                    (Concrete.Elaboration.rootEnvironment sourceAmbient
                      sourceLocals sourceOuter sourceLocal) relations).mp
                    sourceDenotation)
              exact ⟨targetLocal,
                (targetPermutation
                  (Concrete.Elaboration.rootEnvironment targetAmbient
                    targetLocals targetOuter targetLocal) relations).mpr
                  targetPartitionDenotation⟩
          | backward =>
              intro targetLocal targetDenotation
              obtain ⟨sourceLocal, sourcePartitionDenotation⟩ :=
                partitionTransport sourceOuter targetOuter relations agreement
                  targetLocal
                  ((targetPermutation
                    (Concrete.Elaboration.rootEnvironment targetAmbient
                      targetLocals targetOuter targetLocal) relations).mp
                    targetDenotation)
              exact ⟨sourceLocal,
                (sourcePermutation
                  (Concrete.Elaboration.rootEnvironment sourceAmbient
                    sourceLocals sourceOuter sourceLocal) relations).mpr
                  sourcePartitionDenotation⟩

end VisualProof.Concrete.VacuousElimTrace
