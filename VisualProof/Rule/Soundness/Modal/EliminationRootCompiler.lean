import VisualProof.Rule.Soundness.Modal.EliminationFocusedCompiler
import VisualProof.Rule.Soundness.Modal.EliminationRootTransport

namespace VisualProof.Concrete.DoubleCutElimTrace

open VisualProof.Concrete
open VisualProof.Rule

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedRootItems_transport
    (trace : DoubleCutElimTrace input outer raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed )
    (targetWellFormed : input.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceAmbient sourceLocals :
      Concrete.Elaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : Concrete.Elaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceBinders : Concrete.Elaboration.BinderContext
      trace.sourceDiagram [])
    (targetBinders : Concrete.Elaboration.BinderContext input [])
    (binderWitness : PromotedBinderWitness trace sourceBinders targetBinders)
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact
        (trace.targetIndex targetWellFormed))
    (targetExact :
      (targetAmbient ++ targetLocals).Exact trace.target)
    (sourceBindersCover :
      sourceBinders.Covers (trace.targetIndex targetWellFormed))
    (targetBindersCover : targetBinders.Covers trace.target)
    (sourceEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration trace.sourceDiagram
        sourceBinders (trace.targetIndex targetWellFormed))
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input targetBinders
        trace.target)
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
      (childBinderWitness : PromotedBinderWitness trace childSourceBinders
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
        (Concrete.Elaboration.localOccurrences input trace.target) =
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
        [Concrete.Elaboration.LocalOccurrence.child outer])
      (by
        intro occurrence member
        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
          input targetRecurse targetRoot targetBinders targetCompiled
          ((trace.targetFocusOccurrences_perm
            targetWellFormed).mem_iff.mp member))
  obtain ⟨targetKeptItems, targetOuterItems, targetKeptCompiled,
      targetOuterCompiled, targetPartitionEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split targetRecurse
      targetRoot targetBinders
      ((trace.keptOccurrences targetWellFormed).map trace.occurrenceMap)
      [Concrete.Elaboration.LocalOccurrence.child outer]
      targetPartitionItems targetPartitionCompiled
  simp only [Concrete.Elaboration.compileOccurrencesWith?] at targetOuterCompiled
  dsimp only [targetRecurse] at targetOuterCompiled
  simp only [Concrete.Elaboration.compileOccurrenceWith?, trace.outer_eq]
    at targetOuterCompiled
  cases outerResult : Concrete.Elaboration.compileRegion?  input
      fuelTarget outer targetRoot targetBinders with
  | none => simp [outerResult] at targetOuterCompiled
  | some outerBody =>
      simp [outerResult] at targetOuterCompiled
      subst targetOuterItems
      cases fuelTarget with
      | zero =>
          simp [Concrete.Elaboration.compileRegion?] at outerResult
      | succ outerFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at outerResult
          rw [trace.outer_localOccurrences] at outerResult
          obtain ⟨outerItems, outerItemsCompiled, outerBodyEq⟩ :=
            Option.bind_eq_some_iff.mp outerResult
          have outerBodyEq' :
              Concrete.Elaboration.finishRegion input targetRoot outer
                  outerItems = outerBody := Option.some.inj outerBodyEq
          subst outerBody
          simp only [Concrete.Elaboration.compileOccurrencesWith?]
            at outerItemsCompiled
          simp only [Concrete.Elaboration.compileOccurrenceWith?, trace.inner_eq]
            at outerItemsCompiled
          cases innerResult : Concrete.Elaboration.compileRegion?  input
              outerFuel trace.inner (targetRoot.extend outer) targetBinders with
          | none => simp [innerResult] at outerItemsCompiled
          | some innerBody =>
              simp [innerResult] at outerItemsCompiled
              subst outerItems
              cases outerFuel with
              | zero =>
                  simp [Concrete.Elaboration.compileRegion?] at innerResult
              | succ innerFuel =>
                  simp only [Concrete.Elaboration.compileRegion?] at innerResult
                  rw [trace.inner_localOccurrences targetWellFormed]
                    at innerResult
                  obtain ⟨targetSelectedItems, targetSelectedCompiled,
                      innerBodyEq⟩ := Option.bind_eq_some_iff.mp innerResult
                  have innerBodyEq' :
                      Concrete.Elaboration.finishRegion input
                          (targetRoot.extend outer) trace.inner
                          targetSelectedItems = innerBody :=
                    Option.some.inj innerBodyEq
                  subst innerBody
                  let selectedContext := context.extendRootSelected trace
                    targetWellFormed sourceRoot targetRoot sourceExact
                  have targetOuterCover :=
                    Concrete.Elaboration.BinderContext.covers_cut_child
                      targetBindersCover trace.outer_eq
                  have targetInnerCover :=
                    Concrete.Elaboration.BinderContext.covers_cut_child
                      targetOuterCover trace.inner_eq
                  have targetOuterEnumeration :=
                    targetEnumeration.cutChild targetWellFormed trace.outer_eq
                  have targetInnerEnumeration :=
                    targetOuterEnumeration.cutChild targetWellFormed
                      trace.inner_eq
                  have targetSelectedExact :=
                    trace.targetRootSelected_exact targetWellFormed targetRoot
                      targetExact
                  have keptPointwise : ∀ occurrence,
                      occurrence ∈ trace.keptOccurrences targetWellFormed →
                      ∀ sourceItem targetItem,
                      Concrete.Elaboration.compileOccurrenceWith?
                          trace.sourceDiagram sourceRecurse sourceRoot
                          sourceBinders occurrence = some sourceItem →
                      Concrete.Elaboration.compileOccurrenceWith?  input
                          targetRecurse targetRoot targetBinders
                          (trace.occurrenceMap occurrence) = some targetItem →
                      Concrete.Elaboration.ItemSimulation model  direction
                        context.indexRelation
                        (sourceItem.renameRelations binderWitness.relationMap)
                        targetItem := by
                    intro occurrence member sourceItem targetItem
                      sourceOccurrence targetOccurrence
                    apply trace.focusedOccurrence_itemSimulation
                      sourceWellFormed targetWellFormed model  direction
                      fuelSource (innerFuel + 1 + 1) trace.target sourceRoot
                      targetRoot context sourceBinders targetBinders
                      binderWitness sourceExact targetExact sourceBindersCover
                      targetBindersCover sourceEnumeration targetEnumeration
                      occurrence
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
                      Concrete.Elaboration.compileOccurrenceWith?
                          trace.sourceDiagram sourceRecurse sourceRoot
                          sourceBinders occurrence = some sourceItem →
                      Concrete.Elaboration.compileOccurrenceWith?  input
                          (Concrete.Elaboration.compileRegion?  input
                            innerFuel)
                          ((targetRoot.extend outer).extend trace.inner)
                          targetBinders (trace.occurrenceMap occurrence) =
                            some targetItem →
                      Concrete.Elaboration.ItemSimulation model  direction
                        selectedContext.indexRelation
                        (sourceItem.renameRelations binderWitness.relationMap)
                        targetItem := by
                    intro occurrence member sourceItem targetItem
                      sourceOccurrence targetOccurrence
                    apply trace.focusedOccurrence_itemSimulation
                      sourceWellFormed targetWellFormed model  direction
                      fuelSource innerFuel trace.inner sourceRoot
                      ((targetRoot.extend outer).extend trace.inner)
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
                    Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model  direction sourceRecurse targetRecurse
                      sourceRoot targetRoot sourceBinders targetBinders
                      context.indexRelation binderWitness.relationMap
                      trace.occurrenceMap
                      (trace.keptOccurrences targetWellFormed) keptPointwise
                      sourceKeptItems targetKeptItems sourceKeptCompiled
                      targetKeptCompiled
                  have selectedSimulation :=
                    Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model  direction sourceRecurse
                      (Concrete.Elaboration.compileRegion?  input
                        innerFuel)
                      sourceRoot
                      ((targetRoot.extend outer).extend trace.inner)
                      sourceBinders targetBinders selectedContext.indexRelation
                      binderWitness.relationMap trace.occurrenceMap
                      (trace.selectedOccurrences targetWellFormed)
                      selectedPointwise sourceSelectedItems targetSelectedItems
                      sourceSelectedCompiled targetSelectedCompiled
                  have relationMapEq :
                      (binderWitness.relationMap : RelationRenaming [] []) =
                        (fun {arity} (relation : RelVar [] arity) =>
                          relation) := rfl
                  rw [relationMapEq, ItemSeq.renameRelations_id]
                    at keptSimulation selectedSimulation
                  have partitionTransport :=
                    trace.focusedRootPartition_transport targetWellFormed model
                       direction sourceAmbient sourceLocals targetAmbient
                      targetLocals context sourceExact targetSelectedExact.nodup
                      targetAmbientSubset sourceAmbientSubset sourceKeptItems
                      sourceSelectedItems targetKeptItems targetSelectedItems
                      keptSimulation selectedSimulation
                  rw [← sourcePartitionEq, ← targetPartitionEq]
                    at partitionTransport
                  intro sourceOuter targetOuter relations agreement
                  cases direction with
                  | forward =>
                      intro sourceLocal sourceDenotation
                      obtain ⟨targetLocal, targetPartitionDenotation⟩ :=
                        partitionTransport sourceOuter targetOuter relations
                          agreement sourceLocal
                          ((VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                            trace.sourceDiagram sourceRecurse sourceRoot
                            sourceBinders
                            (trace.focusOccurrences_perm_partition
                              targetWellFormed).symm
                            sourceCompiled sourcePartitionCompiled model
                            (Concrete.Elaboration.rootEnvironment sourceAmbient
                              sourceLocals sourceOuter sourceLocal)
                            relations).mp sourceDenotation)
                      exact ⟨targetLocal,
                        (VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                          input targetRecurse targetRoot targetBinders
                          (trace.targetFocusOccurrences_perm
                            targetWellFormed).symm
                          targetCompiled targetPartitionCompiled model
                          (Concrete.Elaboration.rootEnvironment targetAmbient
                            targetLocals targetOuter targetLocal)
                          relations).mpr targetPartitionDenotation⟩
                  | backward =>
                      intro targetLocal targetDenotation
                      obtain ⟨sourceLocal, sourcePartitionDenotation⟩ :=
                        partitionTransport sourceOuter targetOuter relations
                          agreement targetLocal
                          ((VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                            input targetRecurse targetRoot targetBinders
                            (trace.targetFocusOccurrences_perm
                              targetWellFormed).symm
                            targetCompiled targetPartitionCompiled model
                            (Concrete.Elaboration.rootEnvironment targetAmbient
                              targetLocals targetOuter targetLocal)
                            relations).mp targetDenotation)
                      exact ⟨sourceLocal,
                        (VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                          trace.sourceDiagram sourceRecurse sourceRoot
                          sourceBinders
                          (trace.focusOccurrences_perm_partition
                            targetWellFormed).symm
                          sourceCompiled sourcePartitionCompiled model
                          (Concrete.Elaboration.rootEnvironment sourceAmbient
                            sourceLocals sourceOuter sourceLocal)
                          relations).mpr sourcePartitionDenotation⟩

end VisualProof.Concrete.DoubleCutElimTrace
