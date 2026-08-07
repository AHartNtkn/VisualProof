import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedRegionCompiler
import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Every surviving region below the fresh abstraction bubble is simulated
under the fixed comprehension relation.  Occurrence anchors may appear at
either cut polarity; all other material follows the survivor compiler map. -/
theorem fixedRegionSimulation
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed )
    (model : Model)
    :
    ∀ (direction : Concrete.Elaboration.SimulationDirection)
      (sourceFuel targetFuel : Nat)
      (region : Fin input.val.regionCount),
      trace.domains.regions.survives region = true →
      region ≠ wrap.val.anchor →
      region ∈ wrap.selectedRegions →
      AbstractionAllowed input.val wrap.val.anchor direction region →
      FixedRegionSimulation trace model  direction sourceFuel targetFuel
        region := by
  intro direction sourceFuel
  induction sourceFuel generalizing direction with
  | zero =>
      intro targetFuel region regionSurvives notWrap regionSelected allowed
      unfold FixedRegionSimulation
      intro sourceRels targetRels sourceContext targetContext context
        sourceNodup sourceBinders targetBinders binderWitness sourceCover
        targetCover sourceEnumeration targetEnumeration sourceExact targetExact
        sourceBody targetBody sourceCompiled
      simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ sourceFuel induction =>
      intro targetFuel
      cases targetFuel with
      | zero =>
          intro region regionSurvives notWrap regionSelected allowed
          unfold FixedRegionSimulation
          intro sourceRels targetRels sourceContext targetContext context
            sourceNodup sourceBinders targetBinders binderWitness sourceCover
            targetCover sourceEnumeration targetEnumeration sourceExact
            targetExact sourceBody targetBody sourceCompiled targetCompiled
          simp [Concrete.Elaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          intro region regionSurvives notWrap regionSelected allowed
          unfold FixedRegionSimulation
          intro sourceRels targetRels sourceContext targetContext context
            sourceNodup sourceBinders targetBinders binderWitness sourceCover
            targetCover sourceEnumeration targetEnumeration sourceExact
            targetExact sourceBody targetBody sourceCompiled targetCompiled
          simp only [Concrete.Elaboration.compileRegion?]
            at sourceCompiled targetCompiled
          let sourceExtended := sourceContext.extend region
          let targetExtended := targetContext.extend (trace.regionMap region)
          cases sourceItemsResult : Concrete.Elaboration.compileOccurrencesWith?
               input.val
              (Concrete.Elaboration.compileRegion?  input.val sourceFuel)
              sourceExtended sourceBinders
              (Concrete.Elaboration.localOccurrences input.val region) with
          | none =>
              simp [sourceExtended, sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceExtended, sourceItemsResult] at sourceCompiled
              subst sourceBody
              cases targetItemsResult :
                  Concrete.Elaboration.compileOccurrencesWith?
                    trace.diagram
                    (Concrete.Elaboration.compileRegion?  trace.diagram
                      targetFuel)
                    targetExtended targetBinders
                    (Concrete.Elaboration.localOccurrences trace.diagram
                      (trace.regionMap region)) with
              | none =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
              | some targetItems =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
                  subst targetBody
                  let sourceRecurse : ∀ {rels : RelCtx},
                      (child : Fin input.val.regionCount) →
                      (childContext : Concrete.Elaboration.WireContext input.val) →
                      Concrete.Elaboration.BinderContext input.val rels →
                      Option (Region  childContext.length rels) :=
                    fun {rels} => Concrete.Elaboration.compileRegion?
                      input.val sourceFuel
                  let targetRecurse : ∀ {rels : RelCtx},
                      (child : Fin trace.diagram.regionCount) →
                      (childContext : Concrete.Elaboration.WireContext
                        trace.diagram) →
                      Concrete.Elaboration.BinderContext trace.diagram rels →
                      Option (Region  childContext.length rels) :=
                    fun {rels} => Concrete.Elaboration.compileRegion?
                      trace.diagram targetFuel
                  let sourceSurvivors := trace.survivingSources
                    (Concrete.Elaboration.localOccurrences input.val region)
                  let indices := anchorIndices occurrences region
                  let sourceSelected := selectedAt input occurrences region
                  let targetSurvivors :=
                    sourceSurvivors.map trace.survivorOccurrence
                  let targetAtoms : List (Concrete.Elaboration.LocalOccurrence
                      trace.diagram.regionCount trace.diagram.nodeCount) :=
                    indices.map fun index =>
                      Concrete.Elaboration.LocalOccurrence.node
                        (trace.targetAtom index)
                  have sourcePartition :
                      (sourceSurvivors ++ sourceSelected).Perm
                        (Concrete.Elaboration.localOccurrences input.val region) :=
                    trace.localOccurrences_perm_focusedPartition payload region
                      regionSurvives
                  have targetPartition :
                      (Concrete.Elaboration.localOccurrences trace.diagram
                          (trace.regionMap region)).Perm
                        (targetSurvivors ++ targetAtoms) := by
                    rw [trace.regionMap_of_survives region regionSurvives]
                    have rawPartition := trace.targetLocalOccurrences_nonwrap
                      payload region regionSurvives notWrap
                    simpa [sourceSurvivors, targetSurvivors, targetAtoms,
                      indices, atomsAt, anchorIndices,
                      trace.survivingSources_map_survivor] using rawPartition
                  obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_complete
                      sourceRecurse sourceExtended sourceBinders
                      (sourceSurvivors ++ sourceSelected) (by
                        intro occurrence member
                        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
                          input.val sourceRecurse sourceExtended sourceBinders
                          sourceItemsResult
                          ((sourcePartition.mem_iff).1 member))
                  obtain ⟨sourceSurvivorItems, sourceSelectedItems,
                      sourceSurvivorCompiled, sourceSelectedCompiled,
                      sourcePartitionEq⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_append_split
                      sourceRecurse sourceExtended sourceBinders sourceSurvivors
                      sourceSelected sourcePartitionItems sourcePartitionCompiled
                  obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_complete
                      targetRecurse targetExtended targetBinders
                      (targetSurvivors ++ targetAtoms) (by
                        intro occurrence member
                        exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
                          trace.diagram targetRecurse targetExtended targetBinders
                          targetItemsResult
                          ((targetPartition.mem_iff).2 member))
                  obtain ⟨targetSurvivorItems, targetAtomItems,
                      targetSurvivorCompiled, targetAtomCompiled,
                      targetPartitionEq⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_append_split
                      targetRecurse targetExtended targetBinders targetSurvivors
                      targetAtoms targetPartitionItems targetPartitionCompiled
                  have sourceBlockExists : ∀ index, index ∈ indices →
                      ∃ items : ItemSeq  sourceExtended.length
                          sourceRels,
                        Concrete.Elaboration.compileOccurrencesWith?
                          input.val sourceRecurse sourceExtended sourceBinders
                          (VisualProof.Rule.ModalSoundness.selectedOccurrences input.val
                            (occurrences.get index).selection) = some items := by
                    intro index indexMember
                    apply Concrete.Elaboration.compileOccurrencesWith?_complete
                    intro occurrence occurrenceMember
                    apply VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
                      input.val sourceRecurse sourceExtended sourceBinders
                      sourceSelectedCompiled
                    exact (mem_selectedAt input occurrences region occurrence).2
                      ⟨index, (mem_anchorIndices occurrences region index).1
                        indexMember, occurrenceMember⟩
                  let sourceFamilyItems : Fin occurrences.length →
                      ItemSeq  sourceExtended.length sourceRels :=
                    fun index => if member : index ∈ indices then
                      Classical.choose (sourceBlockExists index member)
                    else .nil
                  have sourceFamilyCompiled : ∀ index, index ∈ indices →
                      Concrete.Elaboration.compileOccurrencesWith?
                        input.val sourceRecurse sourceExtended sourceBinders
                        (VisualProof.Rule.ModalSoundness.selectedOccurrences input.val
                          (occurrences.get index).selection) =
                            some (sourceFamilyItems index) := by
                    intro index member
                    dsimp only [sourceFamilyItems]
                    rw [dif_pos member]
                    exact Classical.choose_spec (sourceBlockExists index member)
                  have sourceFamilyAggregateCompiled :=
                    compileOccurrenceFamilyItems sourceRecurse sourceExtended
                      sourceBinders indices
                      (fun index => VisualProof.Rule.ModalSoundness.selectedOccurrences input.val
                        (occurrences.get index).selection)
                      sourceFamilyItems sourceFamilyCompiled
                  have sourceFamilyEq :
                      occurrenceFamilyItems sourceFamilyItems indices =
                        sourceSelectedItems := by
                    apply Option.some.inj
                    exact sourceFamilyAggregateCompiled.symm.trans (by
                      simpa [sourceSelected, selectedAt, indices] using
                        sourceSelectedCompiled)
                  have targetAtomExists : ∀ index, index ∈ indices →
                      ∃ item : Item  targetExtended.length targetRels,
                        Concrete.Elaboration.compileNode?  trace.diagram
                          targetExtended targetBinders (trace.targetAtom index) =
                            some item := by
                    intro index indexMember
                    obtain ⟨item, compiled⟩ :=
                      VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
                        trace.diagram targetRecurse targetExtended targetBinders
                        targetAtomCompiled (by
                          exact List.mem_map.mpr ⟨index, indexMember, rfl⟩)
                    exact ⟨item, by
                      simpa [Concrete.Elaboration.compileOccurrenceWith?] using
                        compiled⟩
                  let targetFamilyItems : Fin occurrences.length →
                      Item  targetExtended.length targetRels :=
                    fun index => if member : index ∈ indices then
                      Classical.choose (targetAtomExists index member)
                    else .cut (.mk 0 .nil)
                  have targetFamilyCompiled : ∀ index, index ∈ indices →
                      Concrete.Elaboration.compileNode?  trace.diagram
                        targetExtended targetBinders (trace.targetAtom index) =
                          some (targetFamilyItems index) := by
                    intro index member
                    dsimp only [targetFamilyItems]
                    rw [dif_pos member]
                    exact Classical.choose_spec (targetAtomExists index member)
                  have targetFamilyAggregateCompiled :=
                    compileOccurrenceFamilyAtomItems targetRecurse targetExtended
                      targetBinders indices
                      (fun index => Concrete.Elaboration.LocalOccurrence.node
                        (trace.targetAtom index))
                      targetFamilyItems (by
                        intro index member
                        simpa [Concrete.Elaboration.compileOccurrenceWith?] using
                          targetFamilyCompiled index member)
                  have targetFamilyEq :
                      occurrenceFamilyAtomItems targetFamilyItems indices =
                        targetAtomItems := by
                    apply Option.some.inj
                    exact targetFamilyAggregateCompiled.symm.trans (by
                      simpa [targetAtoms] using targetAtomCompiled)
                  have sourceCanonicalCompiled :
                      Concrete.Elaboration.compileOccurrencesWith?
                        input.val sourceRecurse sourceExtended sourceBinders
                        (sourceSurvivors ++ sourceSelected) =
                          some (sourceSurvivorItems.append sourceSelectedItems) := by
                    rw [← sourcePartitionEq]
                    exact sourcePartitionCompiled
                  have targetCanonicalCompiled :
                      Concrete.Elaboration.compileOccurrencesWith?
                        trace.diagram targetRecurse targetExtended targetBinders
                        (targetSurvivors ++ targetAtoms) =
                          some (targetSurvivorItems.append targetAtomItems) := by
                    rw [← targetPartitionEq]
                    exact targetPartitionCompiled
                  have sourceCanonicalNodup :
                      (sourceSurvivors ++ sourceSelected).Nodup :=
                    (sourcePartition.nodup_iff).2
                      (Concrete.Elaboration.localOccurrences_nodup input.val
                        region)
                  have targetCanonicalNodup :
                      (targetSurvivors ++ targetAtoms).Nodup :=
                    (targetPartition.nodup_iff).1
                      (Concrete.Elaboration.localOccurrences_nodup trace.diagram
                        (trace.regionMap region))
                  have survivorMembers : ∀ occurrence,
                      occurrence ∈ sourceSurvivors → occurrence ∈
                        Concrete.Elaboration.localOccurrences input.val region := by
                    intro occurrence member
                    exact (mem_survivingSources trace
                      (Concrete.Elaboration.localOccurrences input.val region)
                      occurrence).1 member |>.1
                  have survivorMaps : ∀ occurrence,
                      occurrence ∈ sourceSurvivors →
                        ∃ target,
                          trace.survivingOccurrence? occurrence = some target := by
                    intro occurrence member
                    exact Option.isSome_iff_exists.mp
                      ((mem_survivingSources trace
                        (Concrete.Elaboration.localOccurrences input.val region)
                        occurrence).1 member |>.2)
                  have recurseAt : ∀
                      (childDirection : Concrete.Elaboration.SimulationDirection)
                      (child : Fin input.val.regionCount),
                      child ∈ wrap.selectedRegions →
                      trace.domains.regions.survives child = true →
                      child ≠ wrap.val.anchor →
                      AbstractionAllowed input.val wrap.val.anchor
                        childDirection child →
                      FixedRegionSimulation trace model  childDirection
                        sourceFuel targetFuel child := by
                    intro childDirection child childSelected childSurvives
                      childNotWrap childAllowed
                    exact induction childDirection targetFuel child childSurvives
                      childNotWrap childSelected childAllowed
                  have survivorSemantic :=
                    trace.focusedSurvivingSources_semantic targetWellFormed model
                       direction sourceFuel targetFuel region regionSurvives
                      notWrap regionSelected sourceExtended targetExtended
                      (context.extend region regionSurvives) sourceBinders
                      targetBinders binderWitness sourceExact targetExact
                      sourceCover targetCover sourceEnumeration targetEnumeration
                      allowed recurseAt sourceSurvivors survivorMembers
                      survivorMaps sourceSurvivorItems targetSurvivorItems
                      sourceSurvivorCompiled (by
                        simpa [targetSurvivors] using targetSurvivorCompiled)
                  letI : Nonempty model.Carrier := model.nonempty
                  intro sourceEnvironment targetEnvironment targetRelations
                    environments fixed
                  rw [Concrete.Elaboration.finishRegion_renameRelations]
                  let sourceRelations := RelEnv.pullback
                    binderWitness.relationMap targetRelations
                  have relationAgreement := RelEnv.pullback_agrees
                    binderWitness.relationMap targetRelations
                  have anchored : ∀ index, index ∈ indices →
                      (occurrences.get index).selection.val.anchor = region := by
                    intro index member
                    exact (mem_anchorIndices occurrences region index).1 member
                  cases direction with
                  | forward =>
                      intro sourceDenotes
                      obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                        (DoubleCutElimTrace.finishRegion_denote_iff input.val
                          sourceContext region
                          (sourceItems.renameRelations binderWitness.relationMap)
                          model  sourceEnvironment targetRelations).1
                            sourceDenotes
                      obtain ⟨targetLocal, extendedAgreement⟩ :=
                        trace.survivorEnvironmentSelection targetWellFormed
                          .forward sourceContext targetContext context region
                          regionSurvives sourceExact sourceEnvironment
                          targetEnvironment environments sourceLocal
                      let sourceLocalEnvironment :=
                        Concrete.Elaboration.extendedEnvironment sourceContext
                          region sourceEnvironment sourceLocal
                      let targetLocalEnvironment :=
                        Concrete.Elaboration.extendedEnvironment targetContext
                          (trace.regionMap region) targetEnvironment targetLocal
                      have sourceRawDenote : denoteItemSeq model
                          sourceLocalEnvironment sourceRelations sourceItems :=
                        (denoteItemSeq_renameRelations model
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          sourceLocalEnvironment sourceItems).1 sourceItemsDenote
                      have sourcePermutation :=
                        compileOccurrences_perm_denote_iff input.val
                          sourceRecurse sourceExtended sourceBinders
                          sourcePartition sourceCanonicalNodup
                          (Concrete.Elaboration.localOccurrences_nodup input.val
                            region)
                          sourceCanonicalCompiled sourceItemsResult model
                          sourceLocalEnvironment sourceRelations
                      have sourceCanonicalDenote :=
                        sourcePermutation.mpr sourceRawDenote
                      have sourceParts :=
                        (denoteItemSeq_append model  sourceLocalEnvironment
                          sourceRelations sourceSurvivorItems
                          sourceSelectedItems).1 sourceCanonicalDenote
                      have sourceSurvivorRenamed : denoteItemSeq model
                          sourceLocalEnvironment targetRelations
                          (sourceSurvivorItems.renameRelations
                            binderWitness.relationMap) :=
                        (denoteItemSeq_renameRelations model
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          sourceLocalEnvironment sourceSurvivorItems).2
                            sourceParts.1
                      have targetSurvivorDenote := survivorSemantic
                        sourceLocalEnvironment targetLocalEnvironment
                        targetRelations extendedAgreement fixed
                        sourceSurvivorRenamed
                      have sourceFamilyDenote : denoteItemSeq model
                          sourceLocalEnvironment sourceRelations
                          (occurrenceFamilyItems sourceFamilyItems indices) := by
                        rw [sourceFamilyEq]
                        exact sourceParts.2
                      have targetFamilyDenote := trace.occurrenceFamily_forward
                        payload model  sourceFuel region indices anchored
                        sourceExtended targetExtended
                        (context.extend region regionSurvives) sourceBinders
                        targetBinders sourceCover sourceEnumeration sourceExact
                        sourceFamilyItems targetFamilyItems sourceFamilyCompiled
                        targetFamilyCompiled sourceLocalEnvironment
                        targetLocalEnvironment sourceRelations targetRelations
                        fixed extendedAgreement sourceFamilyDenote
                      have targetCanonicalDenote : denoteItemSeq model
                          targetLocalEnvironment targetRelations
                          (targetSurvivorItems.append targetAtomItems) := by
                        apply (denoteItemSeq_append model
                          targetLocalEnvironment targetRelations
                          targetSurvivorItems targetAtomItems).2
                        refine ⟨targetSurvivorDenote, ?_⟩
                        rw [← targetFamilyEq]
                        exact targetFamilyDenote
                      have targetPermutation :=
                        compileOccurrences_perm_denote_iff trace.diagram
                          targetRecurse targetExtended targetBinders
                          targetPartition
                          (Concrete.Elaboration.localOccurrences_nodup
                            trace.diagram (trace.regionMap region))
                          targetCanonicalNodup targetItemsResult
                          targetCanonicalCompiled model
                          targetLocalEnvironment targetRelations
                      have targetItemsDenote :=
                        targetPermutation.mpr targetCanonicalDenote
                      apply (DoubleCutElimTrace.finishRegion_denote_iff
                        trace.diagram targetContext (trace.regionMap region)
                        targetItems model  targetEnvironment
                        targetRelations).2
                      exact ⟨targetLocal, targetItemsDenote⟩
                  | backward =>
                      intro targetDenotes
                      obtain ⟨targetLocal, targetItemsDenote⟩ :=
                        (DoubleCutElimTrace.finishRegion_denote_iff trace.diagram
                          targetContext (trace.regionMap region) targetItems model
                           targetEnvironment targetRelations).1 targetDenotes
                      let targetLocalEnvironment :=
                        Concrete.Elaboration.extendedEnvironment targetContext
                          (trace.regionMap region) targetEnvironment targetLocal
                      have targetPermutation :=
                        compileOccurrences_perm_denote_iff trace.diagram
                          targetRecurse targetExtended targetBinders
                          targetPartition
                          (Concrete.Elaboration.localOccurrences_nodup
                            trace.diagram (trace.regionMap region))
                          targetCanonicalNodup targetItemsResult
                          targetCanonicalCompiled model
                          targetLocalEnvironment targetRelations
                      have targetCanonicalDenote :=
                        targetPermutation.mp targetItemsDenote
                      have targetParts :=
                        (denoteItemSeq_append model  targetLocalEnvironment
                          targetRelations targetSurvivorItems targetAtomItems).1
                            targetCanonicalDenote
                      obtain ⟨baseSourceLocal, baseAgreement⟩ :=
                        trace.survivorEnvironmentSelection targetWellFormed
                          .backward sourceContext targetContext context region
                          regionSurvives sourceExact sourceEnvironment
                          targetEnvironment environments targetLocal
                      let baseSourceEnvironment :=
                        Concrete.Elaboration.extendedEnvironment sourceContext
                          region sourceEnvironment baseSourceLocal
                      have targetFamilyDenote : denoteItemSeq model
                          targetLocalEnvironment targetRelations
                          (occurrenceFamilyAtomItems targetFamilyItems indices) := by
                        rw [targetFamilyEq]
                        exact targetParts.2
                      obtain ⟨chosenSourceEnvironment, chosenAgreement,
                          sourceFamilyDenote, sourcePreserves⟩ :=
                        trace.occurrenceFamily_backward payload model
                          sourceFuel region indices anchored sourceExtended
                          targetExtended (context.extend region regionSurvives)
                          sourceBinders targetBinders sourceCover
                          sourceEnumeration sourceExact sourceFamilyItems
                          targetFamilyItems sourceFamilyCompiled
                          targetFamilyCompiled baseSourceEnvironment
                          targetLocalEnvironment sourceRelations targetRelations
                          fixed baseAgreement targetFamilyDenote
                      have sourceSurvivorRenamed := survivorSemantic
                        chosenSourceEnvironment targetLocalEnvironment
                        targetRelations chosenAgreement fixed targetParts.1
                      have sourceSurvivorRaw : denoteItemSeq model
                          chosenSourceEnvironment sourceRelations
                          sourceSurvivorItems :=
                        (denoteItemSeq_renameRelations model
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          chosenSourceEnvironment sourceSurvivorItems).1
                            sourceSurvivorRenamed
                      have sourceCanonicalDenote : denoteItemSeq model
                          chosenSourceEnvironment sourceRelations
                          (sourceSurvivorItems.append sourceSelectedItems) := by
                        apply (denoteItemSeq_append model
                          chosenSourceEnvironment sourceRelations
                          sourceSurvivorItems sourceSelectedItems).2
                        refine ⟨sourceSurvivorRaw, ?_⟩
                        rw [← sourceFamilyEq]
                        exact sourceFamilyDenote
                      have sourcePermutation :=
                        compileOccurrences_perm_denote_iff input.val
                          sourceRecurse sourceExtended sourceBinders
                          sourcePartition sourceCanonicalNodup
                          (Concrete.Elaboration.localOccurrences_nodup input.val
                            region)
                          sourceCanonicalCompiled sourceItemsResult model
                          chosenSourceEnvironment sourceRelations
                      have sourceRawDenote :=
                        sourcePermutation.mp sourceCanonicalDenote
                      have sourceRenamedDenote : denoteItemSeq model
                          chosenSourceEnvironment targetRelations
                          (sourceItems.renameRelations
                            binderWitness.relationMap) :=
                        (denoteItemSeq_renameRelations model
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          chosenSourceEnvironment sourceItems).2 sourceRawDenote
                      let chosenSourceLocal := localEnvironmentPart sourceContext
                        region chosenSourceEnvironment
                      have chosenOuterValues : ∀ index,
                          chosenSourceEnvironment
                              (extendedOuterIndex sourceContext region index) =
                            sourceEnvironment index := by
                        intro outerIndex
                        calc
                          chosenSourceEnvironment
                              (extendedOuterIndex sourceContext region
                                outerIndex) =
                              baseSourceEnvironment
                                (extendedOuterIndex sourceContext region
                                  outerIndex) := sourcePreserves _ (by
                                    intro occurrenceIndex occurrenceMember
                                    have anchorEq := anchored occurrenceIndex
                                      occurrenceMember
                                    have outside :=
                                      extendedOuter_not_occurrenceInternal input
                                        (occurrences.get occurrenceIndex).selection
                                        sourceContext (by
                                          rw [anchorEq]
                                          exact sourceExact)
                                        outerIndex
                                    simpa only [sourceExtended,
                                      extendedOuterIndex_get] using outside)
                          _ = sourceEnvironment outerIndex := by
                            simp [baseSourceEnvironment]
                      have chosenEnvironmentEq := extendedEnvironment_of_parts
                        sourceContext region sourceEnvironment
                        chosenSourceEnvironment chosenOuterValues
                      apply (DoubleCutElimTrace.finishRegion_denote_iff input.val
                        sourceContext region
                        (sourceItems.renameRelations binderWitness.relationMap)
                        model  sourceEnvironment targetRelations).2
                      refine ⟨chosenSourceLocal, ?_⟩
                      rw [chosenEnvironmentEq]
                      exact sourceRenamedDenote

end AbstractionRawTrace

end VisualProof.Concrete
