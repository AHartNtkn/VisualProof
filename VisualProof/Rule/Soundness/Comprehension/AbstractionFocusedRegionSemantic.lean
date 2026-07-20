import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedRegionCompiler
import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Every surviving region below the fresh abstraction bubble is simulated
under the fixed comprehension relation.  Occurrence anchors may appear at
either cut polarity; all other material follows the survivor compiler map. -/
theorem fixedRegionSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ∀ (direction : ConcreteElaboration.SimulationDirection)
      (sourceFuel targetFuel : Nat)
      (region : Fin input.val.regionCount),
      trace.domains.regions.survives region = true →
      region ≠ wrap.val.anchor →
      region ∈ wrap.selectedRegions →
      AbstractionAllowed input.val wrap.val.anchor direction region →
      FixedRegionSimulation trace model named direction sourceFuel targetFuel
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
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
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
          simp [ConcreteElaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          intro region regionSurvives notWrap regionSelected allowed
          unfold FixedRegionSimulation
          intro sourceRels targetRels sourceContext targetContext context
            sourceNodup sourceBinders targetBinders binderWitness sourceCover
            targetCover sourceEnumeration targetEnumeration sourceExact
            targetExact sourceBody targetBody sourceCompiled targetCompiled
          simp only [ConcreteElaboration.compileRegion?]
            at sourceCompiled targetCompiled
          let sourceExtended := sourceContext.extend region
          let targetExtended := targetContext.extend (trace.regionMap region)
          cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
              signature input.val
              (ConcreteElaboration.compileRegion? signature input.val sourceFuel)
              sourceExtended sourceBinders
              (ConcreteElaboration.localOccurrences input.val region) with
          | none =>
              simp [sourceExtended, sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceExtended, sourceItemsResult] at sourceCompiled
              subst sourceBody
              cases targetItemsResult :
                  ConcreteElaboration.compileOccurrencesWith? signature
                    trace.diagram
                    (ConcreteElaboration.compileRegion? signature trace.diagram
                      targetFuel)
                    targetExtended targetBinders
                    (ConcreteElaboration.localOccurrences trace.diagram
                      (trace.regionMap region)) with
              | none =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
              | some targetItems =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
                  subst targetBody
                  let sourceRecurse : ∀ {rels : RelCtx},
                      (child : Fin input.val.regionCount) →
                      (childContext : ConcreteElaboration.WireContext input.val) →
                      ConcreteElaboration.BinderContext input.val rels →
                      Option (Region signature childContext.length rels) :=
                    fun {rels} => ConcreteElaboration.compileRegion? signature
                      input.val sourceFuel
                  let targetRecurse : ∀ {rels : RelCtx},
                      (child : Fin trace.diagram.regionCount) →
                      (childContext : ConcreteElaboration.WireContext
                        trace.diagram) →
                      ConcreteElaboration.BinderContext trace.diagram rels →
                      Option (Region signature childContext.length rels) :=
                    fun {rels} => ConcreteElaboration.compileRegion? signature
                      trace.diagram targetFuel
                  let sourceSurvivors := trace.survivingSources
                    (ConcreteElaboration.localOccurrences input.val region)
                  let indices := anchorIndices occurrences region
                  let sourceSelected := selectedAt input occurrences region
                  let targetSurvivors :=
                    sourceSurvivors.map trace.survivorOccurrence
                  let targetAtoms : List (ConcreteElaboration.LocalOccurrence
                      trace.diagram.regionCount trace.diagram.nodeCount) :=
                    indices.map fun index =>
                      ConcreteElaboration.LocalOccurrence.node
                        (trace.targetAtom index)
                  have sourcePartition :
                      (sourceSurvivors ++ sourceSelected).Perm
                        (ConcreteElaboration.localOccurrences input.val region) :=
                    trace.localOccurrences_perm_focusedPartition payload region
                      regionSurvives
                  have targetPartition :
                      (ConcreteElaboration.localOccurrences trace.diagram
                          (trace.regionMap region)).Perm
                        (targetSurvivors ++ targetAtoms) := by
                    rw [trace.regionMap_of_survives region regionSurvives]
                    have rawPartition := trace.targetLocalOccurrences_nonwrap
                      payload region regionSurvives notWrap
                    simpa [sourceSurvivors, targetSurvivors, targetAtoms,
                      indices, atomsAt, anchorIndices,
                      trace.survivingSources_map_survivor] using rawPartition
                  obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_complete
                      sourceRecurse sourceExtended sourceBinders
                      (sourceSurvivors ++ sourceSelected) (by
                        intro occurrence member
                        exact ModalSoundness.compileOccurrence_success_of_mem
                          input.val sourceRecurse sourceExtended sourceBinders
                          sourceItemsResult
                          ((sourcePartition.mem_iff).1 member))
                  obtain ⟨sourceSurvivorItems, sourceSelectedItems,
                      sourceSurvivorCompiled, sourceSelectedCompiled,
                      sourcePartitionEq⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_append_split
                      sourceRecurse sourceExtended sourceBinders sourceSurvivors
                      sourceSelected sourcePartitionItems sourcePartitionCompiled
                  obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_complete
                      targetRecurse targetExtended targetBinders
                      (targetSurvivors ++ targetAtoms) (by
                        intro occurrence member
                        exact ModalSoundness.compileOccurrence_success_of_mem
                          trace.diagram targetRecurse targetExtended targetBinders
                          targetItemsResult
                          ((targetPartition.mem_iff).2 member))
                  obtain ⟨targetSurvivorItems, targetAtomItems,
                      targetSurvivorCompiled, targetAtomCompiled,
                      targetPartitionEq⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_append_split
                      targetRecurse targetExtended targetBinders targetSurvivors
                      targetAtoms targetPartitionItems targetPartitionCompiled
                  have sourceBlockExists : ∀ index, index ∈ indices →
                      ∃ items : ItemSeq signature sourceExtended.length
                          sourceRels,
                        ConcreteElaboration.compileOccurrencesWith? signature
                          input.val sourceRecurse sourceExtended sourceBinders
                          (ModalSoundness.selectedOccurrences input.val
                            (occurrences.get index).selection) = some items := by
                    intro index indexMember
                    apply ConcreteElaboration.compileOccurrencesWith?_complete
                    intro occurrence occurrenceMember
                    apply ModalSoundness.compileOccurrence_success_of_mem
                      input.val sourceRecurse sourceExtended sourceBinders
                      sourceSelectedCompiled
                    exact (mem_selectedAt input occurrences region occurrence).2
                      ⟨index, (mem_anchorIndices occurrences region index).1
                        indexMember, occurrenceMember⟩
                  let sourceFamilyItems : Fin occurrences.length →
                      ItemSeq signature sourceExtended.length sourceRels :=
                    fun index => if member : index ∈ indices then
                      Classical.choose (sourceBlockExists index member)
                    else .nil
                  have sourceFamilyCompiled : ∀ index, index ∈ indices →
                      ConcreteElaboration.compileOccurrencesWith? signature
                        input.val sourceRecurse sourceExtended sourceBinders
                        (ModalSoundness.selectedOccurrences input.val
                          (occurrences.get index).selection) =
                            some (sourceFamilyItems index) := by
                    intro index member
                    dsimp only [sourceFamilyItems]
                    rw [dif_pos member]
                    exact Classical.choose_spec (sourceBlockExists index member)
                  have sourceFamilyAggregateCompiled :=
                    compileOccurrenceFamilyItems sourceRecurse sourceExtended
                      sourceBinders indices
                      (fun index => ModalSoundness.selectedOccurrences input.val
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
                      ∃ item : Item signature targetExtended.length targetRels,
                        ConcreteElaboration.compileNode? signature trace.diagram
                          targetExtended targetBinders (trace.targetAtom index) =
                            some item := by
                    intro index indexMember
                    obtain ⟨item, compiled⟩ :=
                      ModalSoundness.compileOccurrence_success_of_mem
                        trace.diagram targetRecurse targetExtended targetBinders
                        targetAtomCompiled (by
                          exact List.mem_map.mpr ⟨index, indexMember, rfl⟩)
                    exact ⟨item, by
                      simpa [ConcreteElaboration.compileOccurrenceWith?] using
                        compiled⟩
                  let targetFamilyItems : Fin occurrences.length →
                      Item signature targetExtended.length targetRels :=
                    fun index => if member : index ∈ indices then
                      Classical.choose (targetAtomExists index member)
                    else .cut (.mk 0 .nil)
                  have targetFamilyCompiled : ∀ index, index ∈ indices →
                      ConcreteElaboration.compileNode? signature trace.diagram
                        targetExtended targetBinders (trace.targetAtom index) =
                          some (targetFamilyItems index) := by
                    intro index member
                    dsimp only [targetFamilyItems]
                    rw [dif_pos member]
                    exact Classical.choose_spec (targetAtomExists index member)
                  have targetFamilyAggregateCompiled :=
                    compileOccurrenceFamilyAtomItems targetRecurse targetExtended
                      targetBinders indices
                      (fun index => ConcreteElaboration.LocalOccurrence.node
                        (trace.targetAtom index))
                      targetFamilyItems (by
                        intro index member
                        simpa [ConcreteElaboration.compileOccurrenceWith?] using
                          targetFamilyCompiled index member)
                  have targetFamilyEq :
                      occurrenceFamilyAtomItems targetFamilyItems indices =
                        targetAtomItems := by
                    apply Option.some.inj
                    exact targetFamilyAggregateCompiled.symm.trans (by
                      simpa [targetAtoms] using targetAtomCompiled)
                  have sourceCanonicalCompiled :
                      ConcreteElaboration.compileOccurrencesWith? signature
                        input.val sourceRecurse sourceExtended sourceBinders
                        (sourceSurvivors ++ sourceSelected) =
                          some (sourceSurvivorItems.append sourceSelectedItems) := by
                    rw [← sourcePartitionEq]
                    exact sourcePartitionCompiled
                  have targetCanonicalCompiled :
                      ConcreteElaboration.compileOccurrencesWith? signature
                        trace.diagram targetRecurse targetExtended targetBinders
                        (targetSurvivors ++ targetAtoms) =
                          some (targetSurvivorItems.append targetAtomItems) := by
                    rw [← targetPartitionEq]
                    exact targetPartitionCompiled
                  have sourceCanonicalNodup :
                      (sourceSurvivors ++ sourceSelected).Nodup :=
                    (sourcePartition.nodup_iff).2
                      (ConcreteElaboration.localOccurrences_nodup input.val
                        region)
                  have targetCanonicalNodup :
                      (targetSurvivors ++ targetAtoms).Nodup :=
                    (targetPartition.nodup_iff).1
                      (ConcreteElaboration.localOccurrences_nodup trace.diagram
                        (trace.regionMap region))
                  have survivorMembers : ∀ occurrence,
                      occurrence ∈ sourceSurvivors → occurrence ∈
                        ConcreteElaboration.localOccurrences input.val region := by
                    intro occurrence member
                    exact (mem_survivingSources trace
                      (ConcreteElaboration.localOccurrences input.val region)
                      occurrence).1 member |>.1
                  have survivorMaps : ∀ occurrence,
                      occurrence ∈ sourceSurvivors →
                        ∃ target,
                          trace.survivingOccurrence? occurrence = some target := by
                    intro occurrence member
                    exact Option.isSome_iff_exists.mp
                      ((mem_survivingSources trace
                        (ConcreteElaboration.localOccurrences input.val region)
                        occurrence).1 member |>.2)
                  have recurseAt : ∀
                      (childDirection : ConcreteElaboration.SimulationDirection)
                      (child : Fin input.val.regionCount),
                      child ∈ wrap.selectedRegions →
                      trace.domains.regions.survives child = true →
                      child ≠ wrap.val.anchor →
                      AbstractionAllowed input.val wrap.val.anchor
                        childDirection child →
                      FixedRegionSimulation trace model named childDirection
                        sourceFuel targetFuel child := by
                    intro childDirection child childSelected childSurvives
                      childNotWrap childAllowed
                    exact induction childDirection targetFuel child childSurvives
                      childNotWrap childSelected childAllowed
                  have survivorSemantic :=
                    trace.focusedSurvivingSources_semantic targetWellFormed model
                      named direction sourceFuel targetFuel region regionSurvives
                      notWrap regionSelected sourceExtended targetExtended
                      (context.extend region regionSurvives) sourceBinders
                      targetBinders binderWitness sourceExact targetExact
                      sourceCover targetCover sourceEnumeration targetEnumeration
                      allowed recurseAt sourceSurvivors survivorMembers
                      survivorMaps sourceSurvivorItems targetSurvivorItems
                      sourceSurvivorCompiled (by
                        simpa [targetSurvivors] using targetSurvivorCompiled)
                  letI : Nonempty model.Carrier :=
                    ConcreteElaboration.lambdaModel_carrier_nonempty model
                  intro sourceEnvironment targetEnvironment targetRelations
                    environments fixed
                  rw [ConcreteElaboration.finishRegion_renameRelations]
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
                          model named sourceEnvironment targetRelations).1
                            sourceDenotes
                      obtain ⟨targetLocal, extendedAgreement⟩ :=
                        trace.survivorEnvironmentSelection targetWellFormed
                          .forward sourceContext targetContext context region
                          regionSurvives sourceExact sourceEnvironment
                          targetEnvironment environments sourceLocal
                      let sourceLocalEnvironment :=
                        ConcreteElaboration.extendedEnvironment sourceContext
                          region sourceEnvironment sourceLocal
                      let targetLocalEnvironment :=
                        ConcreteElaboration.extendedEnvironment targetContext
                          (trace.regionMap region) targetEnvironment targetLocal
                      have sourceRawDenote : denoteItemSeq model named
                          sourceLocalEnvironment sourceRelations sourceItems :=
                        (denoteItemSeq_renameRelations model named
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          sourceLocalEnvironment sourceItems).1 sourceItemsDenote
                      have sourcePermutation :=
                        compileOccurrences_perm_denote_iff input.val
                          sourceRecurse sourceExtended sourceBinders
                          sourcePartition sourceCanonicalNodup
                          (ConcreteElaboration.localOccurrences_nodup input.val
                            region)
                          sourceCanonicalCompiled sourceItemsResult model named
                          sourceLocalEnvironment sourceRelations
                      have sourceCanonicalDenote :=
                        sourcePermutation.mpr sourceRawDenote
                      have sourceParts :=
                        (denoteItemSeq_append model named sourceLocalEnvironment
                          sourceRelations sourceSurvivorItems
                          sourceSelectedItems).1 sourceCanonicalDenote
                      have sourceSurvivorRenamed : denoteItemSeq model named
                          sourceLocalEnvironment targetRelations
                          (sourceSurvivorItems.renameRelations
                            binderWitness.relationMap) :=
                        (denoteItemSeq_renameRelations model named
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          sourceLocalEnvironment sourceSurvivorItems).2
                            sourceParts.1
                      have targetSurvivorDenote := survivorSemantic
                        sourceLocalEnvironment targetLocalEnvironment
                        targetRelations extendedAgreement fixed
                        sourceSurvivorRenamed
                      have sourceFamilyDenote : denoteItemSeq model named
                          sourceLocalEnvironment sourceRelations
                          (occurrenceFamilyItems sourceFamilyItems indices) := by
                        rw [sourceFamilyEq]
                        exact sourceParts.2
                      have targetFamilyDenote := trace.occurrenceFamily_forward
                        payload model named sourceFuel region indices anchored
                        sourceExtended targetExtended
                        (context.extend region regionSurvives) sourceBinders
                        targetBinders sourceCover sourceEnumeration sourceExact
                        sourceFamilyItems targetFamilyItems sourceFamilyCompiled
                        targetFamilyCompiled sourceLocalEnvironment
                        targetLocalEnvironment sourceRelations targetRelations
                        fixed extendedAgreement sourceFamilyDenote
                      have targetCanonicalDenote : denoteItemSeq model named
                          targetLocalEnvironment targetRelations
                          (targetSurvivorItems.append targetAtomItems) := by
                        apply (denoteItemSeq_append model named
                          targetLocalEnvironment targetRelations
                          targetSurvivorItems targetAtomItems).2
                        refine ⟨targetSurvivorDenote, ?_⟩
                        rw [← targetFamilyEq]
                        exact targetFamilyDenote
                      have targetPermutation :=
                        compileOccurrences_perm_denote_iff trace.diagram
                          targetRecurse targetExtended targetBinders
                          targetPartition
                          (ConcreteElaboration.localOccurrences_nodup
                            trace.diagram (trace.regionMap region))
                          targetCanonicalNodup targetItemsResult
                          targetCanonicalCompiled model named
                          targetLocalEnvironment targetRelations
                      have targetItemsDenote :=
                        targetPermutation.mpr targetCanonicalDenote
                      apply (DoubleCutElimTrace.finishRegion_denote_iff
                        trace.diagram targetContext (trace.regionMap region)
                        targetItems model named targetEnvironment
                        targetRelations).2
                      exact ⟨targetLocal, targetItemsDenote⟩
                  | backward =>
                      intro targetDenotes
                      obtain ⟨targetLocal, targetItemsDenote⟩ :=
                        (DoubleCutElimTrace.finishRegion_denote_iff trace.diagram
                          targetContext (trace.regionMap region) targetItems model
                          named targetEnvironment targetRelations).1 targetDenotes
                      let targetLocalEnvironment :=
                        ConcreteElaboration.extendedEnvironment targetContext
                          (trace.regionMap region) targetEnvironment targetLocal
                      have targetPermutation :=
                        compileOccurrences_perm_denote_iff trace.diagram
                          targetRecurse targetExtended targetBinders
                          targetPartition
                          (ConcreteElaboration.localOccurrences_nodup
                            trace.diagram (trace.regionMap region))
                          targetCanonicalNodup targetItemsResult
                          targetCanonicalCompiled model named
                          targetLocalEnvironment targetRelations
                      have targetCanonicalDenote :=
                        targetPermutation.mp targetItemsDenote
                      have targetParts :=
                        (denoteItemSeq_append model named targetLocalEnvironment
                          targetRelations targetSurvivorItems targetAtomItems).1
                            targetCanonicalDenote
                      obtain ⟨baseSourceLocal, baseAgreement⟩ :=
                        trace.survivorEnvironmentSelection targetWellFormed
                          .backward sourceContext targetContext context region
                          regionSurvives sourceExact sourceEnvironment
                          targetEnvironment environments targetLocal
                      let baseSourceEnvironment :=
                        ConcreteElaboration.extendedEnvironment sourceContext
                          region sourceEnvironment baseSourceLocal
                      have targetFamilyDenote : denoteItemSeq model named
                          targetLocalEnvironment targetRelations
                          (occurrenceFamilyAtomItems targetFamilyItems indices) := by
                        rw [targetFamilyEq]
                        exact targetParts.2
                      obtain ⟨chosenSourceEnvironment, chosenAgreement,
                          sourceFamilyDenote, sourcePreserves⟩ :=
                        trace.occurrenceFamily_backward payload model named
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
                      have sourceSurvivorRaw : denoteItemSeq model named
                          chosenSourceEnvironment sourceRelations
                          sourceSurvivorItems :=
                        (denoteItemSeq_renameRelations model named
                          binderWitness.relationMap sourceRelations
                          targetRelations relationAgreement
                          chosenSourceEnvironment sourceSurvivorItems).1
                            sourceSurvivorRenamed
                      have sourceCanonicalDenote : denoteItemSeq model named
                          chosenSourceEnvironment sourceRelations
                          (sourceSurvivorItems.append sourceSelectedItems) := by
                        apply (denoteItemSeq_append model named
                          chosenSourceEnvironment sourceRelations
                          sourceSurvivorItems sourceSelectedItems).2
                        refine ⟨sourceSurvivorRaw, ?_⟩
                        rw [← sourceFamilyEq]
                        exact sourceFamilyDenote
                      have sourcePermutation :=
                        compileOccurrences_perm_denote_iff input.val
                          sourceRecurse sourceExtended sourceBinders
                          sourcePartition sourceCanonicalNodup
                          (ConcreteElaboration.localOccurrences_nodup input.val
                            region)
                          sourceCanonicalCompiled sourceItemsResult model named
                          chosenSourceEnvironment sourceRelations
                      have sourceRawDenote :=
                        sourcePermutation.mp sourceCanonicalDenote
                      have sourceRenamedDenote : denoteItemSeq model named
                          chosenSourceEnvironment targetRelations
                          (sourceItems.renameRelations
                            binderWitness.relationMap) :=
                        (denoteItemSeq_renameRelations model named
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
                        model named sourceEnvironment targetRelations).2
                      refine ⟨chosenSourceLocal, ?_⟩
                      rw [chosenEnvironmentEq]
                      exact sourceRenamedDenote

end AbstractionRawTrace

end VisualProof.Rule
