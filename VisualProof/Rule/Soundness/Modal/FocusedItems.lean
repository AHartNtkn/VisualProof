import VisualProof.Rule.Soundness.Modal

namespace VisualProof.Rule.ModalSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

theorem doubleCutIntroFocusedItems
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (targetWellFormed :
      (doubleCutIntroRaw input.val selection).WellFormed )
    (model : Model)
    {sourceRels targetRels : RelCtx}
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext :
      Concrete.Elaboration.WireContext
        (doubleCutIntroRaw input.val selection))
    (context :
      LiftedContextWitness input.val selection sourceContext targetContext)
    (sourceBinders :
      Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders :
      Concrete.Elaboration.BinderContext
        (doubleCutIntroRaw input.val selection) targetRels)
    (binderWitness :
      LiftedBinderWitness input.val selection sourceBinders targetBinders)
    (sourceExact :
      sourceContext.Exact
        selection.val.anchor)
    (targetExact :
      targetContext.Exact
          (Fin.castAdd 2 selection.val.anchor))
    (sourceBindersCover : sourceBinders.Covers selection.val.anchor)
    (targetBindersCover :
      targetBinders.Covers (Fin.castAdd 2 selection.val.anchor))
    (sourceEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input.val sourceBinders
        selection.val.anchor)
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration
        (doubleCutIntroRaw input.val selection) targetBinders
        (Fin.castAdd 2 selection.val.anchor))
    (recurseAt :
      ∀ {childDirection : Concrete.Elaboration.SimulationDirection}
        {child : Fin input.val.regionCount}
        {childSourceRels childTargetRels : RelCtx}
        {childSourceBinders :
          Concrete.Elaboration.BinderContext input.val childSourceRels}
        {childTargetBinders :
          Concrete.Elaboration.BinderContext
            (doubleCutIntroRaw input.val selection) childTargetRels}
        (childFuelTarget : Nat)
        (childSourceContext :
          Concrete.Elaboration.WireContext input.val)
        (childTargetContext :
          Concrete.Elaboration.WireContext
            (doubleCutIntroRaw input.val selection))
        (childContext :
          LiftedContextWitness input.val selection childSourceContext
            childTargetContext),
        True →
        True →
        (childBinderWitness :
          LiftedBinderWitness input.val selection childSourceBinders
            childTargetBinders) →
        childSourceBinders.Covers child →
        childTargetBinders.Covers (Fin.castAdd 2 child) →
        Concrete.Elaboration.BinderContext.Enumeration input.val
          childSourceBinders child →
        Concrete.Elaboration.BinderContext.Enumeration
          (doubleCutIntroRaw input.val selection) childTargetBinders
          (Fin.castAdd 2 child) →
        (childSourceContext.extend child).Exact child →
        (childTargetContext.extend (Fin.castAdd 2 child)).Exact
          (Fin.castAdd 2 child) →
        ∀ (sourceBody :
            Region  childSourceContext.length childSourceRels)
          (targetBody :
            Region  childTargetContext.length childTargetRels),
        Concrete.Elaboration.compileRegion?  input.val fuelSource child
            childSourceContext childSourceBinders = some sourceBody →
        Concrete.Elaboration.compileRegion?
            (doubleCutIntroRaw input.val selection) childFuelTarget
            (Fin.castAdd 2 child) childTargetContext childTargetBinders =
          some targetBody →
        Concrete.Elaboration.RegionSimulation model  childDirection
          childContext.indexRelation
          (sourceBody.renameRelations childBinderWitness.relationMap)
          targetBody)
    (sourceItems :
      ItemSeq
        sourceContext.length sourceRels)
    (targetItems :
      ItemSeq
        targetContext.length targetRels)
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val fuelSource)
        sourceContext sourceBinders
        (Concrete.Elaboration.localOccurrences input.val
          selection.val.anchor) = some sourceItems)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrencesWith?
        (doubleCutIntroRaw input.val selection)
        (Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input.val selection) fuelTarget)
        targetContext
        targetBinders
        (Concrete.Elaboration.localOccurrences
          (doubleCutIntroRaw input.val selection)
          (Fin.castAdd 2 selection.val.anchor)) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction
      context.indexRelation
      (sourceItems.renameRelations binderWitness.relationMap)
      targetItems := by
  cases binderWitness.relationContexts_eq
  rw [doubleCutIntroRaw_anchor_localOccurrences] at targetCompiled
  obtain ⟨keptTargetItems, outerTargetItems, keptTargetCompiled,
      outerTargetCompiled, targetItemsEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (d := doubleCutIntroRaw input.val selection)

      (fun {rels} =>
        Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input.val selection) fuelTarget)
      targetContext
      targetBinders
      ((keptOccurrences input.val selection).map
        (liftOccurrence input.val))
      [Concrete.Elaboration.LocalOccurrence.child
        (doubleCutOuter input.val)]
      targetItems targetCompiled
  rw [targetItemsEq]
  simp only [Concrete.Elaboration.compileOccurrencesWith?] at outerTargetCompiled
  simp only [Concrete.Elaboration.compileOccurrenceWith?,
    doubleCutIntroRaw_outer] at outerTargetCompiled
  cases outerRegionResult :
      Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input.val selection) fuelTarget
        (doubleCutOuter input.val)
        targetContext
        targetBinders with
  | none => simp [outerRegionResult] at outerTargetCompiled
  | some outerBody =>
      simp [outerRegionResult] at outerTargetCompiled
      subst outerTargetItems
      cases fuelTarget with
      | zero =>
          simp [Concrete.Elaboration.compileRegion?] at outerRegionResult
      | succ outerFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at outerRegionResult
          rw [doubleCutIntroRaw_outer_localOccurrences] at outerRegionResult
          obtain ⟨outerItems, outerItemsResult, outerBodyEq⟩ :=
            Option.bind_eq_some_iff.mp outerRegionResult
          have outerBodyEq' :
              Concrete.Elaboration.finishRegion
                  (doubleCutIntroRaw input.val selection)
                  targetContext
                  (doubleCutOuter input.val) outerItems =
                outerBody :=
            Option.some.inj outerBodyEq
          subst outerBody
          simp only [Concrete.Elaboration.compileOccurrencesWith?,
            Concrete.Elaboration.compileOccurrenceWith?,
            doubleCutIntroRaw_inner] at outerItemsResult
          cases innerRegionResult :
              Concrete.Elaboration.compileRegion?
                (doubleCutIntroRaw input.val selection) outerFuel
                (doubleCutInner input.val)
                (targetContext.extend
                    (doubleCutOuter input.val))
                targetBinders with
          | none => simp [innerRegionResult] at outerItemsResult
          | some innerBody =>
              simp [innerRegionResult] at outerItemsResult
              subst outerItems
              cases outerFuel with
              | zero =>
                  simp [Concrete.Elaboration.compileRegion?] at innerRegionResult
              | succ innerFuel =>
                  simp only [Concrete.Elaboration.compileRegion?] at innerRegionResult
                  rw [doubleCutIntroRaw_inner_localOccurrences] at innerRegionResult
                  obtain ⟨selectedTargetItems, selectedTargetCompiled,
                      innerBodyEq⟩ :=
                    Option.bind_eq_some_iff.mp innerRegionResult
                  have innerBodyEq' :
                      Concrete.Elaboration.finishRegion
                          (doubleCutIntroRaw input.val selection)
                          (targetContext.extend
                              (doubleCutOuter input.val))
                          (doubleCutInner input.val)
                          selectedTargetItems =
                        innerBody :=
                    Option.some.inj innerBodyEq
                  subst innerBody
                  let sourceRecurse :
                      ∀ {rels : RelCtx},
                        (child : Fin input.val.regionCount) →
                        (childContext :
                          Concrete.Elaboration.WireContext input.val) →
                        Concrete.Elaboration.BinderContext input.val rels →
                        Option
                          (Region  childContext.length rels) :=
                    fun {rels} =>
                      Concrete.Elaboration.compileRegion?  input.val
                        fuelSource
                  obtain ⟨partitionSourceItems, partitionSourceCompiled⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_complete
                      sourceRecurse
                      sourceContext
                      sourceBinders
                      (keptOccurrences input.val selection ++
                        selectedOccurrences input.val selection)
                      (by
                        intro occurrence member
                        exact compileOccurrence_success_of_mem input.val
                          sourceRecurse
                          sourceContext
                          sourceBinders sourceCompiled
                          ((anchorOccurrences_perm_partition input.val
                            selection).mem_iff.mp member))
                  obtain ⟨keptSourceItems, selectedSourceItems,
                      keptSourceCompiled, selectedSourceCompiled,
                      partitionSourceItemsEq⟩ :=
                    Concrete.Elaboration.compileOccurrencesWith?_append_split
                      sourceRecurse
                      sourceContext
                      sourceBinders
                      (keptOccurrences input.val selection)
                      (selectedOccurrences input.val selection)
                      partitionSourceItems partitionSourceCompiled
                  have keptPointwise :
                      ∀ occurrence,
                        occurrence ∈ keptOccurrences input.val selection →
                        ∀ (sourceItem :
                            Item
                              sourceContext.length sourceRels)
                          (targetItem :
                            Item
                              targetContext.length sourceRels),
                        Concrete.Elaboration.compileOccurrenceWith?
                             input.val sourceRecurse
                            sourceContext
                            sourceBinders occurrence =
                          some sourceItem →
                        Concrete.Elaboration.compileOccurrenceWith?

                            (doubleCutIntroRaw input.val selection)
                            (Concrete.Elaboration.compileRegion?
                              (doubleCutIntroRaw input.val selection)
                              (innerFuel + 1 + 1))
                            targetContext
                            targetBinders
                            (liftOccurrence input.val occurrence) =
                          some targetItem →
                        Concrete.Elaboration.ItemSimulation model
                          direction
                          context.indexRelation
                          (sourceItem.renameRelations
                            binderWitness.relationMap)
                          targetItem := by
                    intro occurrence keptMember sourceItem targetItem
                      sourceOccurrenceCompiled targetOccurrenceCompiled
                    have filteredMember := keptMember
                    rw [keptOccurrences] at filteredMember
                    have sourceMember :=
                      (List.mem_filter.mp filteredMember).1
                    apply doubleCutIntro_compileOccurrence_itemSimulation
                      input.val selection input.property targetWellFormed
                      model  direction fuelSource
                      (innerFuel + 1 + 1)
                      selection.val.anchor
                      (Fin.castAdd 2 selection.val.anchor)
                      sourceContext
                      targetContext
                      context
                      sourceBinders targetBinders binderWitness
                      sourceExact targetExact sourceBindersCover
                      targetBindersCover sourceEnumeration targetEnumeration
                      occurrence (Fin.castAdd 2)
                    · intro node occurrenceEq
                      cases occurrenceEq
                      have unselected :=
                        (List.mem_filter.mp filteredMember).2
                      simpa [occurrenceSelected] using
                        (doubleCutIntroRaw_unselected_nodeShape input.val
                          selection node (by
                            simpa [occurrenceSelected] using unselected))
                    · intro child occurrenceEq childParent
                      cases occurrenceEq
                      have unselected :=
                        (List.mem_filter.mp filteredMember).2
                      have shape :=
                        doubleCutIntroRaw_unselected_regionShape input.val
                          selection child (by
                            simpa [occurrenceSelected] using unselected)
                      cases childKind : input.val.regions child with
                      | sheet =>
                          rw [childKind] at childParent
                          simp [CRegion.parent?] at childParent
                      | cut parent =>
                          have parentEq : parent =
                              selection.val.anchor := by
                            rw [childKind] at childParent
                            exact Option.some.inj childParent
                          subst parent
                          simpa [childKind] using shape
                      | bubble parent arity =>
                          have parentEq : parent =
                              selection.val.anchor := by
                            rw [childKind] at childParent
                            exact Option.some.inj childParent
                          subst parent
                          simpa [childKind] using shape
                    · exact recurseAt
                    · exact sourceMember
                    · simpa [sourceRecurse] using sourceOccurrenceCompiled
                    · exact targetOccurrenceCompiled
                  have targetOuterExact :=
                    targetExact.extend_child targetWellFormed
                      (doubleCutIntroRaw_outer_parent input.val selection)
                  have targetInnerExact :=
                    targetOuterExact.extend_child targetWellFormed
                      (doubleCutIntroRaw_inner_parent input.val selection)
                  have targetOuterBindersCover :=
                    Concrete.Elaboration.BinderContext.covers_cut_child
                      targetBindersCover
                      (doubleCutIntroRaw_outer input.val selection)
                  have targetInnerBindersCover :=
                    Concrete.Elaboration.BinderContext.covers_cut_child
                      targetOuterBindersCover
                      (doubleCutIntroRaw_inner input.val selection)
                  have targetOuterEnumeration :=
                    targetEnumeration.cutChild targetWellFormed
                      (doubleCutIntroRaw_outer input.val selection)
                  have targetInnerEnumeration :=
                    targetOuterEnumeration.cutChild targetWellFormed
                      (doubleCutIntroRaw_inner input.val selection)
                  have targetOuterContextEq :
                      targetContext.extend
                          (doubleCutOuter input.val) =
                        targetContext := by
                    unfold Concrete.Elaboration.WireContext.extend
                    rw [doubleCutIntroRaw_outer_exactScopeWires]
                    exact List.append_nil _
                  have selectedTargetContextEq :
                      ((targetContext.extend
                          (doubleCutOuter input.val)).extend
                            (doubleCutInner input.val)) =
                        targetContext := by
                    apply Eq.trans _ targetOuterContextEq
                    unfold Concrete.Elaboration.WireContext.extend
                    rw [doubleCutIntroRaw_inner_exactScopeWires]
                    exact List.append_nil _
                  have selectedContextWitness :
                      LiftedContextWitness input.val selection
                        sourceContext
                        ((targetContext.extend
                            (doubleCutOuter input.val)).extend
                              (doubleCutInner input.val)) := by
                    exact ⟨context.contexts_eq.trans
                        selectedTargetContextEq.symm⟩
                  have selectedPointwise :
                      ∀ occurrence,
                        occurrence ∈ selectedOccurrences input.val selection →
                        ∀ (sourceItem :
                            Item
                              sourceContext.length sourceRels)
                          (targetItem :
                            Item
                              ((targetContext.extend
                                    (doubleCutOuter input.val)).extend
                                      (doubleCutInner input.val)).length
                              sourceRels),
                        Concrete.Elaboration.compileOccurrenceWith?
                             input.val sourceRecurse
                            sourceContext
                            sourceBinders occurrence =
                          some sourceItem →
                        Concrete.Elaboration.compileOccurrenceWith?

                            (doubleCutIntroRaw input.val selection)
                            (Concrete.Elaboration.compileRegion?
                              (doubleCutIntroRaw input.val selection)
                              innerFuel)
                            ((targetContext.extend
                                  (doubleCutOuter input.val)).extend
                                    (doubleCutInner input.val))
                            targetBinders
                            (liftOccurrence input.val occurrence) =
                          some targetItem →
                        Concrete.Elaboration.ItemSimulation model
                          direction selectedContextWitness.indexRelation
                          (sourceItem.renameRelations
                            binderWitness.relationMap)
                          targetItem := by
                    intro occurrence selectedMember sourceItem targetItem
                      sourceOccurrenceCompiled targetOccurrenceCompiled
                    have filteredMember := selectedMember
                    rw [selectedOccurrences] at filteredMember
                    have sourceMember :=
                      (List.mem_filter.mp filteredMember).1
                    apply doubleCutIntro_compileOccurrence_itemSimulation
                      input.val selection input.property targetWellFormed
                      model  direction fuelSource innerFuel
                      selection.val.anchor (doubleCutInner input.val)
                      sourceContext
                      ((targetContext.extend
                          (doubleCutOuter input.val)).extend
                            (doubleCutInner input.val))
                      selectedContextWitness sourceBinders targetBinders
                      binderWitness sourceExact targetInnerExact
                      sourceBindersCover targetInnerBindersCover
                      sourceEnumeration targetInnerEnumeration occurrence
                      (fun _ => doubleCutInner input.val)
                    · intro node occurrenceEq
                      cases occurrenceEq
                      have selected :=
                        (List.mem_filter.mp filteredMember).2
                      exact doubleCutIntroRaw_selected_nodeShape input.val
                        selection node (by
                          simpa [occurrenceSelected] using selected)
                    · intro child occurrenceEq childParent
                      cases occurrenceEq
                      have selected :=
                        (List.mem_filter.mp filteredMember).2
                      exact doubleCutIntroRaw_selected_regionShape input.val
                        selection child (by
                          simpa [occurrenceSelected] using selected)
                    · exact recurseAt
                    · exact sourceMember
                    · simpa [sourceRecurse] using sourceOccurrenceCompiled
                    · exact targetOccurrenceCompiled
                  have keptSimulation :=
                    Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model  direction sourceRecurse
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input.val selection)
                        (innerFuel + 1 + 1))
                      sourceContext
                      targetContext
                      sourceBinders targetBinders
                      context.indexRelation
                      binderWitness.relationMap
                      (liftOccurrence input.val)
                      (keptOccurrences input.val selection)
                      keptPointwise keptSourceItems keptTargetItems
                      keptSourceCompiled keptTargetCompiled
                  have selectedSimulation :=
                    Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model  direction sourceRecurse
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input.val selection) innerFuel)
                      sourceContext
                      ((targetContext.extend
                          (doubleCutOuter input.val)).extend
                            (doubleCutInner input.val))
                      sourceBinders targetBinders
                      selectedContextWitness.indexRelation
                      binderWitness.relationMap
                      (liftOccurrence input.val)
                      (selectedOccurrences input.val selection)
                      selectedPointwise selectedSourceItems
                      selectedTargetItems selectedSourceCompiled
                      selectedTargetCompiled
                  have nestedDenotes
                      (targetEnv : Fin
                        targetContext.length →
                          model.Carrier)
                      (relEnv : RelEnv model.Carrier sourceRels) :
                      denoteItem model  targetEnv relEnv
                          (.cut
                            (Concrete.Elaboration.finishRegion
                              (doubleCutIntroRaw input.val selection)
                              targetContext
                              (doubleCutOuter input.val)
                              (.cons
                                (.cut
                                  (Concrete.Elaboration.finishRegion
                                    (doubleCutIntroRaw input.val selection)
                                    (targetContext.extend
                                          (doubleCutOuter input.val))
                                    (doubleCutInner input.val)
                                    selectedTargetItems))
                                .nil))) ↔
                        denoteItemSeq model
                          (fun index =>
                            targetEnv (Fin.cast
                              (congrArg List.length
                                selectedTargetContextEq) index))
                          relEnv selectedTargetItems := by
                    rw [cut_denotes_negation]
                    rw [finishRegion_noWires_denote
                      (doubleCutIntroRaw input.val selection)
                      targetContext
                      (doubleCutOuter input.val)
                      (doubleCutIntroRaw_outer_exactScopeWires
                        input.val selection)]
                    rw [ItemSeq.castWiresEq_eq_renameWires,
                      denoteItemSeq_renameWires]
                    simp only [denoteItemSeq_cons, denoteItemSeq_nil,
                      and_true, cut_denotes_negation]
                    rw [Classical.not_not]
                    rw [finishRegion_noWires_denote
                      (doubleCutIntroRaw input.val selection)
                      (targetContext.extend
                          (doubleCutOuter input.val))
                      (doubleCutInner input.val)
                      (doubleCutIntroRaw_inner_exactScopeWires
                        input.val selection)]
                    rw [ItemSeq.castWiresEq_eq_renameWires,
                      denoteItemSeq_renameWires]
                    apply iff_of_eq
                    apply congrArg (fun environment =>
                      denoteItemSeq model  environment relEnv
                        selectedTargetItems)
                    funext index
                    apply congrArg targetEnv
                    apply Fin.ext
                    rfl
                  have relationMapEq :
                      (binderWitness.relationMap :
                        RelationRenaming sourceRels sourceRels) =
                          (fun {arity}
                            (relation : RelVar sourceRels arity) =>
                              relation) := by
                    rfl
                  rw [relationMapEq, ItemSeq.renameRelations_id] at keptSimulation selectedSimulation
                  have focusedItemsSimulation :
                      Concrete.Elaboration.ItemSeqSimulation model
                        direction
                        context.indexRelation
                        sourceItems
                        (keptTargetItems.append
                          (.cons
                            (.cut
                              (Concrete.Elaboration.finishRegion
                                (doubleCutIntroRaw input.val selection)
                                targetContext
                                (doubleCutOuter input.val)
                                (.cons
                                  (.cut
                                    (Concrete.Elaboration.finishRegion
                                      (doubleCutIntroRaw input.val selection)
                                      (targetContext.extend
                                            (doubleCutOuter input.val))
                                      (doubleCutInner input.val)
                                      selectedTargetItems))
                                  .nil)))
                            .nil)) := by
                    intro sourceEnv targetEnv relEnv environments
                    have sourcePartition :=
                      compileOccurrences_denote_perm input.val sourceRecurse
                        sourceContext
                        sourceBinders
                        (anchorOccurrences_perm_partition input.val
                          selection).symm
                        sourceCompiled partitionSourceCompiled
                        model  sourceEnv relEnv
                    rw [partitionSourceItemsEq,
                      denoteItemSeq_append] at sourcePartition
                    have keptEntailment :=
                      keptSimulation sourceEnv targetEnv relEnv environments
                    let selectedTargetEnv :
                        Fin
                          ((targetContext.extend
                                (doubleCutOuter input.val)).extend
                                  (doubleCutInner input.val)).length →
                            model.Carrier :=
                      fun index =>
                        targetEnv (Fin.cast
                          (congrArg List.length
                            selectedTargetContextEq) index)
                    have selectedEnvironments :
                        selectedContextWitness.indexRelation.EnvironmentsAgree
                          sourceEnv selectedTargetEnv := by
                      unfold LiftedContextWitness.indexRelation
                        Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
                        Concrete.Elaboration.ContextIndexRelation.forwardMap
                      intro sourceIndex targetIndex related
                      subst targetIndex
                      have base := environments sourceIndex
                        (Fin.cast
                          (congrArg List.length
                            context.contexts_eq)
                          sourceIndex)
                        rfl
                      exact base.trans (by
                        apply congrArg targetEnv
                        apply Fin.ext
                        rfl)
                    have selectedEntailment :=
                      selectedSimulation sourceEnv selectedTargetEnv relEnv
                        selectedEnvironments
                    rw [denoteItemSeq_append, denoteItemSeq_cons,
                      denoteItemSeq_nil, and_true]
                    cases direction with
                    | forward =>
                        intro sourceDenotes
                        have partitionDenotes :=
                          sourcePartition.mp sourceDenotes
                        exact ⟨keptEntailment partitionDenotes.1,
                          (nestedDenotes targetEnv relEnv).mpr
                            (selectedEntailment partitionDenotes.2)⟩
                    | backward =>
                        rintro ⟨keptDenotes, nestedDenotesTarget⟩
                        apply sourcePartition.mpr
                        exact ⟨keptEntailment keptDenotes,
                          selectedEntailment
                            ((nestedDenotes targetEnv relEnv).mp
                              nestedDenotesTarget)⟩
                  rw [relationMapEq, ItemSeq.renameRelations_id]
                  exact focusedItemsSimulation

end VisualProof.Rule.ModalSoundness
