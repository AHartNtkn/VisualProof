import VisualProof.Rule.Soundness.Modal

namespace VisualProof.Rule.ModalSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

theorem doubleCutIntroFocusedItems
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (targetWellFormed :
      (doubleCutIntroRaw input.val selection).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : RelCtx}
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext :
      ConcreteElaboration.WireContext
        (doubleCutIntroRaw input.val selection))
    (context :
      LiftedContextWitness input.val selection sourceContext targetContext)
    (sourceBinders :
      ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders :
      ConcreteElaboration.BinderContext
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
      ConcreteElaboration.BinderContext.Enumeration input.val sourceBinders
        selection.val.anchor)
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        (doubleCutIntroRaw input.val selection) targetBinders
        (Fin.castAdd 2 selection.val.anchor))
    (recurseAt :
      ∀ {childDirection : ConcreteElaboration.SimulationDirection}
        {child : Fin input.val.regionCount}
        {childSourceRels childTargetRels : RelCtx}
        {childSourceBinders :
          ConcreteElaboration.BinderContext input.val childSourceRels}
        {childTargetBinders :
          ConcreteElaboration.BinderContext
            (doubleCutIntroRaw input.val selection) childTargetRels}
        (childFuelTarget : Nat)
        (childSourceContext :
          ConcreteElaboration.WireContext input.val)
        (childTargetContext :
          ConcreteElaboration.WireContext
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
        ConcreteElaboration.BinderContext.Enumeration input.val
          childSourceBinders child →
        ConcreteElaboration.BinderContext.Enumeration
          (doubleCutIntroRaw input.val selection) childTargetBinders
          (Fin.castAdd 2 child) →
        (childSourceContext.extend child).Exact child →
        (childTargetContext.extend (Fin.castAdd 2 child)).Exact
          (Fin.castAdd 2 child) →
        ∀ (sourceBody :
            Region signature childSourceContext.length childSourceRels)
          (targetBody :
            Region signature childTargetContext.length childTargetRels),
        ConcreteElaboration.compileRegion? signature input.val fuelSource child
            childSourceContext childSourceBinders = some sourceBody →
        ConcreteElaboration.compileRegion? signature
            (doubleCutIntroRaw input.val selection) childFuelTarget
            (Fin.castAdd 2 child) childTargetContext childTargetBinders =
          some targetBody →
        ConcreteElaboration.RegionSimulation model named childDirection
          childContext.indexRelation
          (sourceBody.renameRelations childBinderWitness.relationMap)
          targetBody)
    (sourceItems :
      ItemSeq signature
        sourceContext.length sourceRels)
    (targetItems :
      ItemSeq signature
        targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuelSource)
        sourceContext sourceBinders
        (ConcreteElaboration.localOccurrences input.val
          selection.val.anchor) = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (doubleCutIntroRaw input.val selection)
        (ConcreteElaboration.compileRegion? signature
          (doubleCutIntroRaw input.val selection) fuelTarget)
        targetContext
        targetBinders
        (ConcreteElaboration.localOccurrences
          (doubleCutIntroRaw input.val selection)
          (Fin.castAdd 2 selection.val.anchor)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      context.indexRelation
      (sourceItems.renameRelations binderWitness.relationMap)
      targetItems := by
  cases binderWitness.relationContexts_eq
  rw [doubleCutIntroRaw_anchor_localOccurrences] at targetCompiled
  obtain ⟨keptTargetItems, outerTargetItems, keptTargetCompiled,
      outerTargetCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (d := doubleCutIntroRaw input.val selection)
      (signature := signature)
      (fun {rels} =>
        ConcreteElaboration.compileRegion? signature
          (doubleCutIntroRaw input.val selection) fuelTarget)
      targetContext
      targetBinders
      ((keptOccurrences input.val selection).map
        (liftOccurrence input.val))
      [ConcreteElaboration.LocalOccurrence.child
        (doubleCutOuter input.val)]
      targetItems targetCompiled
  rw [targetItemsEq]
  simp only [ConcreteElaboration.compileOccurrencesWith?] at outerTargetCompiled
  simp only [ConcreteElaboration.compileOccurrenceWith?,
    doubleCutIntroRaw_outer] at outerTargetCompiled
  cases outerRegionResult :
      ConcreteElaboration.compileRegion? signature
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
          simp [ConcreteElaboration.compileRegion?] at outerRegionResult
      | succ outerFuel =>
          simp only [ConcreteElaboration.compileRegion?] at outerRegionResult
          rw [doubleCutIntroRaw_outer_localOccurrences] at outerRegionResult
          obtain ⟨outerItems, outerItemsResult, outerBodyEq⟩ :=
            Option.bind_eq_some_iff.mp outerRegionResult
          have outerBodyEq' :
              ConcreteElaboration.finishRegion
                  (doubleCutIntroRaw input.val selection)
                  targetContext
                  (doubleCutOuter input.val) outerItems =
                outerBody :=
            Option.some.inj outerBodyEq
          subst outerBody
          simp only [ConcreteElaboration.compileOccurrencesWith?,
            ConcreteElaboration.compileOccurrenceWith?,
            doubleCutIntroRaw_inner] at outerItemsResult
          cases innerRegionResult :
              ConcreteElaboration.compileRegion? signature
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
                  simp [ConcreteElaboration.compileRegion?] at innerRegionResult
              | succ innerFuel =>
                  simp only [ConcreteElaboration.compileRegion?] at innerRegionResult
                  rw [doubleCutIntroRaw_inner_localOccurrences] at innerRegionResult
                  obtain ⟨selectedTargetItems, selectedTargetCompiled,
                      innerBodyEq⟩ :=
                    Option.bind_eq_some_iff.mp innerRegionResult
                  have innerBodyEq' :
                      ConcreteElaboration.finishRegion
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
                          ConcreteElaboration.WireContext input.val) →
                        ConcreteElaboration.BinderContext input.val rels →
                        Option
                          (Region signature childContext.length rels) :=
                    fun {rels} =>
                      ConcreteElaboration.compileRegion? signature input.val
                        fuelSource
                  obtain ⟨partitionSourceItems, partitionSourceCompiled⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_complete
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
                    ConcreteElaboration.compileOccurrencesWith?_append_split
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
                            Item signature
                              sourceContext.length sourceRels)
                          (targetItem :
                            Item signature
                              targetContext.length sourceRels),
                        ConcreteElaboration.compileOccurrenceWith?
                            signature input.val sourceRecurse
                            sourceContext
                            sourceBinders occurrence =
                          some sourceItem →
                        ConcreteElaboration.compileOccurrenceWith?
                            signature
                            (doubleCutIntroRaw input.val selection)
                            (ConcreteElaboration.compileRegion? signature
                              (doubleCutIntroRaw input.val selection)
                              (innerFuel + 1 + 1))
                            targetContext
                            targetBinders
                            (liftOccurrence input.val occurrence) =
                          some targetItem →
                        ConcreteElaboration.ItemSimulation model named
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
                      model named direction fuelSource
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
                    ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover
                      (doubleCutIntroRaw_outer input.val selection)
                  have targetInnerBindersCover :=
                    ConcreteElaboration.BinderContext.covers_cut_child
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
                    unfold ConcreteElaboration.WireContext.extend
                    rw [doubleCutIntroRaw_outer_exactScopeWires]
                    exact List.append_nil _
                  have selectedTargetContextEq :
                      ((targetContext.extend
                          (doubleCutOuter input.val)).extend
                            (doubleCutInner input.val)) =
                        targetContext := by
                    apply Eq.trans _ targetOuterContextEq
                    unfold ConcreteElaboration.WireContext.extend
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
                            Item signature
                              sourceContext.length sourceRels)
                          (targetItem :
                            Item signature
                              ((targetContext.extend
                                    (doubleCutOuter input.val)).extend
                                      (doubleCutInner input.val)).length
                              sourceRels),
                        ConcreteElaboration.compileOccurrenceWith?
                            signature input.val sourceRecurse
                            sourceContext
                            sourceBinders occurrence =
                          some sourceItem →
                        ConcreteElaboration.compileOccurrenceWith?
                            signature
                            (doubleCutIntroRaw input.val selection)
                            (ConcreteElaboration.compileRegion? signature
                              (doubleCutIntroRaw input.val selection)
                              innerFuel)
                            ((targetContext.extend
                                  (doubleCutOuter input.val)).extend
                                    (doubleCutInner input.val))
                            targetBinders
                            (liftOccurrence input.val occurrence) =
                          some targetItem →
                        ConcreteElaboration.ItemSimulation model named
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
                      model named direction fuelSource innerFuel
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
                    ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model named direction sourceRecurse
                      (ConcreteElaboration.compileRegion? signature
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
                    ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                      model named direction sourceRecurse
                      (ConcreteElaboration.compileRegion? signature
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
                      denoteItem model named targetEnv relEnv
                          (.cut
                            (ConcreteElaboration.finishRegion
                              (doubleCutIntroRaw input.val selection)
                              targetContext
                              (doubleCutOuter input.val)
                              (.cons
                                (.cut
                                  (ConcreteElaboration.finishRegion
                                    (doubleCutIntroRaw input.val selection)
                                    (targetContext.extend
                                          (doubleCutOuter input.val))
                                    (doubleCutInner input.val)
                                    selectedTargetItems))
                                .nil))) ↔
                        denoteItemSeq model named
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
                      denoteItemSeq model named environment relEnv
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
                      ConcreteElaboration.ItemSeqSimulation model named
                        direction
                        context.indexRelation
                        sourceItems
                        (keptTargetItems.append
                          (.cons
                            (.cut
                              (ConcreteElaboration.finishRegion
                                (doubleCutIntroRaw input.val selection)
                                targetContext
                                (doubleCutOuter input.val)
                                (.cons
                                  (.cut
                                    (ConcreteElaboration.finishRegion
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
                        model named sourceEnv relEnv
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
                        ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                        ConcreteElaboration.ContextIndexRelation.forwardMap
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
