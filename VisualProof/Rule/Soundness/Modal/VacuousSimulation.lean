import VisualProof.Rule.Soundness.Modal.VacuousCompiler

namespace VisualProof.Rule.VacuousSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem bubbleItem_denote
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (arity : Nat)
    (context : Concrete.Elaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (items : ItemSeq
      (context.extend (bubbleRegion input)).length (arity :: rels))
    (model : Model)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItem model  env relEnv
        (.bubble arity
          (Concrete.Elaboration.finishRegion
            (vacuousIntroRaw input selection arity) context
            (bubbleRegion input) items)) ↔
      ∃ fresh : Relation model.Carrier arity,
        denoteItemSeq (relCtx := arity :: rels) model  env
          ((fresh, relEnv) : RelEnv model.Carrier (arity :: rels))
          (items.castWiresEq
            (congrArg List.length (by
              unfold Concrete.Elaboration.WireContext.extend
              rw [vacuousIntroRaw_bubble_exactScopeWires]
              exact List.append_nil context))) := by
  rw [bubble_denotes_exists]
  apply exists_congr
  intro fresh
  exact ModalSoundness.finishRegion_noWires_denote
    (vacuousIntroRaw input selection arity) context (bubbleRegion input)
    (vacuousIntroRaw_bubble_exactScopeWires input selection arity)
    items model  env (fresh, relEnv)

theorem focusedItems
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw input.val selection arity).WellFormed )
    (model : Model)
    {sourceRels targetRels : RelCtx}
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext
      (vacuousIntroRaw input.val selection arity))
    (context : LiftedContextWitness input.val selection arity
      sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input.val selection arity) targetRels)
    (binderWitness : MappedBinderWitness input.val selection arity
      sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact selection.val.anchor)
    (targetExact : targetContext.Exact selection.val.anchor.castSucc)
    (sourceBindersCover : sourceBinders.Covers selection.val.anchor)
    (targetBindersCover : targetBinders.Covers selection.val.anchor.castSucc)
    (sourceEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input.val sourceBinders
        selection.val.anchor)
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration
        (vacuousIntroRaw input.val selection arity) targetBinders
        selection.val.anchor.castSucc)
    (recurseAt : ∀
      {childDirection : Concrete.Elaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders :
        Concrete.Elaboration.BinderContext input.val childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        (vacuousIntroRaw input.val selection arity) childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : Concrete.Elaboration.WireContext input.val)
      (childTargetContext : Concrete.Elaboration.WireContext
        (vacuousIntroRaw input.val selection arity))
      (childContext : LiftedContextWitness input.val selection arity
        childSourceContext childTargetContext),
      True → True →
      (childBinderWitness : MappedBinderWitness input.val selection arity
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child.castSucc →
      Concrete.Elaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      Concrete.Elaboration.BinderContext.Enumeration
        (vacuousIntroRaw input.val selection arity) childTargetBinders
        child.castSucc →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend child.castSucc).Exact child.castSucc →
      ∀ (sourceBody : Region  childSourceContext.length
          childSourceRels)
        (targetBody : Region  childTargetContext.length
          childTargetRels),
      Concrete.Elaboration.compileRegion?  input.val fuelSource child
          childSourceContext childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion?
          (vacuousIntroRaw input.val selection arity) childFuelTarget
          child.castSucc childTargetContext childTargetBinders =
        some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap) targetBody)
    (sourceItems : ItemSeq  sourceContext.length sourceRels)
    (targetItems : ItemSeq  targetContext.length targetRels)
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val fuelSource)
        sourceContext sourceBinders
        (Concrete.Elaboration.localOccurrences input.val
          selection.val.anchor) = some sourceItems)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrencesWith?
        (vacuousIntroRaw input.val selection arity)
        (Concrete.Elaboration.compileRegion?
          (vacuousIntroRaw input.val selection arity) fuelTarget)
        targetContext targetBinders
        (Concrete.Elaboration.localOccurrences
          (vacuousIntroRaw input.val selection arity)
          selection.val.anchor.castSucc) = some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction
      context.indexRelation
      (sourceItems.renameRelations binderWitness.relationMap) targetItems := by
  rw [anchor_localOccurrences] at targetCompiled
  obtain ⟨keptTargetItems, bubbleTargetItems, keptTargetCompiled,
      bubbleTargetCompiled, targetItemsEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (d := vacuousIntroRaw input.val selection arity)

      (fun {rels} => Concrete.Elaboration.compileRegion?
        (vacuousIntroRaw input.val selection arity) fuelTarget)
      targetContext targetBinders
      ((ModalSoundness.keptOccurrences input.val selection).map
        (liftOccurrence input.val))
      [Concrete.Elaboration.LocalOccurrence.child (bubbleRegion input.val)]
      targetItems targetCompiled
  rw [targetItemsEq]
  simp only [Concrete.Elaboration.compileOccurrencesWith?] at bubbleTargetCompiled
  simp only [Concrete.Elaboration.compileOccurrenceWith?,
    vacuousIntroRaw_bubble] at bubbleTargetCompiled
  cases bubbleResult :
      Concrete.Elaboration.compileRegion?
        (vacuousIntroRaw input.val selection arity) fuelTarget
        (bubbleRegion input.val) targetContext
        (targetBinders.push (bubbleRegion input.val) arity) with
  | none => simp [bubbleResult] at bubbleTargetCompiled
  | some bubbleBody =>
      simp [bubbleResult] at bubbleTargetCompiled
      subst bubbleTargetItems
      cases fuelTarget with
      | zero =>
          simp [Concrete.Elaboration.compileRegion?] at bubbleResult
      | succ bubbleFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at bubbleResult
          rw [bubble_localOccurrences] at bubbleResult
          obtain ⟨selectedTargetItems, selectedTargetCompiled, bubbleBodyEq⟩ :=
            Option.bind_eq_some_iff.mp bubbleResult
          have bubbleBodyEq' :
              Concrete.Elaboration.finishRegion
                  (vacuousIntroRaw input.val selection arity) targetContext
                  (bubbleRegion input.val) selectedTargetItems = bubbleBody :=
            Option.some.inj bubbleBodyEq
          subst bubbleBody
          let sourceRecurse :
              ∀ {rels : RelCtx},
                (child : Fin input.val.regionCount) →
                (childContext : Concrete.Elaboration.WireContext input.val) →
                Concrete.Elaboration.BinderContext input.val rels →
                Option (Region  childContext.length rels) :=
            fun {rels} => Concrete.Elaboration.compileRegion?
              input.val fuelSource
          obtain ⟨partitionSourceItems, partitionSourceCompiled⟩ :=
            Concrete.Elaboration.compileOccurrencesWith?_complete sourceRecurse
              sourceContext sourceBinders
              (ModalSoundness.keptOccurrences input.val selection ++
                ModalSoundness.selectedOccurrences input.val selection)
              (by
                intro occurrence member
                exact ModalSoundness.compileOccurrence_success_of_mem input.val
                  sourceRecurse sourceContext sourceBinders sourceCompiled
                  ((anchorOccurrences_perm_partition input.val selection).mem_iff.mp
                    member))
          obtain ⟨keptSourceItems, selectedSourceItems,
              keptSourceCompiled, selectedSourceCompiled,
              partitionSourceItemsEq⟩ :=
            Concrete.Elaboration.compileOccurrencesWith?_append_split
              sourceRecurse sourceContext sourceBinders
              (ModalSoundness.keptOccurrences input.val selection)
              (ModalSoundness.selectedOccurrences input.val selection)
              partitionSourceItems partitionSourceCompiled
          have keptPointwise :
              ∀ occurrence,
                occurrence ∈ ModalSoundness.keptOccurrences input.val selection →
                ∀ (sourceItem : Item  sourceContext.length sourceRels)
                  (targetItem : Item  targetContext.length targetRels),
                Concrete.Elaboration.compileOccurrenceWith?  input.val
                    sourceRecurse sourceContext sourceBinders occurrence =
                  some sourceItem →
                Concrete.Elaboration.compileOccurrenceWith?
                    (vacuousIntroRaw input.val selection arity)
                    (Concrete.Elaboration.compileRegion?
                      (vacuousIntroRaw input.val selection arity)
                      (bubbleFuel + 1))
                    targetContext targetBinders
                    (liftOccurrence input.val occurrence) = some targetItem →
                Concrete.Elaboration.ItemSimulation model  direction
                  context.indexRelation
                  (sourceItem.renameRelations binderWitness.relationMap)
                  targetItem := by
            intro occurrence keptMember sourceItem targetItem
              sourceOccurrenceCompiled targetOccurrenceCompiled
            have filteredMember := keptMember
            rw [ModalSoundness.keptOccurrences] at filteredMember
            have sourceMember := (List.mem_filter.mp filteredMember).1
            apply compileOccurrence_itemSimulation input.val selection arity
              input.property targetWellFormed model  direction fuelSource
              (bubbleFuel + 1) selection.val.anchor
              selection.val.anchor.castSucc sourceContext targetContext context
              sourceBinders targetBinders binderWitness sourceExact targetExact
              sourceBindersCover targetBindersCover sourceEnumeration
              targetEnumeration occurrence Fin.castSucc
            · intro node occurrenceEq
              cases occurrenceEq
              have unselected := (List.mem_filter.mp filteredMember).2
              exact unselected_nodeShape input.val selection arity node (by
                simpa [ModalSoundness.occurrenceSelected] using unselected)
            · intro child occurrenceEq childParent
              cases occurrenceEq
              have unselected := (List.mem_filter.mp filteredMember).2
              have shape := unselected_regionShape input.val selection arity
                child (by
                  simpa [ModalSoundness.occurrenceSelected] using unselected)
              cases childKind : input.val.regions child with
              | sheet =>
                  rw [childKind] at childParent
                  simp [CRegion.parent?] at childParent
              | cut parent =>
                  have parentEq : parent = selection.val.anchor := by
                    rw [childKind] at childParent
                    exact Option.some.inj childParent
                  subst parent
                  simpa [childKind] using shape
              | bubble parent childArity =>
                  have parentEq : parent = selection.val.anchor := by
                    rw [childKind] at childParent
                    exact Option.some.inj childParent
                  subst parent
                  simpa [childKind] using shape
            · intro childDirection child childSourceRels childTargetRels
                childSourceBinders childTargetBinders childFuelTarget
                childSourceContext childTargetContext childContext
                childBinderWitness childSourceCover childTargetCover
                childSourceEnumeration childTargetEnumeration childSourceExact
                childTargetExact sourceBody targetBody sourceResult targetResult
              exact recurseAt childFuelTarget childSourceContext
                childTargetContext childContext True.intro True.intro
                childBinderWitness childSourceCover childTargetCover
                childSourceEnumeration childTargetEnumeration childSourceExact
                childTargetExact sourceBody targetBody sourceResult targetResult
            · exact sourceMember
            · simpa [sourceRecurse] using sourceOccurrenceCompiled
            · exact targetOccurrenceCompiled
          have bubbleParent :=
            vacuousIntroRaw_bubble_parent input.val selection arity
          have targetBubbleExact :=
            targetExact.extend_child targetWellFormed bubbleParent
          have targetBubbleBindersCover :=
            Concrete.Elaboration.BinderContext.push_covers_bubble_child
              targetBindersCover
              (vacuousIntroRaw_bubble input.val selection arity)
          have targetBubbleEnumeration :=
            targetEnumeration.bubbleChild targetWellFormed
              (vacuousIntroRaw_bubble input.val selection arity)
          have targetBubbleContextEq :
              targetContext.extend (bubbleRegion input.val) = targetContext := by
            unfold Concrete.Elaboration.WireContext.extend
            rw [vacuousIntroRaw_bubble_exactScopeWires]
            exact List.append_nil _
          have selectedContextWitness :
              LiftedContextWitness input.val selection arity sourceContext
                (targetContext.extend (bubbleRegion input.val)) :=
            ⟨context.contexts_eq.trans targetBubbleContextEq.symm⟩
          let bubbleBinderWitness :=
            MappedBinderWitness.intoBubble binderWitness
          have selectedPointwise :
              ∀ occurrence,
                occurrence ∈
                  ModalSoundness.selectedOccurrences input.val selection →
                ∀ (sourceItem : Item  sourceContext.length sourceRels)
                  (targetItem : Item
                    (targetContext.extend (bubbleRegion input.val)).length
                    (arity :: targetRels)),
                Concrete.Elaboration.compileOccurrenceWith?  input.val
                    sourceRecurse sourceContext sourceBinders occurrence =
                  some sourceItem →
                Concrete.Elaboration.compileOccurrenceWith?
                    (vacuousIntroRaw input.val selection arity)
                    (Concrete.Elaboration.compileRegion?
                      (vacuousIntroRaw input.val selection arity) bubbleFuel)
                    (targetContext.extend (bubbleRegion input.val))
                    (targetBinders.push (bubbleRegion input.val) arity)
                    (liftOccurrence input.val occurrence) = some targetItem →
                Concrete.Elaboration.ItemSimulation model  direction
                  selectedContextWitness.indexRelation
                  (sourceItem.renameRelations bubbleBinderWitness.relationMap)
                  targetItem := by
            intro occurrence selectedMember sourceItem targetItem
              sourceOccurrenceCompiled targetOccurrenceCompiled
            have filteredMember := selectedMember
            rw [ModalSoundness.selectedOccurrences] at filteredMember
            have sourceMember := (List.mem_filter.mp filteredMember).1
            apply compileOccurrence_itemSimulation input.val selection arity
              input.property targetWellFormed model  direction fuelSource
              bubbleFuel selection.val.anchor (bubbleRegion input.val)
              sourceContext (targetContext.extend (bubbleRegion input.val))
              selectedContextWitness sourceBinders
              (targetBinders.push (bubbleRegion input.val) arity)
              bubbleBinderWitness sourceExact targetBubbleExact
              sourceBindersCover targetBubbleBindersCover sourceEnumeration
              targetBubbleEnumeration occurrence (fun _ => bubbleRegion input.val)
            · intro node occurrenceEq
              cases occurrenceEq
              have selected := (List.mem_filter.mp filteredMember).2
              exact selected_nodeShape input.val selection arity node (by
                simpa [ModalSoundness.occurrenceSelected] using selected)
            · intro child occurrenceEq childParent
              cases occurrenceEq
              have selected := (List.mem_filter.mp filteredMember).2
              exact selected_regionShape input.val selection arity child (by
                simpa [ModalSoundness.occurrenceSelected] using selected)
            · intro childDirection child childSourceRels childTargetRels
                childSourceBinders childTargetBinders childFuelTarget
                childSourceContext childTargetContext childContext
                childBinderWitness childSourceCover childTargetCover
                childSourceEnumeration childTargetEnumeration childSourceExact
                childTargetExact sourceBody targetBody sourceResult targetResult
              exact recurseAt childFuelTarget childSourceContext
                childTargetContext childContext True.intro True.intro
                childBinderWitness childSourceCover childTargetCover
                childSourceEnumeration childTargetEnumeration childSourceExact
                childTargetExact sourceBody targetBody sourceResult targetResult
            · exact sourceMember
            · simpa [sourceRecurse] using sourceOccurrenceCompiled
            · exact targetOccurrenceCompiled
          have keptSimulation :=
            Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model  direction sourceRecurse
              (Concrete.Elaboration.compileRegion?
                (vacuousIntroRaw input.val selection arity) (bubbleFuel + 1))
              sourceContext targetContext sourceBinders targetBinders
              context.indexRelation binderWitness.relationMap
              (liftOccurrence input.val)
              (ModalSoundness.keptOccurrences input.val selection)
              keptPointwise keptSourceItems keptTargetItems keptSourceCompiled
              keptTargetCompiled
          have selectedSimulation :=
            Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model  direction sourceRecurse
              (Concrete.Elaboration.compileRegion?
                (vacuousIntroRaw input.val selection arity) bubbleFuel)
              sourceContext (targetContext.extend (bubbleRegion input.val))
              sourceBinders
              (targetBinders.push (bubbleRegion input.val) arity)
              selectedContextWitness.indexRelation
              bubbleBinderWitness.relationMap (liftOccurrence input.val)
              (ModalSoundness.selectedOccurrences input.val selection)
              selectedPointwise selectedSourceItems selectedTargetItems
              selectedSourceCompiled selectedTargetCompiled
          have sourcePartitionDenote
              (sourceEnv : Fin sourceContext.length → model.Carrier)
              (sourceRelEnv : RelEnv model.Carrier sourceRels) :
              denoteItemSeq model  sourceEnv sourceRelEnv sourceItems ↔
                (denoteItemSeq model  sourceEnv sourceRelEnv
                    keptSourceItems ∧
                  denoteItemSeq model  sourceEnv sourceRelEnv
                    selectedSourceItems) := by
            have permutation :=
              ModalSoundness.compileOccurrences_denote_perm input.val
                sourceRecurse sourceContext sourceBinders
                (anchorOccurrences_perm_partition input.val selection).symm
                sourceCompiled partitionSourceCompiled model  sourceEnv
                sourceRelEnv
            rw [partitionSourceItemsEq,
              denoteItemSeq_append] at permutation
            exact permutation
          let selectedTargetEnv
              (targetEnv : Fin targetContext.length → model.Carrier) :
              Fin (targetContext.extend (bubbleRegion input.val)).length →
                model.Carrier :=
            fun index => targetEnv (Fin.cast
              (congrArg List.length targetBubbleContextEq) index)
          have selectedEnvironments
              (sourceEnv : Fin sourceContext.length → model.Carrier)
              (targetEnv : Fin targetContext.length → model.Carrier)
              (environments : context.indexRelation.EnvironmentsAgree
                sourceEnv targetEnv) :
              selectedContextWitness.indexRelation.EnvironmentsAgree sourceEnv
                (selectedTargetEnv targetEnv) := by
            unfold LiftedContextWitness.indexRelation
              Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
              Concrete.Elaboration.ContextIndexRelation.forwardMap
            intro sourceIndex targetIndex related
            subst targetIndex
            have base := environments sourceIndex
              (Fin.cast (congrArg List.length context.contexts_eq) sourceIndex)
              rfl
            exact base.trans (by
              apply congrArg targetEnv
              apply Fin.ext
              rfl)
          have bubbleDenotes
              (targetEnv : Fin targetContext.length → model.Carrier)
              (targetRelEnv : RelEnv model.Carrier targetRels) :
              denoteItem model  targetEnv targetRelEnv
                  (.bubble arity
                    (Concrete.Elaboration.finishRegion
                      (vacuousIntroRaw input.val selection arity) targetContext
                      (bubbleRegion input.val) selectedTargetItems)) ↔
                ∃ fresh : Relation model.Carrier arity,
                  denoteItemSeq (relCtx := arity :: targetRels) model
                    (selectedTargetEnv targetEnv)
                    (fresh, targetRelEnv) selectedTargetItems := by
            rw [bubbleItem_denote input.val selection arity targetContext
              selectedTargetItems model  targetEnv targetRelEnv]
            apply exists_congr
            intro fresh
            rw [ItemSeq.castWiresEq_eq_renameWires,
              denoteItemSeq_renameWires]
            apply iff_of_eq
            apply congrArg (fun environment =>
              denoteItemSeq (relCtx := arity :: targetRels) model
                environment (fresh, targetRelEnv) selectedTargetItems)
            funext index
            rfl
          intro sourceEnv targetEnv targetRelEnv environments
          let sourceRelEnv : RelEnv model.Carrier sourceRels :=
            RelEnv.pullback binderWitness.relationMap targetRelEnv
          have baseAgrees : RelEnv.Agrees binderWitness.relationMap
              sourceRelEnv targetRelEnv :=
            RelEnv.pullback_agrees binderWitness.relationMap targetRelEnv
          have bubbleAgrees (fresh : Relation model.Carrier arity) :
              RelEnv.Agrees bubbleBinderWitness.relationMap sourceRelEnv
                (fresh, targetRelEnv) := by
            intro binderArity relation
            exact baseAgrees binderArity relation
          have sourceRename :
              denoteItemSeq model  sourceEnv targetRelEnv
                  (sourceItems.renameRelations binderWitness.relationMap) ↔
                denoteItemSeq model  sourceEnv sourceRelEnv sourceItems :=
            denoteItemSeq_renameRelations model  binderWitness.relationMap
              sourceRelEnv targetRelEnv baseAgrees sourceEnv sourceItems
          have keptRename :
              denoteItemSeq model  sourceEnv targetRelEnv
                  (keptSourceItems.renameRelations binderWitness.relationMap) ↔
                denoteItemSeq model  sourceEnv sourceRelEnv
                  keptSourceItems :=
            denoteItemSeq_renameRelations model  binderWitness.relationMap
              sourceRelEnv targetRelEnv baseAgrees sourceEnv keptSourceItems
          have selectedRename (fresh : Relation model.Carrier arity) :
              denoteItemSeq (relCtx := arity :: targetRels) model
                  sourceEnv (fresh, targetRelEnv)
                  (selectedSourceItems.renameRelations
                    bubbleBinderWitness.relationMap) ↔
                denoteItemSeq model  sourceEnv sourceRelEnv
                  selectedSourceItems :=
            denoteItemSeq_renameRelations model
              bubbleBinderWitness.relationMap sourceRelEnv
              (fresh, targetRelEnv) (bubbleAgrees fresh) sourceEnv
              selectedSourceItems
          have keptEntailment :=
            keptSimulation sourceEnv targetEnv targetRelEnv environments
          have selectedAgreement :=
            selectedEnvironments sourceEnv targetEnv environments
          simp only [denoteItemSeq_append, denoteItemSeq_cons,
            denoteItemSeq_nil, and_true]
          cases direction with
          | forward =>
              intro sourceDenotes
              have partitionDenotes :=
                (sourcePartitionDenote sourceEnv sourceRelEnv).mp
                  (sourceRename.mp sourceDenotes)
              have keptTarget :=
                keptEntailment (keptRename.mpr partitionDenotes.1)
              let fresh : Relation model.Carrier arity := fun _ => False
              have selectedEntailment := selectedSimulation sourceEnv
                (selectedTargetEnv targetEnv) (fresh, targetRelEnv)
                selectedAgreement
              have selectedTarget := selectedEntailment
                ((selectedRename fresh).mpr partitionDenotes.2)
              exact ⟨keptTarget,
                ⟨(bubbleDenotes targetEnv targetRelEnv).mpr
                  ⟨fresh, selectedTarget⟩, trivial⟩⟩
          | backward =>
              rintro ⟨keptTarget, bubbleTarget⟩
              have keptSourceRenamed := keptEntailment keptTarget
              rcases bubbleTarget with ⟨bubbleItemTarget, _⟩
              obtain ⟨fresh, selectedTarget⟩ :=
                (bubbleDenotes targetEnv targetRelEnv).mp bubbleItemTarget
              have selectedEntailment := selectedSimulation sourceEnv
                (selectedTargetEnv targetEnv) (fresh, targetRelEnv)
                selectedAgreement
              have selectedSourceRenamed :=
                selectedEntailment selectedTarget
              apply sourceRename.mpr
              apply (sourcePartitionDenote sourceEnv sourceRelEnv).mpr
              exact ⟨keptRename.mp keptSourceRenamed,
                (selectedRename fresh).mp selectedSourceRenamed⟩

theorem localTransport_of_itemSimulation
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (arity : Nat) (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (context : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceItems : ItemSeq
      (sourceContext.extend region).length rels)
    (targetItems : ItemSeq
      (targetContext.extend region.castSucc).length rels)
    (itemSimulation : Concrete.Elaboration.ItemSeqSimulation model
      direction (context.extend region).indexRelation sourceItems targetItems) :
    ∀ relEnv,
      Concrete.Elaboration.DirectionalLocalTransport direction
        sourceContext targetContext region region.castSucc
        context.indexRelation model  relEnv sourceItems targetItems := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  let extendedWitness :=
    LiftedContextWitness.extend
      (input := input) (selection := selection) (arity := arity)
      (⟨rfl⟩ : LiftedContextWitness input selection arity
        sourceContext sourceContext) region
  intro relEnv
  apply Concrete.Elaboration.directionalLocalTransport_of_agreement
    (source := input) (target := vacuousIntroRaw input selection arity)
    direction sourceContext sourceContext region region.castSucc
    (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
    extendedWitness.indexRelation model  sourceItems targetItems
  · intro sourceOuter targetOuter outerAgrees
    have outerEq : sourceOuter = targetOuter := by
      simpa only [
        Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap,
        Function.comp_id] using outerAgrees
    cases direction with
    | forward =>
        intro sourceLocal
        let localCountEq :
            (Concrete.Elaboration.exactScopeWires
              (vacuousIntroRaw input selection arity) region.castSucc).length =
              (Concrete.Elaboration.exactScopeWires input region).length :=
          congrArg List.length
            (vacuousIntroRaw_exactScopeWires input selection arity region)
        let targetLocal : Fin
            (Concrete.Elaboration.exactScopeWires
              (vacuousIntroRaw input selection arity)
              region.castSucc).length → model.Carrier :=
          fun index => sourceLocal (Fin.cast localCountEq index)
        refine ⟨targetLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
          Concrete.Elaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        subst targetOuter
        simp only [Concrete.Elaboration.extendedEnvironment, targetLocal,
          Function.comp_apply]
        apply ModalSoundness.extendWireEnv_transport
          (countEq := localCountEq) (sourceLocal := sourceLocal)
          (targetLocal := targetLocal)
        · intro localIndex
          rfl
        · rfl
    | backward =>
        intro targetLocal
        let localCountEq :
            (Concrete.Elaboration.exactScopeWires
              (vacuousIntroRaw input selection arity) region.castSucc).length =
              (Concrete.Elaboration.exactScopeWires input region).length :=
          congrArg List.length
            (vacuousIntroRaw_exactScopeWires input selection arity region)
        let sourceLocal :
            Fin (Concrete.Elaboration.exactScopeWires input region).length →
              model.Carrier :=
          fun index => targetLocal (Fin.cast localCountEq.symm index)
        refine ⟨sourceLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
          Concrete.Elaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        subst targetOuter
        simp only [Concrete.Elaboration.extendedEnvironment, sourceLocal,
          Function.comp_apply]
        apply ModalSoundness.extendWireEnv_transport
          (countEq := localCountEq) (sourceLocal := sourceLocal)
          (targetLocal := targetLocal)
        · intro localIndex
          apply congrArg targetLocal
          apply Fin.ext
          rfl
        · rfl
  · exact itemSimulation

noncomputable def vacuousIntroSimulation
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw input.val selection arity).WellFormed )
    (model : Model)
    :
    Concrete.Elaboration.ConcreteSemanticSimulation  input.val
      (vacuousIntroRaw input.val selection arity) model  where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := Fin.castSucc
  binderMap := Fin.castSucc
  Distinguished := fun region => region = selection.val.anchor
  occurrenceMap := fun _ _ occurrence => liftOccurrence input.val occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := vacuousIntroRaw_root input.val selection arity
  region_shape := by
    intro parent regular child childParent
    exact regular_regionShape input.val selection arity parent child regular
      childParent
  localOccurrences_map := by
    intro region regular
    exact regular_localOccurrences input.val selection arity region regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    MappedBinderWitness input.val selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := {
    relationMap := Concrete.Elaboration.identityRelationRenaming []
    bindersMapped := by
      intro region binderArity sourceRelation sourceLookup
      exact Fin.elim0 sourceRelation.index
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      childArity childKind regular
    exact witness.push child childArity
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      childArity childKind regular
    exact witness.relationMap_push child childArity
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := fun sourceContext targetContext =>
    LiftedContextWitness input.val selection arity sourceContext targetContext
  AtRegion := fun _ _ => True
  indexRelation := fun witness => witness.indexRelation
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact witness.extend region
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    exact witness.extend region
  at_child := by simp
  at_extended := by simp
  at_focused_child := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    exact localTransport_of_itemSimulation input.val selection arity model
      direction sourceContext targetContext context region
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    have targetNodeEq : targetNode = sourceNode :=
      Concrete.Elaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    apply compileNode_itemSimulation input.val selection arity model
      direction sourceContext targetContext context sourceBinders targetBinders
      binderWitness.relationMap sourceNode binderWitness.bindersMapped
      Fin.castSucc
    · exact regular_nodeShape input.val selection arity region regular
        sourceNode nodeRegion
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    let extendedContext := context.extend selection.val.anchor
    have itemSemantics := focusedItems input selection arity targetWellFormed
      model  direction fuelSource fuelTarget
      (sourceContext.extend selection.val.anchor)
      (targetContext.extend selection.val.anchor.castSucc) extendedContext
      sourceBinders targetBinders binderWitness sourceExact targetExact
      sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
      recurseAt sourceItems targetItems sourceCompiled targetCompiled
    rw [Concrete.Elaboration.finishRegion_renameRelations sourceContext
      selection.val.anchor binderWitness.relationMap sourceItems]
    apply Concrete.Elaboration.finishRegion_denote
      (source := input.val)
      (target := vacuousIntroRaw input.val selection arity)
      direction sourceContext targetContext selection.val.anchor
      selection.val.anchor.castSucc context.indexRelation model
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
    exact localTransport_of_itemSimulation input.val selection arity model
      direction sourceContext targetContext context selection.val.anchor
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
      itemSemantics

end VisualProof.Rule.VacuousSoundness
