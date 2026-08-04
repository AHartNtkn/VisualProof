import VisualProof.Rule.Soundness.Modal.VacuousCompiler

namespace VisualProof.Rule.VacuousSoundness

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem bubbleItem_denote
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat)
    (context : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (items : ItemSeq signature
      (context.extend (bubbleRegion input)).length (arity :: rels))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItem model named env relEnv
        (.bubble arity
          (ConcreteElaboration.finishRegion
            (vacuousIntroRaw input selection arity) context
            (bubbleRegion input) items)) ↔
      ∃ fresh : Relation model.Carrier arity,
        denoteItemSeq (relCtx := arity :: rels) model named env
          ((fresh, relEnv) : RelEnv model.Carrier (arity :: rels))
          (items.castWiresEq
            (congrArg List.length (by
              unfold ConcreteElaboration.WireContext.extend
              rw [vacuousIntroRaw_bubble_exactScopeWires]
              exact List.append_nil context))) := by
  rw [bubble_denotes_exists]
  apply exists_congr
  intro fresh
  exact ModalSoundness.finishRegion_noWires_denote
    (vacuousIntroRaw input selection arity) context (bubbleRegion input)
    (vacuousIntroRaw_bubble_exactScopeWires input selection arity)
    items model named env (fresh, relEnv)

theorem focusedItems
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw input.val selection arity).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : RelCtx}
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input.val selection arity))
    (context : LiftedContextWitness input.val selection arity
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input.val selection arity) targetRels)
    (binderWitness : MappedBinderWitness input.val selection arity
      sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact selection.val.anchor)
    (targetExact : targetContext.Exact selection.val.anchor.castSucc)
    (sourceBindersCover : sourceBinders.Covers selection.val.anchor)
    (targetBindersCover : targetBinders.Covers selection.val.anchor.castSucc)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input.val sourceBinders
        selection.val.anchor)
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        (vacuousIntroRaw input.val selection arity) targetBinders
        selection.val.anchor.castSucc)
    (recurseAt : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders :
        ConcreteElaboration.BinderContext input.val childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (vacuousIntroRaw input.val selection arity) childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : ConcreteElaboration.WireContext input.val)
      (childTargetContext : ConcreteElaboration.WireContext
        (vacuousIntroRaw input.val selection arity))
      (childContext : LiftedContextWitness input.val selection arity
        childSourceContext childTargetContext),
      True → True →
      (childBinderWitness : MappedBinderWitness input.val selection arity
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child.castSucc →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (vacuousIntroRaw input.val selection arity) childTargetBinders
        child.castSucc →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend child.castSucc).Exact child.castSucc →
      ∀ (sourceBody : Region signature childSourceContext.length
          childSourceRels)
        (targetBody : Region signature childTargetContext.length
          childTargetRels),
      ConcreteElaboration.compileRegion? signature input.val fuelSource child
          childSourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (vacuousIntroRaw input.val selection arity) childFuelTarget
          child.castSucc childTargetContext childTargetBinders =
        some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap) targetBody)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuelSource)
        sourceContext sourceBinders
        (ConcreteElaboration.localOccurrences input.val
          selection.val.anchor) = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (vacuousIntroRaw input.val selection arity)
        (ConcreteElaboration.compileRegion? signature
          (vacuousIntroRaw input.val selection arity) fuelTarget)
        targetContext targetBinders
        (ConcreteElaboration.localOccurrences
          (vacuousIntroRaw input.val selection arity)
          selection.val.anchor.castSucc) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      context.indexRelation
      (sourceItems.renameRelations binderWitness.relationMap) targetItems := by
  rw [anchor_localOccurrences] at targetCompiled
  obtain ⟨keptTargetItems, bubbleTargetItems, keptTargetCompiled,
      bubbleTargetCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (d := vacuousIntroRaw input.val selection arity)
      (signature := signature)
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (vacuousIntroRaw input.val selection arity) fuelTarget)
      targetContext targetBinders
      ((ModalSoundness.keptOccurrences input.val selection).map
        (liftOccurrence input.val))
      [ConcreteElaboration.LocalOccurrence.child (bubbleRegion input.val)]
      targetItems targetCompiled
  rw [targetItemsEq]
  simp only [ConcreteElaboration.compileOccurrencesWith?] at bubbleTargetCompiled
  simp only [ConcreteElaboration.compileOccurrenceWith?,
    vacuousIntroRaw_bubble] at bubbleTargetCompiled
  cases bubbleResult :
      ConcreteElaboration.compileRegion? signature
        (vacuousIntroRaw input.val selection arity) fuelTarget
        (bubbleRegion input.val) targetContext
        (targetBinders.push (bubbleRegion input.val) arity) with
  | none => simp [bubbleResult] at bubbleTargetCompiled
  | some bubbleBody =>
      simp [bubbleResult] at bubbleTargetCompiled
      subst bubbleTargetItems
      cases fuelTarget with
      | zero =>
          simp [ConcreteElaboration.compileRegion?] at bubbleResult
      | succ bubbleFuel =>
          simp only [ConcreteElaboration.compileRegion?] at bubbleResult
          rw [bubble_localOccurrences] at bubbleResult
          obtain ⟨selectedTargetItems, selectedTargetCompiled, bubbleBodyEq⟩ :=
            Option.bind_eq_some_iff.mp bubbleResult
          have bubbleBodyEq' :
              ConcreteElaboration.finishRegion
                  (vacuousIntroRaw input.val selection arity) targetContext
                  (bubbleRegion input.val) selectedTargetItems = bubbleBody :=
            Option.some.inj bubbleBodyEq
          subst bubbleBody
          let sourceRecurse :
              ∀ {rels : RelCtx},
                (child : Fin input.val.regionCount) →
                (childContext : ConcreteElaboration.WireContext input.val) →
                ConcreteElaboration.BinderContext input.val rels →
                Option (Region signature childContext.length rels) :=
            fun {rels} => ConcreteElaboration.compileRegion? signature
              input.val fuelSource
          obtain ⟨partitionSourceItems, partitionSourceCompiled⟩ :=
            ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
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
            ConcreteElaboration.compileOccurrencesWith?_append_split
              sourceRecurse sourceContext sourceBinders
              (ModalSoundness.keptOccurrences input.val selection)
              (ModalSoundness.selectedOccurrences input.val selection)
              partitionSourceItems partitionSourceCompiled
          have keptPointwise :
              ∀ occurrence,
                occurrence ∈ ModalSoundness.keptOccurrences input.val selection →
                ∀ (sourceItem : Item signature sourceContext.length sourceRels)
                  (targetItem : Item signature targetContext.length targetRels),
                ConcreteElaboration.compileOccurrenceWith? signature input.val
                    sourceRecurse sourceContext sourceBinders occurrence =
                  some sourceItem →
                ConcreteElaboration.compileOccurrenceWith? signature
                    (vacuousIntroRaw input.val selection arity)
                    (ConcreteElaboration.compileRegion? signature
                      (vacuousIntroRaw input.val selection arity)
                      (bubbleFuel + 1))
                    targetContext targetBinders
                    (liftOccurrence input.val occurrence) = some targetItem →
                ConcreteElaboration.ItemSimulation model named direction
                  context.indexRelation
                  (sourceItem.renameRelations binderWitness.relationMap)
                  targetItem := by
            intro occurrence keptMember sourceItem targetItem
              sourceOccurrenceCompiled targetOccurrenceCompiled
            have filteredMember := keptMember
            rw [ModalSoundness.keptOccurrences] at filteredMember
            have sourceMember := (List.mem_filter.mp filteredMember).1
            apply compileOccurrence_itemSimulation input.val selection arity
              input.property targetWellFormed model named direction fuelSource
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
            ConcreteElaboration.BinderContext.push_covers_bubble_child
              targetBindersCover
              (vacuousIntroRaw_bubble input.val selection arity)
          have targetBubbleEnumeration :=
            targetEnumeration.bubbleChild targetWellFormed
              (vacuousIntroRaw_bubble input.val selection arity)
          have targetBubbleContextEq :
              targetContext.extend (bubbleRegion input.val) = targetContext := by
            unfold ConcreteElaboration.WireContext.extend
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
                ∀ (sourceItem : Item signature sourceContext.length sourceRels)
                  (targetItem : Item signature
                    (targetContext.extend (bubbleRegion input.val)).length
                    (arity :: targetRels)),
                ConcreteElaboration.compileOccurrenceWith? signature input.val
                    sourceRecurse sourceContext sourceBinders occurrence =
                  some sourceItem →
                ConcreteElaboration.compileOccurrenceWith? signature
                    (vacuousIntroRaw input.val selection arity)
                    (ConcreteElaboration.compileRegion? signature
                      (vacuousIntroRaw input.val selection arity) bubbleFuel)
                    (targetContext.extend (bubbleRegion input.val))
                    (targetBinders.push (bubbleRegion input.val) arity)
                    (liftOccurrence input.val occurrence) = some targetItem →
                ConcreteElaboration.ItemSimulation model named direction
                  selectedContextWitness.indexRelation
                  (sourceItem.renameRelations bubbleBinderWitness.relationMap)
                  targetItem := by
            intro occurrence selectedMember sourceItem targetItem
              sourceOccurrenceCompiled targetOccurrenceCompiled
            have filteredMember := selectedMember
            rw [ModalSoundness.selectedOccurrences] at filteredMember
            have sourceMember := (List.mem_filter.mp filteredMember).1
            apply compileOccurrence_itemSimulation input.val selection arity
              input.property targetWellFormed model named direction fuelSource
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
            ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model named direction sourceRecurse
              (ConcreteElaboration.compileRegion? signature
                (vacuousIntroRaw input.val selection arity) (bubbleFuel + 1))
              sourceContext targetContext sourceBinders targetBinders
              context.indexRelation binderWitness.relationMap
              (liftOccurrence input.val)
              (ModalSoundness.keptOccurrences input.val selection)
              keptPointwise keptSourceItems keptTargetItems keptSourceCompiled
              keptTargetCompiled
          have selectedSimulation :=
            ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
              model named direction sourceRecurse
              (ConcreteElaboration.compileRegion? signature
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
              denoteItemSeq model named sourceEnv sourceRelEnv sourceItems ↔
                (denoteItemSeq model named sourceEnv sourceRelEnv
                    keptSourceItems ∧
                  denoteItemSeq model named sourceEnv sourceRelEnv
                    selectedSourceItems) := by
            have permutation :=
              ModalSoundness.compileOccurrences_denote_perm input.val
                sourceRecurse sourceContext sourceBinders
                (anchorOccurrences_perm_partition input.val selection).symm
                sourceCompiled partitionSourceCompiled model named sourceEnv
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
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
              ConcreteElaboration.ContextIndexRelation.forwardMap
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
              denoteItem model named targetEnv targetRelEnv
                  (.bubble arity
                    (ConcreteElaboration.finishRegion
                      (vacuousIntroRaw input.val selection arity) targetContext
                      (bubbleRegion input.val) selectedTargetItems)) ↔
                ∃ fresh : Relation model.Carrier arity,
                  denoteItemSeq (relCtx := arity :: targetRels) model named
                    (selectedTargetEnv targetEnv)
                    (fresh, targetRelEnv) selectedTargetItems := by
            rw [bubbleItem_denote input.val selection arity targetContext
              selectedTargetItems model named targetEnv targetRelEnv]
            apply exists_congr
            intro fresh
            rw [ItemSeq.castWiresEq_eq_renameWires,
              denoteItemSeq_renameWires]
            apply iff_of_eq
            apply congrArg (fun environment =>
              denoteItemSeq (relCtx := arity :: targetRels) model named
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
              denoteItemSeq model named sourceEnv targetRelEnv
                  (sourceItems.renameRelations binderWitness.relationMap) ↔
                denoteItemSeq model named sourceEnv sourceRelEnv sourceItems :=
            denoteItemSeq_renameRelations model named binderWitness.relationMap
              sourceRelEnv targetRelEnv baseAgrees sourceEnv sourceItems
          have keptRename :
              denoteItemSeq model named sourceEnv targetRelEnv
                  (keptSourceItems.renameRelations binderWitness.relationMap) ↔
                denoteItemSeq model named sourceEnv sourceRelEnv
                  keptSourceItems :=
            denoteItemSeq_renameRelations model named binderWitness.relationMap
              sourceRelEnv targetRelEnv baseAgrees sourceEnv keptSourceItems
          have selectedRename (fresh : Relation model.Carrier arity) :
              denoteItemSeq (relCtx := arity :: targetRels) model named
                  sourceEnv (fresh, targetRelEnv)
                  (selectedSourceItems.renameRelations
                    bubbleBinderWitness.relationMap) ↔
                denoteItemSeq model named sourceEnv sourceRelEnv
                  selectedSourceItems :=
            denoteItemSeq_renameRelations model named
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
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (context : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceItems : ItemSeq signature
      (sourceContext.extend region).length rels)
    (targetItems : ItemSeq signature
      (targetContext.extend region.castSucc).length rels)
    (itemSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction (context.extend region).indexRelation sourceItems targetItems) :
    ∀ relEnv,
      ConcreteElaboration.DirectionalLocalTransport direction
        sourceContext targetContext region region.castSucc
        context.indexRelation model named relEnv sourceItems targetItems := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  let extendedWitness :=
    LiftedContextWitness.extend
      (input := input) (selection := selection) (arity := arity)
      (⟨rfl⟩ : LiftedContextWitness input selection arity
        sourceContext sourceContext) region
  intro relEnv
  apply ConcreteElaboration.directionalLocalTransport_of_agreement
    (source := input) (target := vacuousIntroRaw input selection arity)
    direction sourceContext sourceContext region region.castSucc
    (ConcreteElaboration.ContextIndexRelation.forwardMap id)
    extendedWitness.indexRelation model named sourceItems targetItems
  · intro sourceOuter targetOuter outerAgrees
    have outerEq : sourceOuter = targetOuter := by
      simpa only [
        ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
        Function.comp_id] using outerAgrees
    cases direction with
    | forward =>
        intro sourceLocal
        let localCountEq :
            (ConcreteElaboration.exactScopeWires
              (vacuousIntroRaw input selection arity) region.castSucc).length =
              (ConcreteElaboration.exactScopeWires input region).length :=
          congrArg List.length
            (vacuousIntroRaw_exactScopeWires input selection arity region)
        let targetLocal : Fin
            (ConcreteElaboration.exactScopeWires
              (vacuousIntroRaw input selection arity)
              region.castSucc).length → model.Carrier :=
          fun index => sourceLocal (Fin.cast localCountEq index)
        refine ⟨targetLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          ConcreteElaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        subst targetOuter
        simp only [ConcreteElaboration.extendedEnvironment, targetLocal,
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
            (ConcreteElaboration.exactScopeWires
              (vacuousIntroRaw input selection arity) region.castSucc).length =
              (ConcreteElaboration.exactScopeWires input region).length :=
          congrArg List.length
            (vacuousIntroRaw_exactScopeWires input selection arity region)
        let sourceLocal :
            Fin (ConcreteElaboration.exactScopeWires input region).length →
              model.Carrier :=
          fun index => targetLocal (Fin.cast localCountEq.symm index)
        refine ⟨sourceLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          ConcreteElaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        subst targetOuter
        simp only [ConcreteElaboration.extendedEnvironment, sourceLocal,
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
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw input.val selection arity).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      (vacuousIntroRaw input.val selection arity) model named where
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
    relationMap := ConcreteElaboration.identityRelationRenaming []
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
    exact localTransport_of_itemSimulation input.val selection arity model named
      direction sourceContext targetContext context region
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    have targetNodeEq : targetNode = sourceNode :=
      ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    apply compileNode_itemSimulation input.val selection arity model named
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
      model named direction fuelSource fuelTarget
      (sourceContext.extend selection.val.anchor)
      (targetContext.extend selection.val.anchor.castSucc) extendedContext
      sourceBinders targetBinders binderWitness sourceExact targetExact
      sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
      recurseAt sourceItems targetItems sourceCompiled targetCompiled
    rw [ConcreteElaboration.finishRegion_renameRelations sourceContext
      selection.val.anchor binderWitness.relationMap sourceItems]
    apply ConcreteElaboration.finishRegion_denote
      (source := input.val)
      (target := vacuousIntroRaw input.val selection arity)
      direction sourceContext targetContext selection.val.anchor
      selection.val.anchor.castSucc context.indexRelation model named
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
    exact localTransport_of_itemSimulation input.val selection arity model named
      direction sourceContext targetContext context selection.val.anchor
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
      itemSemantics

end VisualProof.Rule.VacuousSoundness
