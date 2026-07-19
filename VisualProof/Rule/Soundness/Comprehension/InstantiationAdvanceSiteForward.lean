import VisualProof.Rule.Soundness.Comprehension.InstantiationForwardEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A denoting quotient-host survivor conjunction supplies the fixed moving
relation at the current atom's ordered argument vector. -/
theorem coalesced_survivor_items_entail_fixedRelation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (quotientWireValue : Fin
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (binderContext : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = quotientWireValue (context.get index))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) fuel)
      context binderContext
      ((ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some items)
    (denotes : denoteItemSeq model named environment relEnv items) :
    relationValue (fun index => quotientWireValue
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).quotientWire (arguments index))) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let occurrences :=
    (ConcreteElaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  have coalescedNode : coalesced.diagram.val.nodes atom =
      .atom site coalesced.bubble := by
    simpa [coalesced, coalescedInstantiationState, spliceInput] using node_eq
  have localMember : ConcreteElaboration.LocalOccurrence.node atom ∈
      ConcreteElaboration.localOccurrences coalesced.diagram.val site := by
    apply (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
    simpa using congrArg CNode.region coalescedNode
  have coalescedPending : coalesced.pendingAtoms = atom :: tail := by
    simpa [coalesced] using pending_eq
  have coalescedOwnedNodup : coalesced.ownedAtoms.Nodup := by
    simpa [InstantiationState.ownedAtoms, coalesced] using ownedNodup
  have survives : dropOccurrenceSurvives coalesced (.node atom) = true :=
    step_atom_survives coalesced atom tail coalescedPending coalescedOwnedNodup
  have member : ConcreteElaboration.LocalOccurrence.node atom ∈ occurrences :=
    List.mem_filter.mpr ⟨localMember, survives⟩
  obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete member
  have occurrenceEq : occurrences.get occurrenceIndex = .node atom :=
    indexOf?_sound occurrenceIndexEq
  let itemIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature coalesced fuel) context binderContext
      compiled).symm occurrenceIndex
  have atIndex := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature coalesced fuel) context binderContext
    compiled occurrenceIndex
  have atAtom : ConcreteElaboration.compileOccurrenceWith? signature
      coalesced.diagram.val (compileSurvivorRegion? signature coalesced fuel)
      context binderContext (.node atom) = some (items.get itemIndex) := by
    rw [← occurrenceEq]
    simpa [occurrences, itemIndex] using atIndex
  have atomCompiled : ConcreteElaboration.compileNode? signature
      spliceInput.coalesceFrameRaw context binderContext atom =
        some (items.get itemIndex) := by
    simpa [coalesced, spliceInput,
      ConcreteElaboration.compileOccurrenceWith?] using atAtom
  have atomDenotes : denoteItem model named environment relEnv
      (items.get itemIndex) :=
    (denoteItemSeq_iff_get model named environment relEnv items).mp denotes
      itemIndex
  exact (coalesced_compiled_atom_iff_fixedRelation comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hadmissible
    model named quotientWireValue relationValue context binderContext relEnv
    fixed relation lookup environment environment_eq (items.get itemIndex)
    atomCompiled).mp atomDenotes

/-- Recursive child occurrences at the distinguished splice site transport
forward under the trace's fixed moving relation and proxy family. -/
theorem advance_site_child_denotes_fixed_forward
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (targets : BinderTargetsAtBubble payload state)
    (sourceFuel targetFuel : Nat)
    (parentRegion : Fin state.diagram.val.regionCount)
    (bubbleEnclosesParent : state.diagram.val.Encloses state.bubble parentRegion)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact parentRegion)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion parentRegion))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers parentRegion)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion parentRegion))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders parentRegion)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion parentRegion))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue targetBinders targetRelEnv)
    (targetProxies : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetBinders targetRelEnv values)
    (targetParameters : ParameterValuesAt
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetContext targetEnv parameterValues)
    (childSimulation : ∀ direction
      (child : Fin state.diagram.val.regionCount),
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues direction sourceFuel targetFuel child)
    (child : Fin state.diagram.val.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      (ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val parentRegion).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders
            payload state site arguments hadmissible)))
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapFrameOccurrence (.child child)) =
        some targetItem)
    (sourceDenotes : denoteItem model named sourceEnv
      (RelEnv.pullback relationMap targetRelEnv) sourceItem) :
    denoteItem model named targetEnv targetRelEnv targetItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  have childParent :=
    (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
      (List.mem_filter.mp member).1
  cases childKind : coalesced.diagram.val.regions child with
  | sheet =>
      have frameKind : spliceInput.frame.val.regions child = .sheet := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind]
        at sourceCompiled
  | cut parent =>
      have parentEq : parent = parentRegion := by
        rw [childKind] at childParent
        exact Option.some.inj childParent
      subst parent
      have frameKind : spliceInput.frame.val.regions child =
          .cut parentRegion := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_cut child parentRegion (by
        simpa [coalesced, coalescedInstantiationState, spliceInput] using
          childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind]
        at sourceCompiled
      change (compileSurvivorRegion? signature coalesced sourceFuel child
          sourceContext sourceBinders).bind (fun body => some (.cut body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion? signature coalesced
          sourceFuel child sourceContext sourceBinders with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?, targetKindExplicit]
            at targetCompiled
          change (compileSurvivorRegion? signature next targetFuel
              (layout.frameRegion child) targetContext targetBinders).bind
              (fun body => some (.cut body)) = some targetItem at targetCompiled
          cases targetChildResult : compileSurvivorRegion? signature next
              targetFuel (layout.frameRegion child) targetContext targetBinders with
          | none =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
          | some targetChild =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
              subst targetItem
              have simulation := childSimulation .backward child sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourceBinders targetBinders
                (ConcreteElaboration.BinderContext.covers_cut_child sourceCover
                  childKind)
                (ConcreteElaboration.BinderContext.covers_cut_child targetCover
                  targetKind)
                (sourceEnumeration.cutChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.cutChild
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  targetKind)
                wireMap wireSpec relationMap
                (layout.frameRelationLookup_cutChild hadmissible parentRegion child
                  sourceBinders targetBinders sourceEnumeration childKind
                  relationMap relationSpec)
                sourceChild targetChild sourceChildResult targetChildResult
                sourceEnv targetEnv targetRelEnv (by simpa using environmentEq)
                targetFixed targetProxies targetParameters
              change ¬ denoteRegion model named sourceEnv
                (RelEnv.pullback relationMap targetRelEnv) sourceChild
                at sourceDenotes
              change ¬ denoteRegion model named targetEnv targetRelEnv
                targetChild
              intro targetDenotes
              apply sourceDenotes
              have sourceRenamed := simulation targetDenotes
              exact (denoteRegion_renameRelations model named relationMap
                (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                (RelEnv.pullback_agrees relationMap targetRelEnv) sourceEnv
                sourceChild).mp sourceRenamed
  | bubble parent arity =>
      have parentEq : parent = parentRegion := by
        rw [childKind] at childParent
        exact Option.some.inj childParent
      subst parent
      have frameKind : spliceInput.frame.val.regions child =
          .bubble parentRegion arity := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_bubble child parentRegion
        arity (by simpa [coalesced, coalescedInstantiationState, spliceInput]
          using childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push (layout.frameRegion child) arity
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind,
        sourcePushed] at sourceCompiled
      change (compileSurvivorRegion? signature coalesced sourceFuel child
          sourceContext sourcePushed).bind (fun body => some (.bubble arity body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion? signature coalesced
          sourceFuel child sourceContext sourcePushed with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?, targetKindExplicit,
            targetPushed] at targetCompiled
          change (compileSurvivorRegion? signature next targetFuel
              (layout.frameRegion child) targetContext targetPushed).bind
              (fun body => some (.bubble arity body)) = some targetItem
            at targetCompiled
          cases targetChildResult : compileSurvivorRegion? signature next
              targetFuel (layout.frameRegion child) targetContext targetPushed with
          | none =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
          | some targetChild =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
              subst targetItem
              have stateChildParent :
                  (state.diagram.val.regions child).parent? =
                    some parentRegion := by
                simpa [coalesced, coalescedInstantiationState, spliceInput,
                  Splice.Input.coalesceFrameRaw_regions, CRegion.parent?] using
                    childParent
              have bubbleNeChild : state.bubble ≠ child := by
                intro equality
                subst child
                exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent bubbleEnclosesParent
              have targetsNeChild : ∀ index,
                  state.binderTargets index ≠ child := by
                intro index equality
                subst child
                have targetEnclosesSite :=
                  ConcreteElaboration.checked_encloses_trans
                    state.diagram.property (targets.target_encloses index)
                    bubbleEnclosesParent
                exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent targetEnclosesSite
              change ∃ childRelation : Relation model.Carrier arity,
                denoteRegion (relCtx := arity :: sourceRels) model named sourceEnv
                  (childRelation, RelEnv.pullback relationMap targetRelEnv)
                  sourceChild at sourceDenotes
              obtain ⟨childRelation, sourceChildDenotes⟩ := sourceDenotes
              have nextBubbleNe :
                  next.bubble ≠ layout.frameRegion child := by
                intro equality
                change layout.frameRegion state.bubble =
                  layout.frameRegion child at equality
                exact bubbleNeChild (layout.frameRegion_injective equality)
              have nextTargetsNe : ∀ index,
                  next.binderTargets index ≠ layout.frameRegion child := by
                intro index equality
                change layout.frameRegion (state.binderTargets index) =
                  layout.frameRegion child at equality
                exact targetsNeChild index
                  (layout.frameRegion_injective equality)
              have childFixed := fixedRelationAt_push_other payload next
                relationValue targetBinders targetRelEnv targetFixed
                (layout.frameRegion child) arity childRelation nextBubbleNe
              have childProxies := ProxyRelationsAt.push_other payload next
                targetBinders targetRelEnv values targetProxies
                (layout.frameRegion child) arity childRelation nextTargetsNe
              have simulation := childSimulation .forward child sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourcePushed targetPushed
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceCover childKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetCover targetKind)
                (sourceEnumeration.bubbleChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.bubbleChild
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  targetKind)
                wireMap wireSpec (RelationRenaming.lift relationMap arity)
                (layout.frameRelationLookup_bubbleChild hadmissible parentRegion
                  child sourceBinders targetBinders sourceEnumeration arity
                  childKind relationMap relationSpec)
                sourceChild targetChild sourceChildResult targetChildResult
                sourceEnv targetEnv (childRelation, targetRelEnv)
                (by simpa using environmentEq) childFixed childProxies
                targetParameters
              refine ⟨childRelation, ?_⟩
              apply simulation
              exact (denoteRegion_renameRelations model named
                (RelationRenaming.lift relationMap arity)
                (childRelation, RelEnv.pullback relationMap targetRelEnv)
                (childRelation, targetRelEnv)
                (RelEnv.Agrees.lift relationMap
                  (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                  (RelEnv.pullback_agrees relationMap targetRelEnv)
                  childRelation) sourceEnv sourceChild).mpr sourceChildDenotes

/-- Forward semantic assembly for the survivor conjunction at the splice
site.  Every target conjunct is classified by the executor receipt as either
the exact image of a retained non-current frame occurrence or an inserted
pattern occurrence. -/
theorem advance_site_items_denote_forward
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders
      ((ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (sourceDenotes : denoteItemSeq model named sourceEnv sourceRelEnv sourceItems)
    (frameDenotes : ∀
      (occurrence : ConcreteElaboration.LocalOccurrence
        state.diagram.val.regionCount state.diagram.val.nodeCount)
      (member : occurrence ∈
        (ConcreteElaboration.localOccurrences
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible).diagram.val site).filter
          (dropOccurrenceSurvives
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible)))
      (notCurrent : occurrence ≠ .node atom)
      (sourceItem : Item signature sourceContext.length sourceRels)
      (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          (compileSurvivorRegion? signature
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible) sourceFuel)
          sourceContext sourceBinders occurrence = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion? signature
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapFrameOccurrence occurrence) =
            some targetItem →
      denoteItem model named sourceEnv sourceRelEnv sourceItem →
      denoteItem model named targetEnv targetRelEnv targetItem)
    (patternDenotes : ∀
      (occurrence : ConcreteElaboration.LocalOccurrence
        comprehension.val.diagram.regionCount
        comprehension.val.diagram.nodeCount)
      (member : occurrence ∈ ConcreteElaboration.localOccurrences
        comprehension.val.diagram payload.binderSpine.bodyContainer)
      (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion? signature
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapPatternOccurrence occurrence) =
            some targetItem →
      denoteItem model named targetEnv targetRelEnv targetItem) :
    denoteItemSeq model named targetEnv targetRelEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceOccurrences :=
    (ConcreteElaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  let targetOccurrences :=
    (ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion site)).filter (dropOccurrenceSurvives next)
  apply (denoteItemSeq_iff_get model named targetEnv targetRelEnv targetItems).2
  intro targetItemIndex
  let targetOccurrenceIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature next targetFuel) targetContext
      targetBinders targetCompiled) targetItemIndex
  generalize occurrenceEq : targetOccurrences.get targetOccurrenceIndex =
    targetOccurrence
  have targetOccurrenceMember : targetOccurrence ∈ targetOccurrences :=
    occurrenceEq ▸ List.get_mem targetOccurrences targetOccurrenceIndex
  have targetAt := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature next targetFuel) targetContext
    targetBinders targetCompiled targetOccurrenceIndex
  have targetAt' : ConcreteElaboration.compileOccurrenceWith? signature
      next.diagram.val (compileSurvivorRegion? signature next targetFuel)
      targetContext targetBinders targetOccurrence =
        some (targetItems.get targetItemIndex) := by
    rw [← occurrenceEq]
    simpa [targetOccurrences, targetOccurrenceIndex] using targetAt
  have classified := (advance_site_survivor_occurrences_iff comprehension
    attachments binders payload state atom tail site arguments hadmissible
    targetOccurrence).1 targetOccurrenceMember
  cases classified with
  | inl frame =>
      obtain ⟨sourceOccurrence, sourceLocal, sourceSurvives, notCurrent,
        mapped⟩ := frame
      have sourceMember : sourceOccurrence ∈ sourceOccurrences := by
        apply List.mem_filter.mpr
        exact ⟨by simpa [coalesced, coalescedInstantiationState, spliceInput]
          using sourceLocal,
          by simpa [coalesced] using sourceSurvives⟩
      obtain ⟨sourceOccurrenceIndex, sourceIndexEq⟩ :=
        indexOf?_complete sourceMember
      have sourceOccurrenceEq :
          sourceOccurrences.get sourceOccurrenceIndex = sourceOccurrence :=
        indexOf?_sound sourceIndexEq
      let sourceItemIndex := Fin.cast
        (ConcreteElaboration.compileOccurrencesWith?_length
          (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
          sourceBinders sourceCompiled).symm sourceOccurrenceIndex
      have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
        (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
        sourceBinders sourceCompiled sourceOccurrenceIndex
      have sourceAt' : ConcreteElaboration.compileOccurrenceWith? signature
          spliceInput.coalesceFrameRaw
          (compileSurvivorRegion? signature coalesced sourceFuel)
          sourceContext sourceBinders sourceOccurrence =
            some (sourceItems.get sourceItemIndex) := by
        rw [← sourceOccurrenceEq]
        simpa [sourceOccurrences, coalesced, spliceInput, sourceItemIndex]
          using sourceAt
      have sourceItemDenotes : denoteItem model named sourceEnv sourceRelEnv
          (sourceItems.get sourceItemIndex) :=
        (denoteItemSeq_iff_get model named sourceEnv sourceRelEnv sourceItems).mp
          sourceDenotes sourceItemIndex
      have targetAtMapped := targetAt'
      rw [mapped] at targetAtMapped
      exact frameDenotes sourceOccurrence sourceMember notCurrent
        (sourceItems.get sourceItemIndex) (targetItems.get targetItemIndex)
        sourceAt'
        (by simpa [next] using targetAtMapped) sourceItemDenotes
  | inr pattern =>
      obtain ⟨patternOccurrence, patternMember, mapped⟩ := pattern
      have targetAtMapped := targetAt'
      rw [mapped] at targetAtMapped
      exact patternDenotes patternOccurrence patternMember
        (targetItems.get targetItemIndex) (by simpa [next] using targetAtMapped)

end InstantiationSemantic

end VisualProof.Rule
