import VisualProof.Rule.Soundness.Comprehension.InstantiationForwardEnvironment

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A denoting quotient-host survivor conjunction supplies the fixed moving
relation at the current atom's ordered argument vector. -/
theorem coalesced_survivor_items_entail_fixedRelation
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
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
    (model : Model)
    (quotientWireValue : Fin
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    (fuel : Nat)
    (context : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (binderContext : Concrete.Elaboration.BinderContext
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
    (items : ItemSeq  context.length rels)
    (compiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) fuel)
      context binderContext
      ((Concrete.Elaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some items)
    (denotes : denoteItemSeq model  environment relEnv items) :
    relationValue (fun index => quotientWireValue
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).quotientWire (arguments index))) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let occurrences :=
    (Concrete.Elaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  have coalescedNode : coalesced.diagram.val.nodes atom =
      .atom site coalesced.bubble := by
    simpa [coalesced, coalescedInstantiationState, spliceInput] using node_eq
  have localMember : Concrete.Elaboration.LocalOccurrence.node atom ∈
      Concrete.Elaboration.localOccurrences coalesced.diagram.val site := by
    apply (Concrete.Elaboration.mem_localOccurrences_node _ _ _).2
    simpa using congrArg CNode.region coalescedNode
  have coalescedPending : coalesced.pendingAtoms = atom :: tail := by
    simpa [coalesced] using pending_eq
  have coalescedOwnedNodup : coalesced.ownedAtoms.Nodup := by
    simpa [InstantiationState.ownedAtoms, coalesced] using ownedNodup
  have survives : dropOccurrenceSurvives coalesced (.node atom) = true :=
    step_atom_survives coalesced atom tail coalescedPending coalescedOwnedNodup
  have member : Concrete.Elaboration.LocalOccurrence.node atom ∈ occurrences :=
    List.mem_filter.mpr ⟨localMember, survives⟩
  obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete member
  have occurrenceEq : occurrences.get occurrenceIndex = .node atom :=
    indexOf?_sound occurrenceIndexEq
  let itemIndex := Fin.cast
    (Concrete.Elaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion?  coalesced fuel) context binderContext
      compiled).symm occurrenceIndex
  have atIndex := Concrete.Elaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion?  coalesced fuel) context binderContext
    compiled occurrenceIndex
  have atAtom : Concrete.Elaboration.compileOccurrenceWith?
      coalesced.diagram.val (compileSurvivorRegion?  coalesced fuel)
      context binderContext (.node atom) = some (items.get itemIndex) := by
    rw [← occurrenceEq]
    simpa [occurrences, itemIndex] using atIndex
  have atomCompiled : Concrete.Elaboration.compileNode?
      spliceInput.coalesceFrameRaw context binderContext atom =
        some (items.get itemIndex) := by
    simpa [coalesced, spliceInput,
      Concrete.Elaboration.compileOccurrenceWith?] using atAtom
  have atomDenotes : denoteItem model  environment relEnv
      (items.get itemIndex) :=
    (denoteItemSeq_iff_get model  environment relEnv items).mp denotes
      itemIndex
  exact (coalesced_compiled_atom_iff_fixedRelation comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hadmissible
    model  quotientWireValue relationValue context binderContext relEnv
    fixed relation lookup environment environment_eq (items.get itemIndex)
    atomCompiled).mp atomDenotes

/-- Recursive child occurrences at the distinguished splice site transport
forward under the trace's fixed moving relation and proxy family. -/
theorem advance_site_child_denotes_fixed_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
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
    (sourceContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact parentRegion)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion parentRegion))
    (sourceBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers parentRegion)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion parentRegion))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders parentRegion)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
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
    (model : Model)
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
      state.diagram.val.Encloses state.bubble child →
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model  relationValue
        values parameterValues direction sourceFuel targetFuel child)
    (child : Fin state.diagram.val.regionCount)
    (member : Concrete.Elaboration.LocalOccurrence.child child ∈
      (Concrete.Elaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val parentRegion).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders
            payload state site arguments hadmissible)))
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapFrameOccurrence (.child child)) =
        some targetItem)
    (sourceDenotes : denoteItem model  sourceEnv
      (RelEnv.pullback relationMap targetRelEnv) sourceItem) :
    denoteItem model  targetEnv targetRelEnv targetItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  have childParent :=
    (Concrete.Elaboration.mem_localOccurrences_child _ _ _).1
      (List.mem_filter.mp member).1
  have stateChildParent' :
      (state.diagram.val.regions child).parent? = some parentRegion := by
    simpa [coalesced, coalescedInstantiationState, spliceInput,
      Concrete.Splice.Input.coalesceFrameRaw_regions, CRegion.parent?] using childParent
  have parentEnclosesChild :
      state.diagram.val.Encloses parentRegion child := by
    have hpositive := child.isLt
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp [Concrete.Diagram.climb, stateChildParent']
  have bubbleEnclosesChild :
      state.diagram.val.Encloses state.bubble child :=
    Concrete.Elaboration.checked_encloses_trans state.diagram.property
      bubbleEnclosesParent parentEnclosesChild
  cases childKind : coalesced.diagram.val.regions child with
  | sheet =>
      have frameKind : spliceInput.frame.val.regions child = .sheet := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Concrete.Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      simp [Concrete.Elaboration.compileOccurrenceWith?, frameKind]
        at sourceCompiled
  | cut parent =>
      have parentEq : parent = parentRegion := by
        rw [childKind] at childParent
        exact Option.some.inj childParent
      subst parent
      have frameKind : spliceInput.frame.val.regions child =
          .cut parentRegion := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Concrete.Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_cut child parentRegion (by
        simpa [coalesced, coalescedInstantiationState, spliceInput] using
          childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      simp [Concrete.Elaboration.compileOccurrenceWith?, frameKind]
        at sourceCompiled
      change (compileSurvivorRegion?  coalesced sourceFuel child
          sourceContext sourceBinders).bind (fun body => some (.cut body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion?  coalesced
          sourceFuel child sourceContext sourceBinders with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Concrete.Splice.Input.PlugLayout.mapFrameOccurrence,
            Concrete.Elaboration.compileOccurrenceWith?, targetKindExplicit]
            at targetCompiled
          change (compileSurvivorRegion?  next targetFuel
              (layout.frameRegion child) targetContext targetBinders).bind
              (fun body => some (.cut body)) = some targetItem at targetCompiled
          cases targetChildResult : compileSurvivorRegion?  next
              targetFuel (layout.frameRegion child) targetContext targetBinders with
          | none =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
          | some targetChild =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
              subst targetItem
              have simulation := childSimulation .backward child
                bubbleEnclosesChild sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed  spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourceBinders targetBinders
                (Concrete.Elaboration.BinderContext.covers_cut_child sourceCover
                  childKind)
                (Concrete.Elaboration.BinderContext.covers_cut_child targetCover
                  targetKind)
                (sourceEnumeration.cutChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.cutChild
                  (layout.plugRaw_wellFormed  spliceInput hadmissible)
                  targetKind)
                wireMap wireSpec relationMap
                (layout.frameRelationLookup_cutChild hadmissible parentRegion child
                  sourceBinders targetBinders sourceEnumeration childKind
                  relationMap relationSpec)
                sourceChild targetChild sourceChildResult targetChildResult
                sourceEnv targetEnv targetRelEnv (by simpa using environmentEq)
                targetFixed targetProxies targetParameters
              change ¬ denoteRegion model  sourceEnv
                (RelEnv.pullback relationMap targetRelEnv) sourceChild
                at sourceDenotes
              change ¬ denoteRegion model  targetEnv targetRelEnv
                targetChild
              intro targetDenotes
              apply sourceDenotes
              have sourceRenamed := simulation targetDenotes
              exact (denoteRegion_renameRelations model  relationMap
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
          Concrete.Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_bubble child parentRegion
        arity (by simpa [coalesced, coalescedInstantiationState, spliceInput]
          using childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push (layout.frameRegion child) arity
      simp [Concrete.Elaboration.compileOccurrenceWith?, frameKind,
        sourcePushed] at sourceCompiled
      change (compileSurvivorRegion?  coalesced sourceFuel child
          sourceContext sourcePushed).bind (fun body => some (.bubble arity body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion?  coalesced
          sourceFuel child sourceContext sourcePushed with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Concrete.Splice.Input.PlugLayout.mapFrameOccurrence,
            Concrete.Elaboration.compileOccurrenceWith?, targetKindExplicit,
            targetPushed] at targetCompiled
          change (compileSurvivorRegion?  next targetFuel
              (layout.frameRegion child) targetContext targetPushed).bind
              (fun body => some (.bubble arity body)) = some targetItem
            at targetCompiled
          cases targetChildResult : compileSurvivorRegion?  next
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
                  Concrete.Splice.Input.coalesceFrameRaw_regions, CRegion.parent?] using
                    childParent
              have bubbleNeChild : state.bubble ≠ child := by
                intro equality
                subst child
                exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent bubbleEnclosesParent
              have targetsNeChild : ∀ index,
                  state.binderTargets index ≠ child := by
                intro index equality
                subst child
                have targetEnclosesSite :=
                  Concrete.Elaboration.checked_encloses_trans
                    state.diagram.property (targets.target_encloses index)
                    bubbleEnclosesParent
                exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent targetEnclosesSite
              change ∃ childRelation : Relation model.Carrier arity,
                denoteRegion (relCtx := arity :: sourceRels) model  sourceEnv
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
              have simulation := childSimulation .forward child
                bubbleEnclosesChild sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed  spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourcePushed targetPushed
                (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                  sourceCover childKind)
                (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                  targetCover targetKind)
                (sourceEnumeration.bubbleChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.bubbleChild
                  (layout.plugRaw_wellFormed  spliceInput hadmissible)
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
              exact (denoteRegion_renameRelations model
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
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (sourceFuel targetFuel : Nat)
    (sourceContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (model : Model)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (sourceItems : ItemSeq  sourceContext.length sourceRels)
    (targetItems : ItemSeq  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders
      ((Concrete.Elaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((Concrete.Elaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (sourceDenotes : denoteItemSeq model  sourceEnv sourceRelEnv sourceItems)
    (frameDenotes : ∀
      (occurrence : Concrete.Elaboration.LocalOccurrence
        state.diagram.val.regionCount state.diagram.val.nodeCount)
      (member : occurrence ∈
        (Concrete.Elaboration.localOccurrences
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible).diagram.val site).filter
          (dropOccurrenceSurvives
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible)))
      (notCurrent : occurrence ≠ .node atom)
      (sourceItem : Item  sourceContext.length sourceRels)
      (targetItem : Item  targetContext.length targetRels),
      Concrete.Elaboration.compileOccurrenceWith?
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          (compileSurvivorRegion?
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible) sourceFuel)
          sourceContext sourceBinders occurrence = some sourceItem →
      Concrete.Elaboration.compileOccurrenceWith?
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion?
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapFrameOccurrence occurrence) =
            some targetItem →
      denoteItem model  sourceEnv sourceRelEnv sourceItem →
      denoteItem model  targetEnv targetRelEnv targetItem)
    (patternDenotes : ∀
      (occurrence : Concrete.Elaboration.LocalOccurrence
        comprehension.val.diagram.regionCount
        comprehension.val.diagram.nodeCount)
      (member : occurrence ∈ Concrete.Elaboration.localOccurrences
        comprehension.val.diagram payload.binderSpine.bodyContainer)
      (targetItem : Item  targetContext.length targetRels),
      Concrete.Elaboration.compileOccurrenceWith?
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion?
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapPatternOccurrence occurrence) =
            some targetItem →
      denoteItem model  targetEnv targetRelEnv targetItem) :
    denoteItemSeq model  targetEnv targetRelEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceOccurrences :=
    (Concrete.Elaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  let targetOccurrences :=
    (Concrete.Elaboration.localOccurrences next.diagram.val
      (layout.frameRegion site)).filter (dropOccurrenceSurvives next)
  apply (denoteItemSeq_iff_get model  targetEnv targetRelEnv targetItems).2
  intro targetItemIndex
  let targetOccurrenceIndex := Fin.cast
    (Concrete.Elaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion?  next targetFuel) targetContext
      targetBinders targetCompiled) targetItemIndex
  generalize occurrenceEq : targetOccurrences.get targetOccurrenceIndex =
    targetOccurrence
  have targetOccurrenceMember : targetOccurrence ∈ targetOccurrences :=
    occurrenceEq ▸ List.get_mem targetOccurrences targetOccurrenceIndex
  have targetAt := Concrete.Elaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion?  next targetFuel) targetContext
    targetBinders targetCompiled targetOccurrenceIndex
  have targetAt' : Concrete.Elaboration.compileOccurrenceWith?
      next.diagram.val (compileSurvivorRegion?  next targetFuel)
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
        (Concrete.Elaboration.compileOccurrencesWith?_length
          (compileSurvivorRegion?  coalesced sourceFuel) sourceContext
          sourceBinders sourceCompiled).symm sourceOccurrenceIndex
      have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
        (compileSurvivorRegion?  coalesced sourceFuel) sourceContext
        sourceBinders sourceCompiled sourceOccurrenceIndex
      have sourceAt' : Concrete.Elaboration.compileOccurrenceWith?
          spliceInput.coalesceFrameRaw
          (compileSurvivorRegion?  coalesced sourceFuel)
          sourceContext sourceBinders sourceOccurrence =
            some (sourceItems.get sourceItemIndex) := by
        rw [← sourceOccurrenceEq]
        simpa [sourceOccurrences, coalesced, spliceInput, sourceItemIndex]
          using sourceAt
      have sourceItemDenotes : denoteItem model  sourceEnv sourceRelEnv
          (sourceItems.get sourceItemIndex) :=
        (denoteItemSeq_iff_get model  sourceEnv sourceRelEnv sourceItems).mp
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
