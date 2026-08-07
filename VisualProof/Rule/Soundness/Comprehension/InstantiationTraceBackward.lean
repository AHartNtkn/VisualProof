import VisualProof.Rule.Soundness.Comprehension.InstantiationDiscrete

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A target-driven semantic presentation of the moving quantified bubble.
The compiler data is the survivor view of the executor state, while the four
semantic fields retain the single trace relation, every proxy relation, the
ordered parameter valuation, and truth of the compiled bubble body. -/
structure BubblePresentation
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier) where
  rels : RelCtx
  outer : Concrete.Elaboration.WireContext state.diagram.val
  outerExact : (outer.extend state.bubble).Exact state.bubble
  binderContext : Concrete.Elaboration.BinderContext state.diagram.val rels
  binderCover : binderContext.Covers state.bubble
  binderEnumeration : Concrete.Elaboration.BinderContext.Enumeration
    state.diagram.val binderContext state.bubble
  fuel : Nat
  body : Region  outer.length rels
  compiled : compileSurvivorRegion?  state fuel state.bubble outer
    binderContext = some body
  environment : Fin outer.length → model.Carrier
  relationEnvironment : RelEnv model.Carrier rels
  fixed : FixedRelationAt payload state relationValue binderContext
    relationEnvironment
  proxies : ProxyRelationsAt payload state binderContext relationEnvironment
    values
  parameters : ParameterValuesAt state outer environment parameterValues
  denotes : denoteRegion model  environment relationEnvironment body

/-- Canonical compiler focus of the quantified bubble after deleting the
executor's already-processed atom placeholders. -/
noncomputable def droppedBubbleView
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount) :
    Concrete.Splice.SiteView (InstantiationDrop.checkedDrop state) state.bubble :=
  Classical.choice
    (Concrete.Splice.siteView_complete (InstantiationDrop.checkedDrop state)
      state.bubble)

/-- The focused compiler leaf on a dropped state computes exactly the
survivor region consumed by the fixed-relation simulation. -/
theorem droppedBubbleView_compileSurvivor
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount) :
    let view := droppedBubbleView state
    compileSurvivorRegion?  state (view.compilerLeaf.fuel + 1)
        state.bubble view.compilerLeaf.inheritedWires
        view.compilerLeaf.binders =
      some (Concrete.Elaboration.finishRegion state.diagram.val
        view.compilerLeaf.inheritedWires state.bubble
        view.compilerLeaf.items) := by
  let view := droppedBubbleView state
  let leaf := view.compilerLeaf
  change compileSurvivorRegion?  state (leaf.fuel + 1)
      state.bubble leaf.inheritedWires leaf.binders =
    some (Concrete.Elaboration.finishRegion state.diagram.val
      leaf.inheritedWires state.bubble leaf.items)
  have droppedCompiled : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw state) (leaf.fuel + 1) state.bubble
      leaf.inheritedWires leaf.binders =
        some (Concrete.Elaboration.finishRegion
          (dropInstantiationAtomsRaw state) leaf.inheritedWires state.bubble
          leaf.items) := by
    have itemsComputation := leaf.itemsComputation
    change Concrete.Elaboration.compileOccurrencesWith?
        (dropInstantiationAtomsRaw state)
        (Concrete.Elaboration.compileRegion?
          (dropInstantiationAtomsRaw state) leaf.fuel)
        (leaf.inheritedWires.extend state.bubble) leaf.binders
        (Concrete.Elaboration.localOccurrences
          (dropInstantiationAtomsRaw state) state.bubble) = some leaf.items
      at itemsComputation
    unfold Concrete.Elaboration.compileRegion?
    dsimp only
    exact (congrArg (fun result => result.bind (fun items =>
      some (Concrete.Elaboration.finishRegion state.diagram.val
        leaf.inheritedWires state.bubble items))) itemsComputation).trans rfl
  exact (drop_compileRegion_eq_survivor state (leaf.fuel + 1) state.bubble
    leaf.inheritedWires leaf.binders).symm.trans droppedCompiled

theorem exact_of_drop
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (exact : @Concrete.Elaboration.WireContext.Exact
      (dropInstantiationAtomsRaw state) context region) :
    @Concrete.Elaboration.WireContext.Exact state.diagram.val context region := by
  constructor
  · exact exact.nodup
  · intro wire
    constructor
    · intro member
      have droppedVisible := (exact.mem_iff wire).1 member
      exact (InstantiationDrop.raw_encloses_iff state
        (state.diagram.val.wires wire).scope region).1 (by
          simpa only [InstantiationDrop.raw_wire_scope] using droppedVisible)
    · intro visible
      apply (exact.mem_iff wire).2
      simpa only [InstantiationDrop.raw_wire_scope] using
        (InstantiationDrop.raw_encloses_iff state
          (state.diagram.val.wires wire).scope region).2 visible

private theorem exact_to_drop
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (exact : @Concrete.Elaboration.WireContext.Exact state.diagram.val context
      region) :
    @Concrete.Elaboration.WireContext.Exact (dropInstantiationAtomsRaw state)
      context region := by
  constructor
  · exact exact.nodup
  · intro wire
    constructor
    · intro member
      have visible := (exact.mem_iff wire).1 member
      simpa only [InstantiationDrop.raw_wire_scope] using
        (InstantiationDrop.raw_encloses_iff state
          (state.diagram.val.wires wire).scope region).2 visible
    · intro droppedVisible
      apply (exact.mem_iff wire).2
      exact (InstantiationDrop.raw_encloses_iff state
        (state.diagram.val.wires wire).scope region).1 (by
          simpa only [InstantiationDrop.raw_wire_scope] using droppedVisible)

private theorem binderCover_of_drop
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (cover : @Concrete.Elaboration.BinderContext.Covers
      (dropInstantiationAtomsRaw state) rels context region) :
    @Concrete.Elaboration.BinderContext.Covers state.diagram.val rels context
      region := by
  intro binder parent arity bubbleEq encloses
  apply cover binder parent arity
  · simpa only [InstantiationDrop.raw_regions] using bubbleEq
  · exact (InstantiationDrop.raw_encloses_iff state binder region).2 encloses

private theorem binderCover_to_drop
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (cover : @Concrete.Elaboration.BinderContext.Covers state.diagram.val rels
      context region) :
    @Concrete.Elaboration.BinderContext.Covers (dropInstantiationAtomsRaw state)
      rels context region := by
  intro binder parent arity bubbleEq encloses
  apply cover binder parent arity
  · simpa only [InstantiationDrop.raw_regions] using bubbleEq
  · exact (InstantiationDrop.raw_encloses_iff state binder region).1 encloses

private def binderEnumeration_of_drop
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (enumeration : Concrete.Elaboration.BinderContext.Enumeration
      (dropInstantiationAtomsRaw state) context region) :
    Concrete.Elaboration.BinderContext.Enumeration state.diagram.val context
      region where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := by
    intro index
    obtain ⟨parent, bubbleEq⟩ := enumeration.bubble index
    exact ⟨parent, by simpa only [InstantiationDrop.raw_regions] using bubbleEq⟩
  encloses := by
    intro index
    exact (InstantiationDrop.raw_encloses_iff state _ _).1
      (enumeration.encloses index)
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

private theorem frameInherited_mem
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      (input.plugLayout.frameRegion region)).Exact
      (input.plugLayout.frameRegion region))
    (index : Fin sourceOuter.length) :
    input.plugLayout.frameWire (sourceOuter.get index) ∈ targetOuter := by
  let layout := input.plugLayout
  let sourceFull := sourceOuter.extend region
  let targetFull := targetOuter.extend (layout.frameRegion region)
  have sourceMember : sourceOuter.get index ∈ sourceFull := by
    exact List.mem_append_left _ (List.get_mem sourceOuter index)
  have targetMember : layout.frameWire (sourceOuter.get index) ∈ targetFull :=
    (layout.frameWire_mem_context_iff region sourceFull targetFull sourceExact
      targetExact (sourceOuter.get index)).2 sourceMember
  have targetParts : layout.frameWire (sourceOuter.get index) ∈ targetOuter ∨
      layout.frameWire (sourceOuter.get index) ∈
        Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion region) := by
    change layout.frameWire (sourceOuter.get index) ∈
      targetOuter ++ Concrete.Elaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region) at targetMember
    exact List.mem_append.mp targetMember
  apply targetParts.resolve_right
  intro targetLocal
  have targetScope :=
    (Concrete.Elaboration.mem_exactScopeWires layout.plugRaw
      (layout.frameRegion region) _).1 targetLocal
  have frameScope :
      (layout.plugRaw.wires
        (layout.frameWire (sourceOuter.get index))).scope =
        layout.frameRegion
          (input.coalescedScope (sourceOuter.get index)) := by
    change (layout.plugWire
      (layout.quotientBlockWire (sourceOuter.get index))).scope = _
    rw [Concrete.Splice.Input.PlugLayout.plugWire_quotientBlockWire]
  have sourceScope :
      (input.coalesceFrameRaw.wires (sourceOuter.get index)).scope = region := by
    have coalescedScopeEq :
        input.coalescedScope (sourceOuter.get index) = region :=
      layout.frameRegion_injective (frameScope.symm.trans targetScope)
    simpa [input.coalesceFrameRaw_wire] using coalescedScopeEq
  have sourceLocal : sourceOuter.get index ∈
      Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw region :=
    (Concrete.Elaboration.mem_exactScopeWires _ _ _).2 sourceScope
  have nodup := sourceExact.nodup
  rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
  exact nodup.2.2 _ (List.get_mem sourceOuter index) _ sourceLocal rfl

/-- Index transport for the inherited part of any two exact bubble compiler
contexts across one splice frame. -/
noncomputable def frameInheritedIndex
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      (input.plugLayout.frameRegion region)).Exact
      (input.plugLayout.frameRegion region)) :
    Fin sourceOuter.length → Fin targetOuter.length :=
  fun index => Classical.choose
    (Concrete.Elaboration.WireContext.lookup?_complete
      (frameInherited_mem input region sourceOuter targetOuter sourceExact
        targetExact index))

theorem frameInheritedIndex_lookup
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      (input.plugLayout.frameRegion region)).Exact
      (input.plugLayout.frameRegion region))
    (index : Fin sourceOuter.length) :
    targetOuter.lookup?
        (input.plugLayout.frameWire (sourceOuter.get index)) =
      some (frameInheritedIndex input region sourceOuter targetOuter
        sourceExact targetExact index) := by
  exact Classical.choose_spec
    (Concrete.Elaboration.WireContext.lookup?_complete
      (frameInherited_mem input region sourceOuter targetOuter sourceExact
        targetExact index))

theorem frameInheritedIndex_spec
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      (input.plugLayout.frameRegion region)).Exact
      (input.plugLayout.frameRegion region))
    (index : Fin sourceOuter.length) :
    targetOuter.get (frameInheritedIndex input region sourceOuter targetOuter
      sourceExact targetExact index) =
      input.plugLayout.frameWire (sourceOuter.get index) := by
  apply Concrete.Elaboration.WireContext.lookup?_sound
  exact Classical.choose_spec
    (Concrete.Elaboration.WireContext.lookup?_complete
      (frameInherited_mem input region sourceOuter targetOuter sourceExact
        targetExact index))

private theorem frameRelation_exists
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceBinders : Concrete.Elaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (targetBinders : Concrete.Elaboration.BinderContext
      input.plugLayout.plugRaw targetRels)
    (targetCover : targetBinders.Covers
      (input.plugLayout.frameRegion region))
    {arity : Nat} (relation : RelVar sourceRels arity) :
    ∃ target : RelVar targetRels arity,
      targetBinders
          (input.plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, target⟩ := by
  let layout := input.plugLayout
  obtain ⟨parent, bubbleEq⟩ :=
    sourceEnumeration.bubble relation.index
  have bubbleEq' : input.coalesceFrameRaw.regions
      (sourceEnumeration.binder relation.index) =
        .bubble parent arity := by
    rw [relation.hasArity] at bubbleEq
    exact bubbleEq
  have targetBubble := layout.plugRaw_frameRegion_bubble
    (sourceEnumeration.binder relation.index) parent arity bubbleEq'
  have sourceEncloses := sourceEnumeration.encloses relation.index
  have frameEncloses : layout.plugRaw.Encloses
      (layout.frameRegion (sourceEnumeration.binder relation.index))
      (layout.frameRegion region) := by
    apply layout.frame_encloses
    simpa [input.coalesceFrameRaw_encloses_iff] using sourceEncloses
  exact targetCover _ _ _ targetBubble frameEncloses

/-- Relation-variable transport induced by the exact concrete binder owners
of the source and target bubble compiler contexts. -/
noncomputable def frameRelationMap
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceBinders : Concrete.Elaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (targetBinders : Concrete.Elaboration.BinderContext
      input.plugLayout.plugRaw targetRels)
    (targetCover : targetBinders.Covers
      (input.plugLayout.frameRegion region)) :
    RelationRenaming sourceRels targetRels :=
  fun relation => Classical.choose
    (frameRelation_exists input region sourceBinders sourceEnumeration
      targetBinders targetCover relation)

theorem frameRelationMap_spec
    (input : Concrete.Splice.Input )
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceBinders : Concrete.Elaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (targetBinders : Concrete.Elaboration.BinderContext
      input.plugLayout.plugRaw targetRels)
    (targetCover : targetBinders.Covers
      (input.plugLayout.frameRegion region))
    {arity : Nat} (relation : RelVar sourceRels arity) :
    targetBinders
        (input.plugLayout.frameRegion
          (sourceEnumeration.binder relation.index)) =
      some ⟨arity, frameRelationMap input region sourceBinders
        sourceEnumeration targetBinders targetCover relation⟩ := by
  exact Classical.choose_spec
    (frameRelation_exists input region sourceBinders sourceEnumeration
      targetBinders targetCover relation)

/-- Ordered parameter values pull back from an accepted step's target context
to the alias-quotient source context. -/
theorem parameterValuesAt_pullback_frame
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
    (sourceOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend state.bubble).Exact state.bubble)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion state.bubble)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion state.bubble))
    (targetEnvironment : Fin targetOuter.length → D)
    (parameterValues : Fin attachments.length → D)
    (targetParameters : ParameterValuesAt
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetOuter targetEnvironment parameterValues) :
    ParameterValuesAt
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      sourceOuter
      (targetEnvironment ∘ frameInheritedIndex
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments)
        state.bubble sourceOuter targetOuter sourceExact targetExact)
      parameterValues := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let outerMap := frameInheritedIndex spliceInput state.bubble sourceOuter
    targetOuter sourceExact targetExact
  intro position
  obtain ⟨targetIndex, targetWire, targetValue⟩ := targetParameters position
  let sourceWire := spliceInput.quotientWire (state.parameters position)
  have targetWire' : targetOuter.get targetIndex =
      layout.frameWire sourceWire := by
    simpa [next, sourceWire, spliceInput] using targetWire
  have targetFullMember : layout.frameWire sourceWire ∈
      targetOuter.extend (layout.frameRegion state.bubble) := by
    exact targetWire' ▸
      List.mem_append_left _ (List.get_mem targetOuter targetIndex)
  have targetVisible : layout.plugRaw.Encloses
      (layout.plugRaw.wires (layout.frameWire sourceWire)).scope
      (layout.frameRegion state.bubble) :=
    (targetExact.mem_iff _).1 targetFullMember
  have sourceVisible : spliceInput.coalesceFrameRaw.Encloses
      (spliceInput.coalesceFrameRaw.wires sourceWire).scope state.bubble :=
    (layout.frameWire_visible_at_region_iff state.bubble sourceWire).1
      targetVisible
  have sourceFullMember : sourceWire ∈ sourceOuter.extend state.bubble :=
    (sourceExact.mem_iff sourceWire).2 sourceVisible
  have targetOuterNodup : targetOuter.Nodup := by
    have nodup := targetExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have sourceOuterNodup : sourceOuter.Nodup := by
    have nodup := sourceExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have sourceMember : sourceWire ∈ sourceOuter := by
    change sourceWire ∈ sourceOuter ++
      Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
        state.bubble at sourceFullMember
    apply (List.mem_append.mp sourceFullMember).resolve_right
    intro sourceLocal
    have sourceScope :=
      (Concrete.Elaboration.mem_exactScopeWires spliceInput.coalesceFrameRaw
        state.bubble sourceWire).1 sourceLocal
    have targetScope :
        (layout.plugRaw.wires (layout.frameWire sourceWire)).scope =
          layout.frameRegion state.bubble := by
      change (layout.plugWire (layout.quotientBlockWire sourceWire)).scope = _
      rw [Concrete.Splice.Input.PlugLayout.plugWire_quotientBlockWire]
      exact congrArg layout.frameRegion (by
        simpa [spliceInput.coalesceFrameRaw_wire] using sourceScope)
    have targetLocal : layout.frameWire sourceWire ∈
        Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion state.bubble) :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).2 targetScope
    have nodup := targetExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.2.2 _
      (targetWire' ▸ List.get_mem targetOuter targetIndex)
      _ targetLocal rfl
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete sourceMember
  have sourceGet : sourceOuter.get sourceIndex = sourceWire :=
    Concrete.Elaboration.WireContext.lookup?_sound sourceLookup
  refine ⟨sourceIndex, ?_, ?_⟩
  · simpa [coalesced, sourceWire, spliceInput] using sourceGet
  · have mappedGet := frameInheritedIndex_spec spliceInput state.bubble
      sourceOuter targetOuter sourceExact targetExact sourceIndex
    have mappedTarget : outerMap sourceIndex = targetIndex := by
      have mappedLookup := frameInheritedIndex_lookup spliceInput state.bubble
        sourceOuter targetOuter sourceExact targetExact sourceIndex
      rw [sourceGet] at mappedLookup
      change targetOuter.lookup? (layout.frameWire sourceWire) =
        some (outerMap sourceIndex) at mappedLookup
      have targetIsMapped := Concrete.Elaboration.WireContext.lookup?_unique
        targetOuterNodup mappedLookup targetWire'
      exact targetIsMapped.symm
    change targetEnvironment (outerMap sourceIndex) = parameterValues position
    rw [mappedTarget]
    exact targetValue

/-- One accepted copy step pulls a target bubble presentation back to the
alias-quotient source while preserving the single trace witness. -/
noncomputable def coalescedBubblePresentation_of_target
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
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : ∀ sourceFuel targetFuel,
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model  relationValue
        values parameterValues .backward sourceFuel targetFuel state.bubble)
    (target : BubblePresentation payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      model  relationValue values parameterValues) :
    BubblePresentation payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      model  relationValue values parameterValues := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceView := droppedBubbleView coalesced
  let sourceLeaf := sourceView.compilerLeaf
  let sourceOuter := sourceLeaf.inheritedWires
  let sourceBinders := sourceLeaf.binders
  let sourceEnumeration := sourceLeaf.binderEnumeration
  let sourceBody := Concrete.Elaboration.finishRegion coalesced.diagram.val
    sourceOuter coalesced.bubble sourceLeaf.items
  have sourceExact : @Concrete.Elaboration.WireContext.Exact
      coalesced.diagram.val
      (@Concrete.Elaboration.WireContext.extend coalesced.diagram.val sourceOuter
        state.bubble) state.bubble := by
    apply exact_of_drop coalesced
    simpa only [drop_exactScopeWires] using sourceLeaf.wiresExact
  have targetExact : (target.outer.extend
      (layout.frameRegion state.bubble)).Exact
      (layout.frameRegion state.bubble) := by
    simpa [next, layout, spliceInput, advanceInstantiationState] using
      target.outerExact
  have sourceCover : @Concrete.Elaboration.BinderContext.Covers
      coalesced.diagram.val sourceView.intrinsicPath.toFocus.holeRels
      sourceBinders state.bubble := by
    exact binderCover_of_drop coalesced sourceBinders state.bubble (by
      exact sourceLeaf.bindersCover)
  have targetCover : target.binderContext.Covers
      (layout.frameRegion state.bubble) := by
    simpa [next, layout, spliceInput, advanceInstantiationState] using
      target.binderCover
  have sourceEnumeration' : Concrete.Elaboration.BinderContext.Enumeration
      spliceInput.coalesceFrameRaw sourceBinders state.bubble := by
    exact binderEnumeration_of_drop coalesced sourceBinders state.bubble (by
      simpa [sourceEnumeration, sourceBinders, sourceLeaf, sourceView,
        coalesced, spliceInput] using sourceLeaf.binderEnumeration)
  let outerMap := frameInheritedIndex spliceInput state.bubble sourceOuter
    target.outer sourceExact targetExact
  let relationMap : RelationRenaming
      sourceView.intrinsicPath.toFocus.holeRels target.rels :=
    frameRelationMap spliceInput state.bubble sourceBinders sourceEnumeration'
      target.binderContext targetCover
  let sourceEnvironment := target.environment ∘ outerMap
  let sourceRelationEnvironment :=
    RelEnv.pullback relationMap target.relationEnvironment
  have sourceCompiled : compileSurvivorRegion?  coalesced
      (sourceLeaf.fuel + 1) state.bubble sourceOuter sourceBinders =
        some sourceBody := by
    simpa [sourceBody, sourceOuter, sourceLeaf, sourceView, coalesced] using
      droppedBubbleView_compileSurvivor coalesced
  have targetCompiled : compileSurvivorRegion?  next target.fuel
      (layout.frameRegion state.bubble) target.outer target.binderContext =
        some target.body := by
    simpa [next, layout, spliceInput, advanceInstantiationState] using
      target.compiled
  have outerSpec : ∀ index, target.outer.get (outerMap index) =
      layout.frameWire (sourceOuter.get index) := by
    intro index
    exact frameInheritedIndex_spec spliceInput state.bubble sourceOuter
      target.outer sourceExact targetExact index
  have relationSpec' : ∀ {arity} (relation : RelVar
      sourceView.intrinsicPath.toFocus.holeRels arity),
      target.binderContext
          (layout.frameRegion
            (sourceEnumeration'.binder relation.index)) =
        some ⟨arity, relationMap relation⟩ := by
    intro arity relation
    exact frameRelationMap_spec spliceInput state.bubble sourceBinders
      sourceEnumeration' target.binderContext targetCover relation
  have environmentsAgree :
      (Concrete.Elaboration.ContextIndexRelation.forwardMap outerMap)
        |>.EnvironmentsAgree sourceEnvironment target.environment := by
    rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap]
    rfl
  have sourceRenamedDenotes : denoteRegion model  sourceEnvironment
      target.relationEnvironment (sourceBody.renameRelations relationMap) := by
    exact simulations (sourceLeaf.fuel + 1) target.fuel sourceOuter target.outer
      sourceExact targetExact sourceBinders target.binderContext sourceCover
      targetCover sourceEnumeration' target.binderEnumeration outerMap outerSpec
      relationMap relationSpec' sourceBody target.body sourceCompiled
      targetCompiled sourceEnvironment target.environment
      target.relationEnvironment environmentsAgree target.fixed target.proxies
      target.parameters target.denotes
  have sourceDenotes : denoteRegion model  sourceEnvironment
      sourceRelationEnvironment sourceBody := by
    exact (denoteRegion_renameRelations model  relationMap
      sourceRelationEnvironment target.relationEnvironment
      (RelEnv.pullback_agrees relationMap target.relationEnvironment)
      sourceEnvironment sourceBody).mp sourceRenamedDenotes
  have sourceFixed : FixedRelationAt payload coalesced relationValue
      sourceBinders sourceRelationEnvironment := by
    exact fixedRelationAt_pullback_frame comprehension attachments binders
      payload state atom tail site arguments hadmissible state.bubble
      sourceBinders target.binderContext sourceEnumeration' relationMap
      relationSpec' model relationValue target.relationEnvironment target.fixed
  have sourceProxies : ProxyRelationsAt payload coalesced sourceBinders
      sourceRelationEnvironment values := by
    exact proxyRelationsAt_pullback_frame comprehension attachments binders
      payload state atom tail site arguments hadmissible state.bubble
      sourceBinders target.binderContext sourceEnumeration' relationMap
      relationSpec' model values target.relationEnvironment target.proxies
  have sourceParameters : ParameterValuesAt coalesced sourceOuter
      sourceEnvironment parameterValues := by
    exact parameterValuesAt_pullback_frame comprehension attachments binders
      payload state atom tail site arguments hadmissible sourceOuter
      target.outer sourceExact targetExact target.environment parameterValues
      target.parameters
  exact {
    rels := sourceView.intrinsicPath.toFocus.holeRels
    outer := sourceOuter
    outerExact := by simpa [coalesced] using sourceExact
    binderContext := sourceBinders
    binderCover := by simpa [coalesced] using sourceCover
    binderEnumeration := by
      simpa [coalesced] using sourceEnumeration'
    fuel := sourceLeaf.fuel + 1
    body := sourceBody
    compiled := by simpa [coalesced] using sourceCompiled
    environment := sourceEnvironment
    relationEnvironment := sourceRelationEnvironment
    fixed := sourceFixed
    proxies := sourceProxies
    parameters := sourceParameters
    denotes := sourceDenotes
  }

private theorem inherited_mem_iff_iso
    {source target : Concrete.Diagram}
    (iso : Concrete.Iso source target)
    (region : Fin source.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext source)
    (targetOuter : Concrete.Elaboration.WireContext target)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend (iso.regions region)).Exact
      (iso.regions region))
    (wire : Fin source.wireCount) :
    iso.wires wire ∈ targetOuter ↔ wire ∈ sourceOuter := by
  constructor
  · intro targetMember
    have targetFull : iso.wires wire ∈
        targetOuter.extend (iso.regions region) := by
      exact List.mem_append_left _ targetMember
    have targetVisible := (targetExact.mem_iff _).1 targetFull
    have sourceVisible : source.Encloses (source.wires wire).scope region := by
      have pulled := iso.symm.encloses_transport targetVisible
      have scopeEq : iso.regions.invFun
          (target.wires (iso.wires wire)).scope =
          (source.wires wire).scope := by
        rw [← iso.wire_scope_eq wire, iso.regions.left_inv]
      simpa [Concrete.Iso.symm, scopeEq] using pulled
    have sourceFull := (sourceExact.mem_iff wire).2 sourceVisible
    apply (List.mem_append.mp sourceFull).resolve_right
    intro sourceLocal
    have targetScope : (target.wires (iso.wires wire)).scope =
        iso.regions region := by
      rw [← iso.wire_scope_eq wire]
      exact congrArg iso.regions
        ((Concrete.Elaboration.mem_exactScopeWires source region wire).1
          sourceLocal)
    have targetLocal : iso.wires wire ∈
        Concrete.Elaboration.exactScopeWires target (iso.regions region) :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).2 targetScope
    have nodup := targetExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.2.2 _ targetMember _ targetLocal rfl
  · intro sourceMember
    have sourceFull : wire ∈ sourceOuter.extend region :=
      List.mem_append_left _ sourceMember
    have sourceVisible := (sourceExact.mem_iff wire).1 sourceFull
    have targetVisible := iso.encloses_transport sourceVisible
    have targetFull := (targetExact.mem_iff (iso.wires wire)).2 (by
      simpa only [iso.wire_scope_eq] using targetVisible)
    apply (List.mem_append.mp targetFull).resolve_right
    intro targetLocal
    have targetScope :=
      (Concrete.Elaboration.mem_exactScopeWires target (iso.regions region)
        (iso.wires wire)).1 targetLocal
    have sourceScope : (source.wires wire).scope = region := by
      apply iso.regions.injective
      rw [iso.wire_scope_eq]
      exact targetScope
    have sourceLocal : wire ∈
        Concrete.Elaboration.exactScopeWires source region :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).2 sourceScope
    have nodup := sourceExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.2.2 _ sourceMember _ sourceLocal rfl

noncomputable def inheritedWireEquivIso
    {source target : Concrete.Diagram}
    (iso : Concrete.Iso source target)
    (region : Fin source.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext source)
    (targetOuter : Concrete.Elaboration.WireContext target)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend (iso.regions region)).Exact
      (iso.regions region)) :
    FiniteEquiv (Fin sourceOuter.length) (Fin targetOuter.length) :=
  FiniteEquiv.restrictLists iso.wires sourceOuter targetOuter
    (by
      have nodup := sourceExact.nodup
      rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
      exact nodup.1)
    (by
      have nodup := targetExact.nodup
      rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
      exact nodup.1)
    (fun wire => inherited_mem_iff_iso iso region sourceOuter targetOuter
      sourceExact targetExact wire)

theorem inheritedWireEquivIso_spec
    {source target : Concrete.Diagram}
    (iso : Concrete.Iso source target)
    (region : Fin source.regionCount)
    (sourceOuter : Concrete.Elaboration.WireContext source)
    (targetOuter : Concrete.Elaboration.WireContext target)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend (iso.regions region)).Exact
      (iso.regions region))
    (index : Fin sourceOuter.length) :
    targetOuter.get
        (inheritedWireEquivIso iso region sourceOuter targetOuter sourceExact
          targetExact index) =
      iso.wires (sourceOuter.get index) :=
  FiniteEquiv.restrictLists_spec iso.wires sourceOuter targetOuter _ _ _ index

/-- Deleting processed atoms commutes with cancellation of any retained-host
quotient certified discrete by the executor's attachment contract. -/
noncomputable def attachmentRespectingDroppedStateIso
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (respects : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).AttachmentsRespectBoundary) :
    Concrete.Iso
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible))
      (dropInstantiationAtomsRaw state) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let wireEquiv :=
    Concrete.Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary
      spliceInput respects
  exact {
    regionCount_eq := rfl
    nodeCount_eq := rfl
    wireCount_eq := by
      apply Nat.le_antisymm
      · exact fin_card_le_of_injective wireEquiv wireEquiv.injective
      · exact fin_card_le_of_injective wireEquiv.symm wireEquiv.symm.injective
    regions := .refl _
    nodes := .refl _
    wires := wireEquiv
    root_eq := rfl
    regions_eq := by
      intro region
      change (state.diagram.val.regions region).rename (.refl _) =
        state.diagram.val.regions region
      simp
    nodes_eq := by
      intro node
      change (state.diagram.val.nodes
          ((instantiationAtomDomain state).origin node)).rename (.refl _) =
        state.diagram.val.nodes ((instantiationAtomDomain state).origin node)
      simp
    wire_scope_eq := by
      intro quotient
      change spliceInput.coalescedScope quotient =
        (state.diagram.val.wires (wireEquiv quotient)).scope
      exact Concrete.Splice.Input.coalescedScope_eq_of_attachmentsRespectBoundary
        spliceInput respects quotient
    wire_endpoints_perm := by
      intro quotient
      change
        (((spliceInput.coalescedEndpoints quotient).filterMap
            (instantiationAtomDomain state).reindexEndpoint?).map
          (CEndpoint.rename (.refl _))).Perm
        ((state.diagram.val.wires (wireEquiv quotient)).endpoints.filterMap
          (instantiationAtomDomain state).reindexEndpoint?)
      rw [Concrete.Splice.Input.coalescedEndpoints_eq_of_attachmentsRespectBoundary
        spliceInput respects quotient]
      simpa [spliceInput, instantiateSpliceInput, wireEquiv] using
        (Concrete.Iso.refl (dropInstantiationAtomsRaw state)).wire_endpoints_perm
          (wireEquiv quotient)
  }

theorem attachmentRespectingDroppedRegionIso
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (respects : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).AttachmentsRespectBoundary)
    {sourceRels : RelCtx}
    {sourceFuel targetFuel : Nat}
    {sourceRegion : Fin
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)).regionCount}
    {targetRegion : Fin (dropInstantiationAtomsRaw state).regionCount}
    (regionEq :
      (attachmentRespectingDroppedStateIso comprehension attachments binders
        payload state site arguments hadmissible respects).regions sourceRegion =
        targetRegion)
    (sourceContext : Concrete.Elaboration.WireContext
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)))
    (targetContext : Concrete.Elaboration.WireContext
      (dropInstantiationAtomsRaw state))
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (contextsAgree : Concrete.Elaboration.WireContextsAgree
      (attachmentRespectingDroppedStateIso comprehension attachments binders
        payload state site arguments hadmissible respects)
      sourceContext targetContext ambient)
    (targetExact : (targetContext.extend targetRegion).Exact targetRegion)
    (sourceBinders : Concrete.Elaboration.BinderContext
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)) sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (dropInstantiationAtomsRaw state) sourceRels)
    (bindersAgree : Concrete.Elaboration.BinderContextsAgree
      (attachmentRespectingDroppedStateIso comprehension attachments binders
        payload state site arguments hadmissible respects)
      sourceBinders targetBinders)
    (sourceBody : Region  sourceContext.length sourceRels)
    (targetBody : Region  targetContext.length sourceRels)
    (sourceCompiled : compileSurvivorRegion?
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      sourceFuel sourceRegion sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw state) targetFuel targetRegion targetContext
      targetBinders = some targetBody) :
    RegionIso  ambient sourceRels sourceBody targetBody := by
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let iso := attachmentRespectingDroppedStateIso comprehension attachments
    binders payload state site arguments hadmissible respects
  have sourceCompiled' : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw coalesced) sourceFuel sourceRegion sourceContext
      sourceBinders = some sourceBody := by
    exact (drop_compileRegion_eq_survivor coalesced sourceFuel sourceRegion
      sourceContext sourceBinders).trans (by
        simpa [coalesced] using sourceCompiled)
  subst targetRegion
  exact Concrete.Elaboration.compileRegion?_equivariant iso
    (InstantiationDrop.raw_wellFormed state) contextsAgree targetExact
    bindersAgree sourceCompiled' targetCompiled

/-- Cancellation of an executor-certified discrete retained-host quotient
transports a bubble presentation back to the executor state. -/
noncomputable def bubblePresentation_of_coalesced
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (respects : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).AttachmentsRespectBoundary)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (source : BubblePresentation payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      model  relationValue values parameterValues) :
    BubblePresentation payload state model  relationValue values
      parameterValues := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let actualIso :=
    Concrete.Splice.Input.coalescedFrameIsoOfAttachmentsRespectBoundary spliceInput
      respects
  let droppedIso := attachmentRespectingDroppedStateIso comprehension
    attachments binders payload state site arguments hadmissible respects
  let targetView := droppedBubbleView state
  let targetLeaf := targetView.compilerLeaf
  let targetOuter := targetLeaf.inheritedWires
  have targetExact : @Concrete.Elaboration.WireContext.Exact state.diagram.val
      (@Concrete.Elaboration.WireContext.extend state.diagram.val targetOuter
        state.bubble) state.bubble := by
    apply exact_of_drop state
    simpa only [drop_exactScopeWires] using targetLeaf.wiresExact
  have sourceExact : @Concrete.Elaboration.WireContext.Exact
      spliceInput.coalesceFrameRaw
      (@Concrete.Elaboration.WireContext.extend spliceInput.coalesceFrameRaw
        source.outer state.bubble) state.bubble := by
    simpa [coalesced, spliceInput] using source.outerExact
  let ambient := inheritedWireEquivIso actualIso state.bubble source.outer
    targetOuter sourceExact targetExact
  let targetBinders : Concrete.Elaboration.BinderContext state.diagram.val
      source.rels := fun region =>
    source.binderContext (actualIso.regions.invFun region)
  have bindersAgree : Concrete.Elaboration.BinderContextsAgree droppedIso
      source.binderContext targetBinders := by
    intro region
    change source.binderContext
        (actualIso.regions.invFun (droppedIso.regions region)) =
      source.binderContext region
    apply congrArg source.binderContext
    apply Fin.ext
    rfl
  have actualBindersAgree : Concrete.Elaboration.BinderContextsAgree actualIso
      source.binderContext targetBinders := by
    intro region
    exact congrArg source.binderContext (actualIso.regions.left_inv region)
  have targetCover : targetBinders.Covers state.bubble := by
    have mapped := source.binderCover.mapIso actualIso actualBindersAgree
    simpa [actualIso, coalesced, spliceInput] using mapped
  let targetEnumeration := source.binderEnumeration.mapIso actualIso
    actualBindersAgree
  let depth := Classical.choose
    (state.diagram.property.all_regions_reach_root state.bubble)
  have depthEq := Classical.choose_spec
    (state.diagram.property.all_regions_reach_root state.bubble)
  have depthLe : depth.val ≤ state.diagram.val.regionCount :=
    Concrete.Elaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      state.diagram depthEq
  let targetFuel := state.diagram.val.regionCount + 1 - depth.val
  have fuelEq : depth.val + targetFuel = state.diagram.val.regionCount + 1 := by
    dsimp [targetFuel]
    omega
  have droppedDepth : (dropInstantiationAtomsRaw state).climb depth.val
      state.bubble = some (dropInstantiationAtomsRaw state).root := by
    simpa only [InstantiationDrop.raw_climb, InstantiationDrop.raw_root] using
      depthEq
  have droppedExact : @Concrete.Elaboration.WireContext.Exact
      (dropInstantiationAtomsRaw state)
      (@Concrete.Elaboration.WireContext.extend
        (dropInstantiationAtomsRaw state) targetOuter state.bubble)
      state.bubble := by
    apply exact_to_drop state
    simpa only [drop_exactScopeWires] using targetExact
  have droppedCover : @Concrete.Elaboration.BinderContext.Covers
      (dropInstantiationAtomsRaw state) source.rels targetBinders
      state.bubble := binderCover_to_drop state targetBinders state.bubble
        targetCover
  let targetCompilation := Concrete.Elaboration.compileRegion?_complete
      (InstantiationDrop.raw_wellFormed state) droppedDepth fuelEq droppedExact
      droppedCover
  let targetBody := Classical.choose targetCompilation
  have targetCompiledDropped := Classical.choose_spec targetCompilation
  have targetCompiled : compileSurvivorRegion?  state targetFuel
      state.bubble targetOuter targetBinders = some targetBody := by
    exact (drop_compileRegion_eq_survivor state targetFuel state.bubble
      targetOuter targetBinders).symm.trans targetCompiledDropped
  have contextsAgree : Concrete.Elaboration.WireContextsAgree droppedIso
      source.outer targetOuter ambient := by
    intro index
    simpa [ambient, actualIso, droppedIso,
      attachmentRespectingDroppedStateIso,
      Concrete.Splice.Input.coalescedFrameIsoOfAttachmentsRespectBoundary] using
      inheritedWireEquivIso_spec actualIso state.bubble source.outer targetOuter
        sourceExact targetExact index
  have sourceCompiled : compileSurvivorRegion?  coalesced source.fuel
      state.bubble source.outer source.binderContext = some source.body := by
    simpa [coalesced] using source.compiled
  have bodyIso : RegionIso  ambient source.rels source.body
      targetBody := by
    exact attachmentRespectingDroppedRegionIso comprehension attachments
      binders payload state site arguments hadmissible respects rfl source.outer
      targetOuter ambient contextsAgree droppedExact source.binderContext
      targetBinders bindersAgree source.body targetBody sourceCompiled
      targetCompiledDropped
  let targetEnvironment : Fin targetOuter.length → model.Carrier :=
    source.environment ∘ ambient.invFun
  have environmentsAgree : EnvironmentsAgree ambient source.environment
      targetEnvironment := by
    intro index
    change source.environment (ambient.invFun (ambient index)) =
      source.environment index
    exact congrArg source.environment (ambient.left_inv index)
  have targetDenotes : denoteRegion model  targetEnvironment
      source.relationEnvironment targetBody :=
    (bodyIso.denotation model  source.environment targetEnvironment
      source.relationEnvironment environmentsAgree).mp source.denotes
  have targetFixed : FixedRelationAt payload state relationValue targetBinders
      source.relationEnvironment := by
    intro relation lookup
    apply source.fixed relation
    simpa [targetBinders, actualIso, coalesced, spliceInput] using lookup
  have targetProxies : ProxyRelationsAt payload state targetBinders
      source.relationEnvironment values := by
    intro index relation lookup
    apply source.proxies index relation
    simpa [targetBinders, actualIso, coalesced, spliceInput] using lookup
  have targetParameters : ParameterValuesAt state targetOuter targetEnvironment
      parameterValues := by
    intro position
    obtain ⟨sourceIndex, wireEq, valueEq⟩ := source.parameters position
    let targetIndex := ambient sourceIndex
    refine ⟨targetIndex, ?_, ?_⟩
    · have mappedWire := inheritedWireEquivIso_spec actualIso state.bubble
        source.outer targetOuter sourceExact targetExact sourceIndex
      change targetOuter.get targetIndex =
        actualIso.wires (source.outer.get sourceIndex) at mappedWire
      rw [wireEq] at mappedWire
      have parameterImage : actualIso.wires (coalesced.parameters position) =
          state.parameters position := by
        change Concrete.Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary
            spliceInput respects
            (spliceInput.quotientWire (state.parameters position)) =
          state.parameters position
        exact Concrete.Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary_quotientWire
          spliceInput respects (state.parameters position)
      exact mappedWire.trans parameterImage
    · change source.environment (ambient.invFun (ambient sourceIndex)) =
        parameterValues position
      rw [ambient.left_inv]
      exact valueEq
  exact {
    rels := source.rels
    outer := targetOuter
    outerExact := targetExact
    binderContext := targetBinders
    binderCover := targetCover
    binderEnumeration := by
      simpa [targetEnumeration, actualIso, coalesced, spliceInput] using
        targetEnumeration
    fuel := targetFuel
    body := targetBody
    compiled := targetCompiled
    environment := targetEnvironment
    relationEnvironment := source.relationEnvironment
    fixed := targetFixed
    proxies := targetProxies
    parameters := targetParameters
    denotes := targetDenotes
  }

/-- Backward fixed-relation simulations compose over the executor's complete
accepted trace, normalizing each transient quotient before the next step. -/
theorem bubblePresentation_nonempty_of_trace
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : Concrete.Checked }
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : RegionSimulationsEveryStep trace model  relationValue
      values parameterValues)
    (target : BubblePresentation payload result model  relationValue values
      parameterValues) :
    Nonempty (BubblePresentation payload state model  relationValue values
      parameterValues) := by
  induction trace with
  | done fuel state pending_empty =>
      exact ⟨target⟩
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      rcases simulations with ⟨simulation, restSimulations⟩
      obtain ⟨nextPresentation⟩ := ih restSimulations target
      rw [plan.next_eq] at nextPresentation
      let hadmissible :=
        (Concrete.Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have operationalTarget : BubblePresentation plan.operationalPayload
          (advanceInstantiationState plan.materialization.result attachments
            binders plan.operationalPayload state atom tail site arguments
            hadmissible)
          model  relationValue values parameterValues := {
        rels := nextPresentation.rels
        outer := nextPresentation.outer
        outerExact := nextPresentation.outerExact
        binderContext := nextPresentation.binderContext
        binderCover := nextPresentation.binderCover
        binderEnumeration := nextPresentation.binderEnumeration
        fuel := nextPresentation.fuel
        body := nextPresentation.body
        compiled := nextPresentation.compiled
        environment := nextPresentation.environment
        relationEnvironment := nextPresentation.relationEnvironment
        fixed := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.spine,
            Concrete.Splice.AttachmentAliasMaterialization.binderSpine] using
            nextPresentation.fixed
        proxies := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.spine,
            Concrete.Splice.AttachmentAliasMaterialization.binderSpine] using
            nextPresentation.proxies
        parameters := nextPresentation.parameters
        denotes := nextPresentation.denotes
      }
      let coalesced := coalescedBubblePresentation_of_target
        plan.materialization.result attachments binders
        plan.operationalPayload state atom tail site arguments hadmissible model
         relationValue values parameterValues
        (fun sourceFuel targetFuel => simulation .backward sourceFuel targetFuel
          state.bubble (Concrete.Diagram.Encloses.refl _ _))
        operationalTarget
      let source := bubblePresentation_of_coalesced
        plan.materialization.result attachments binders
        plan.operationalPayload state site arguments hadmissible
        plan.attachmentsRespectBoundary model  relationValue values
        parameterValues coalesced
      exact ⟨{
        rels := source.rels
        outer := source.outer
        outerExact := source.outerExact
        binderContext := source.binderContext
        binderCover := source.binderCover
        binderEnumeration := source.binderEnumeration
        fuel := source.fuel
        body := source.body
        compiled := source.compiled
        environment := source.environment
        relationEnvironment := source.relationEnvironment
        fixed := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.spine,
            Concrete.Splice.AttachmentAliasMaterialization.binderSpine] using source.fixed
        proxies := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.spine,
            Concrete.Splice.AttachmentAliasMaterialization.binderSpine] using
            source.proxies
        parameters := source.parameters
        denotes := source.denotes
      }⟩

/-- Choice-free clients use the propositional composition theorem above;
semantic soundness extracts its canonical presentation only at the boundary. -/
noncomputable def bubblePresentation_of_trace
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : Concrete.Checked }
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : RegionSimulationsEveryStep trace model  relationValue
      values parameterValues)
    (target : BubblePresentation payload result model  relationValue values
      parameterValues) :
    BubblePresentation payload state model  relationValue values
      parameterValues :=
  Classical.choice (bubblePresentation_nonempty_of_trace trace model
    relationValue values parameterValues simulations target)

end InstantiationSemantic

end VisualProof.Rule
