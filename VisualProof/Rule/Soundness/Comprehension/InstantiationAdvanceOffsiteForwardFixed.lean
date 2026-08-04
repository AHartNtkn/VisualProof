import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteForwardFixed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Forward fixed-relation transport for a survivor conjunction away from the
distinguished splice site.  The exact occurrence equivalence supplies every
target position; recursive children use the same trace-level relation,
proxy-family, and ordered parameter valuation. -/
theorem advance_offsite_items_denote_fixed_forward
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
    (site region : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (hne : region ≠ site)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (targets : BinderTargetsAtBubble payload state)
    (bubbleEnclosesRegion : state.diagram.val.Encloses state.bubble region)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
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
      state.diagram.val.Encloses state.bubble child →
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues direction sourceFuel targetFuel child)
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
          state site arguments hadmissible).diagram.val region).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders
            payload state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload state
        atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion region)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (sourceDenotes : denoteItemSeq model named sourceEnv
      (RelEnv.pullback relationMap targetRelEnv) sourceItems) :
    denoteItemSeq model named targetEnv targetRelEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceOccurrences :=
    (ConcreteElaboration.localOccurrences coalesced.diagram.val region).filter
      (dropOccurrenceSurvives coalesced)
  let targetOccurrences :=
    (ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion region)).filter (dropOccurrenceSurvives next)
  let positions := advanceOffsiteOccurrenceEquiv comprehension attachments
    binders payload state atom tail site arguments node_eq hadmissible region hne
  have positionSpec : ∀ index,
      targetOccurrences.get (positions index) =
        layout.mapFrameOccurrence (sourceOccurrences.get index) := by
    intro index
    exact advanceOffsiteOccurrenceEquiv_spec comprehension attachments binders
      payload state atom tail site arguments node_eq hadmissible region hne index
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
    sourceBinders sourceCompiled
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (compileSurvivorRegion? signature next targetFuel) targetContext
    targetBinders targetCompiled
  apply (denoteItemSeq_iff_get model named targetEnv targetRelEnv targetItems).2
  intro targetItemIndex
  let targetOccurrenceIndex := Fin.cast targetLength targetItemIndex
  let sourceOccurrenceIndex := positions.symm targetOccurrenceIndex
  let sourceItemIndex := Fin.cast sourceLength.symm sourceOccurrenceIndex
  generalize occurrenceEq :
    sourceOccurrences.get sourceOccurrenceIndex = occurrence
  have occurrenceMember : occurrence ∈ sourceOccurrences :=
    occurrenceEq ▸ List.get_mem sourceOccurrences sourceOccurrenceIndex
  have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
    sourceBinders sourceCompiled sourceOccurrenceIndex
  have targetAt := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature next targetFuel) targetContext
    targetBinders targetCompiled targetOccurrenceIndex
  have positionEq : positions sourceOccurrenceIndex = targetOccurrenceIndex :=
    positions.right_inv targetOccurrenceIndex
  rw [← positionEq, positionSpec sourceOccurrenceIndex] at targetAt
  rw [occurrenceEq] at targetAt
  have targetItemIndexEq :
      Fin.cast targetLength.symm (positions sourceOccurrenceIndex) =
        targetItemIndex := by
    apply Fin.ext
    change (positions sourceOccurrenceIndex).val = targetItemIndex.val
    calc
      _ = targetOccurrenceIndex.val := congrArg Fin.val positionEq
      _ = targetItemIndex.val := rfl
  rw [targetItemIndexEq] at targetAt
  have sourceAt' : ConcreteElaboration.compileOccurrenceWith? signature
      spliceInput.coalesceFrameRaw
      (compileSurvivorRegion? signature coalesced sourceFuel)
      sourceContext sourceBinders occurrence =
        some (sourceItems.get sourceItemIndex) := by
    rw [← occurrenceEq]
    simpa [sourceOccurrences, coalesced, spliceInput, sourceItemIndex] using
      sourceAt
  have sourceDenotesItem : denoteItem model named sourceEnv
      (RelEnv.pullback relationMap targetRelEnv)
      (sourceItems.get sourceItemIndex) :=
    (denoteItemSeq_iff_get model named sourceEnv
      (RelEnv.pullback relationMap targetRelEnv) sourceItems).mp sourceDenotes
        sourceItemIndex
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
          (List.mem_filter.mp occurrenceMember).1
      have simulation := frameNode_simulation_of_mapped spliceInput hadmissible
        region sourceContext targetContext sourceExact targetExact sourceBinders
        targetBinders sourceCover sourceEnumeration wireMap wireSpec relationMap
        relationSpec node nodeRegion model named .forward
        (sourceItems.get sourceItemIndex) (targetItems.get targetItemIndex)
        (by simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt')
        (by simpa [layout,
          Splice.Input.PlugLayout.mapFrameOccurrence, next] using targetAt)
      have sourcePrepared :=
        (denoteItem_renameRelations model named relationMap
          (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
          (RelEnv.pullback_agrees relationMap targetRelEnv) sourceEnv
          (sourceItems.get sourceItemIndex)).mpr sourceDenotesItem
      exact simulation sourceEnv targetEnv targetRelEnv (by simpa using
        environmentEq) sourcePrepared
  | child child =>
      exact advance_site_child_denotes_fixed_forward comprehension attachments
        binders payload state atom tail site arguments node_eq hadmissible
        targets sourceFuel targetFuel region bubbleEnclosesRegion sourceContext
        targetContext sourceExact targetExact sourceBinders targetBinders
        sourceCover targetCover sourceEnumeration targetEnumeration wireMap
        wireSpec relationMap relationSpec model named relationValue values
        parameterValues sourceEnv targetEnv targetRelEnv environmentEq
        targetFixed targetProxies targetParameters childSimulation child
        occurrenceMember
        (sourceItems.get sourceItemIndex) (targetItems.get targetItemIndex)
        sourceAt'
        (by simpa [layout,
          Splice.Input.PlugLayout.mapFrameOccurrence, next] using targetAt)
        sourceDenotesItem

end InstantiationSemantic

end VisualProof.Rule
