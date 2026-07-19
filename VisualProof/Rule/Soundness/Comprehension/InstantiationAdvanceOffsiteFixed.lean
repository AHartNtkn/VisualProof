import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteBackward
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteItems

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Backward fixed-relation transport for the survivor conjunction of a frame
region strictly below the moving bubble and distinct from the splice site. -/
theorem advance_offsite_items_denote_fixed
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
          site arguments).plugLayout.frameRegion region)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (targetDenotes : denoteItemSeq model named targetEnv targetRelEnv targetItems) :
    denoteItemSeq model named sourceEnv
      (RelEnv.pullback relationMap targetRelEnv) sourceItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  apply (denoteItemSeq_iff_get model named sourceEnv
    (RelEnv.pullback relationMap targetRelEnv) sourceItems).2
  intro sourceItemIndex
  let sourceOccurrenceIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
      sourceBinders sourceCompiled) sourceItemIndex
  generalize occurrenceEq :
    ((ConcreteElaboration.localOccurrences coalesced.diagram.val region).filter
      (dropOccurrenceSurvives coalesced)).get sourceOccurrenceIndex = occurrence
  have occurrenceMember := occurrenceEq ▸ List.get_mem
    ((ConcreteElaboration.localOccurrences coalesced.diagram.val region).filter
      (dropOccurrenceSurvives coalesced)) sourceOccurrenceIndex
  have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
    sourceBinders sourceCompiled sourceOccurrenceIndex
  have sourceAt' : ConcreteElaboration.compileOccurrenceWith? signature
      spliceInput.coalesceFrameRaw
      (compileSurvivorRegion? signature coalesced sourceFuel)
      sourceContext sourceBinders occurrence =
        some (sourceItems.get sourceItemIndex) := by
    rw [← occurrenceEq]
    simpa [coalesced, spliceInput, sourceOccurrenceIndex] using sourceAt
  obtain ⟨targetItem, targetAt, targetItemDenotes⟩ :=
    advance_mapped_frame_item_denotes comprehension attachments binders payload
      state atom tail site arguments node_eq hadmissible region occurrence
      occurrenceMember (by
        cases occurrence with
        | child => simp
        | node node =>
            intro equality
            have nodeEq : node = atom :=
              ConcreteElaboration.LocalOccurrence.node.inj equality
            subst node
            have coalescedNode : coalesced.diagram.val.nodes atom =
                .atom site coalesced.bubble := by
              simpa [coalesced, coalescedInstantiationState, spliceInput]
                using node_eq
            have atomRegion :
                (coalesced.diagram.val.nodes atom).region = site := by
              rw [coalescedNode]
              rfl
            have localRegion :=
              (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
                (List.mem_filter.mp occurrenceMember).1
            have siteEqRegion : site = region := by
              simpa [atomRegion] using localRegion
            exact hne siteEqRegion.symm)
      targetFuel targetContext targetBinders model named targetEnv targetRelEnv
      targetItems targetCompiled targetDenotes
  cases occurrence with
  | node node =>
      have nodeRegion := (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
        (List.mem_filter.mp occurrenceMember).1
      exact frameNode_denotes_of_mapped spliceInput hadmissible region
        sourceContext targetContext sourceExact targetExact sourceBinders
        targetBinders sourceCover sourceEnumeration wireMap wireSpec relationMap
        relationSpec node nodeRegion model named sourceEnv targetEnv environmentEq
        (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
        (RelEnv.pullback_agrees relationMap targetRelEnv)
        (sourceItems.get sourceItemIndex) targetItem
        (by simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt')
        (by simpa [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
          ConcreteElaboration.compileOccurrenceWith?] using targetAt)
        targetItemDenotes
  | child child =>
      exact advance_site_child_denotes_fixed comprehension attachments binders
        payload state atom tail site arguments node_eq hadmissible targets
        sourceFuel targetFuel region bubbleEnclosesRegion sourceContext
        targetContext sourceExact targetExact sourceBinders targetBinders
        sourceCover targetCover sourceEnumeration targetEnumeration wireMap
        wireSpec relationMap relationSpec model named relationValue values
        parameterValues
        sourceEnv targetEnv targetRelEnv environmentEq targetFixed targetProxies
        targetParameters childSimulation child occurrenceMember
        (sourceItems.get sourceItemIndex)
        targetItem sourceAt' targetAt targetItemDenotes

end InstantiationSemantic

end VisualProof.Rule
