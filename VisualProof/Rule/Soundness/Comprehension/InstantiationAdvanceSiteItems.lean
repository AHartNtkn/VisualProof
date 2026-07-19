import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceAtomSemantic
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceFrameNodeSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Backward semantic transport for the survivor conjunction at the splice
site.  The selected atom is reconstructed by the caller from the inserted
comprehension; every other retained frame occurrence is recovered from its
exact frame image in the denoting target survivor block.  Inserted target
conjuncts need no inverse image. -/
theorem advance_site_items_denote
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
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact site)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
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
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (relationsAgree : RelEnv.Agrees relationMap sourceRelEnv targetRelEnv)
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
    (targetDenotes : denoteItemSeq model named targetEnv targetRelEnv targetItems)
    (currentDenotes : ∀ sourceItem,
      ConcreteElaboration.compileNode? signature
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          sourceContext sourceBinders atom = some sourceItem →
      denoteItem model named sourceEnv sourceRelEnv sourceItem)
    (childDenotes : ∀
      (child : Fin state.diagram.val.regionCount)
      (member : ConcreteElaboration.LocalOccurrence.child child ∈
        (ConcreteElaboration.localOccurrences
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible).diagram.val site).filter
          (dropOccurrenceSurvives
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible)))
      (sourceItem : Item signature sourceContext.length sourceRels)
      (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          (compileSurvivorRegion? signature
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible) sourceFuel)
          sourceContext sourceBinders (.child child) = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion? signature
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapFrameOccurrence (.child child)) =
            some targetItem →
      denoteItem model named targetEnv targetRelEnv targetItem →
      denoteItem model named sourceEnv sourceRelEnv sourceItem) :
    denoteItemSeq model named sourceEnv sourceRelEnv sourceItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let sourceOccurrences :=
    (ConcreteElaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  apply (denoteItemSeq_iff_get model named sourceEnv sourceRelEnv sourceItems).2
  intro sourceItemIndex
  let sourceOccurrenceIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
      sourceBinders sourceCompiled) sourceItemIndex
  generalize occurrenceEq : sourceOccurrences.get sourceOccurrenceIndex =
    occurrence
  have occurrenceMember : occurrence ∈ sourceOccurrences :=
    occurrenceEq ▸ List.get_mem sourceOccurrences sourceOccurrenceIndex
  have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature coalesced sourceFuel) sourceContext
    sourceBinders sourceCompiled sourceOccurrenceIndex
  have sourceAt' : ConcreteElaboration.compileOccurrenceWith? signature
      spliceInput.coalesceFrameRaw
      (compileSurvivorRegion? signature coalesced sourceFuel)
      sourceContext sourceBinders occurrence =
        some (sourceItems.get sourceItemIndex) := by
    rw [← occurrenceEq]
    simpa [sourceOccurrences, sourceOccurrenceIndex, coalesced, spliceInput]
      using sourceAt
  cases occurrence with
  | node node =>
      by_cases current : node = atom
      · subst node
        apply currentDenotes (sourceItems.get sourceItemIndex)
        simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt'
      · obtain ⟨targetItem, targetAt, targetItemDenotes⟩ :=
          advance_mapped_frame_item_denotes comprehension attachments binders
            payload state atom tail site arguments node_eq hadmissible site
            (.node node) occurrenceMember (by simpa using current) targetFuel
            targetContext targetBinders model named targetEnv targetRelEnv
            targetItems targetCompiled targetDenotes
        have nodeLocal := (List.mem_filter.mp occurrenceMember).1
        have nodeRegion :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 nodeLocal
        apply frameNode_denotes_of_mapped spliceInput hadmissible site
          sourceContext targetContext sourceExact targetExact sourceBinders
          targetBinders sourceCover sourceEnumeration wireMap wireSpec
          relationMap relationSpec node nodeRegion model named sourceEnv targetEnv
          environmentEq sourceRelEnv targetRelEnv relationsAgree
          (sourceItems.get sourceItemIndex) targetItem
        · simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt'
        · simpa [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?] using targetAt
        · exact targetItemDenotes
  | child child =>
      obtain ⟨targetItem, targetAt, targetItemDenotes⟩ :=
        advance_mapped_frame_item_denotes comprehension attachments binders
          payload state atom tail site arguments node_eq hadmissible site
          (.child child) occurrenceMember (by simp) targetFuel targetContext
          targetBinders model named targetEnv targetRelEnv targetItems
          targetCompiled targetDenotes
      exact childDenotes child occurrenceMember (sourceItems.get sourceItemIndex)
        targetItem sourceAt' targetAt targetItemDenotes

end InstantiationSemantic

end VisualProof.Rule
