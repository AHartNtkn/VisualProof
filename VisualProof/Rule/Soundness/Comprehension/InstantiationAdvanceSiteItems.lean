import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceAtomSemantic
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceFrameNodeSemantic

namespace VisualProof.Rule

open VisualProof.Concrete

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
    (sourceFuel targetFuel : Nat)
    (sourceContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact site)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
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
    (model : Model)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (relationsAgree : RelEnv.Agrees relationMap sourceRelEnv targetRelEnv)
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
    (targetDenotes : denoteItemSeq model  targetEnv targetRelEnv targetItems)
    (currentDenotes : ∀ sourceItem,
      Concrete.Elaboration.compileNode?
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          sourceContext sourceBinders atom = some sourceItem →
      denoteItem model  sourceEnv sourceRelEnv sourceItem)
    (childDenotes : ∀
      (child : Fin state.diagram.val.regionCount)
      (member : Concrete.Elaboration.LocalOccurrence.child child ∈
        (Concrete.Elaboration.localOccurrences
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible).diagram.val site).filter
          (dropOccurrenceSurvives
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible)))
      (sourceItem : Item  sourceContext.length sourceRels)
      (targetItem : Item  targetContext.length targetRels),
      Concrete.Elaboration.compileOccurrenceWith?
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          (compileSurvivorRegion?
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible) sourceFuel)
          sourceContext sourceBinders (.child child) = some sourceItem →
      Concrete.Elaboration.compileOccurrenceWith?
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion?
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapFrameOccurrence (.child child)) =
            some targetItem →
      denoteItem model  targetEnv targetRelEnv targetItem →
      denoteItem model  sourceEnv sourceRelEnv sourceItem) :
    denoteItemSeq model  sourceEnv sourceRelEnv sourceItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let sourceOccurrences :=
    (Concrete.Elaboration.localOccurrences coalesced.diagram.val site).filter
      (dropOccurrenceSurvives coalesced)
  apply (denoteItemSeq_iff_get model  sourceEnv sourceRelEnv sourceItems).2
  intro sourceItemIndex
  let sourceOccurrenceIndex := Fin.cast
    (Concrete.Elaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion?  coalesced sourceFuel) sourceContext
      sourceBinders sourceCompiled) sourceItemIndex
  generalize occurrenceEq : sourceOccurrences.get sourceOccurrenceIndex =
    occurrence
  have occurrenceMember : occurrence ∈ sourceOccurrences :=
    occurrenceEq ▸ List.get_mem sourceOccurrences sourceOccurrenceIndex
  have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion?  coalesced sourceFuel) sourceContext
    sourceBinders sourceCompiled sourceOccurrenceIndex
  have sourceAt' : Concrete.Elaboration.compileOccurrenceWith?
      spliceInput.coalesceFrameRaw
      (compileSurvivorRegion?  coalesced sourceFuel)
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
        simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceAt'
      · obtain ⟨targetItem, targetAt, targetItemDenotes⟩ :=
          advance_mapped_frame_item_denotes comprehension attachments binders
            payload state atom tail site arguments node_eq hadmissible site
            (.node node) occurrenceMember (by simpa using current) targetFuel
            targetContext targetBinders model  targetEnv targetRelEnv
            targetItems targetCompiled targetDenotes
        have nodeLocal := (List.mem_filter.mp occurrenceMember).1
        have nodeRegion :=
          (Concrete.Elaboration.mem_localOccurrences_node _ _ _).1 nodeLocal
        apply frameNode_denotes_of_mapped spliceInput hadmissible site
          sourceContext targetContext sourceExact targetExact sourceBinders
          targetBinders sourceCover sourceEnumeration wireMap wireSpec
          relationMap relationSpec node nodeRegion model  sourceEnv targetEnv
          environmentEq sourceRelEnv targetRelEnv relationsAgree
          (sourceItems.get sourceItemIndex) targetItem
        · simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceAt'
        · simpa [layout, Concrete.Splice.Input.PlugLayout.mapFrameOccurrence,
            Concrete.Elaboration.compileOccurrenceWith?] using targetAt
        · exact targetItemDenotes
  | child child =>
      obtain ⟨targetItem, targetAt, targetItemDenotes⟩ :=
        advance_mapped_frame_item_denotes comprehension attachments binders
          payload state atom tail site arguments node_eq hadmissible site
          (.child child) occurrenceMember (by simp) targetFuel targetContext
          targetBinders model  targetEnv targetRelEnv targetItems
          targetCompiled targetDenotes
      exact childDenotes child occurrenceMember (sourceItems.get sourceItemIndex)
        targetItem sourceAt' targetAt targetItemDenotes

end InstantiationSemantic

end VisualProof.Rule
