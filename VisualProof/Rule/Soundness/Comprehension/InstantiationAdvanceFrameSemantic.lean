import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredRegionSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Every surviving frame occurrence other than the atom currently being
replaced occurs in the next survivor traversal at its exact frame image.  The
statement covers both the splice site and every off-site compiler frame. -/
theorem advance_mapFrameOccurrence_mem_survivors
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
    (region : Fin state.diagram.val.regionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence
      state.diagram.val.regionCount state.diagram.val.nodeCount)
    (sourceMember : occurrence ∈
      (ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val region).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible)))
    (notCurrent : occurrence ≠ .node atom) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    layout.mapFrameOccurrence occurrence ∈
      (ConcreteElaboration.localOccurrences next.diagram.val
        (layout.frameRegion region)).filter (dropOccurrenceSurvives next) := by
  dsimp only
  by_cases hsite : region = site
  · subst region
    apply (advance_site_survivor_occurrences_iff comprehension attachments
      binders payload state atom tail site arguments hadmissible
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapFrameOccurrence occurrence)).2
    exact Or.inl ⟨occurrence,
      (List.mem_filter.mp sourceMember).1,
      by
        rw [← coalesced_dropOccurrenceSurvives comprehension attachments
          binders payload state site arguments hadmissible]
        exact (List.mem_filter.mp sourceMember).2,
      notCurrent, rfl⟩
  · exact (advance_offsite_survivor_occurrences_iff comprehension attachments
      binders payload state atom tail site arguments node_eq hadmissible region
      hsite
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapFrameOccurrence occurrence)).2
      ⟨occurrence, sourceMember, rfl⟩

/-- A denoting next-state survivor block therefore supplies the compiled item
at the exact frame image of any retained non-current source occurrence. -/
theorem advance_mapped_frame_item_denotes
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
    (region : Fin state.diagram.val.regionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence
      state.diagram.val.regionCount state.diagram.val.nodeCount)
    (sourceMember : occurrence ∈
      (ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val region).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible)))
    (notCurrent : occurrence ≠ .node atom)
    {rels : RelCtx}
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext
      (advanceInstantiationState comprehension attachments binders payload state
        atom tail site arguments hadmissible).diagram.val)
    (relBinders : ConcreteElaboration.BinderContext
      (advanceInstantiationState comprehension attachments binders payload state
        atom tail site arguments hadmissible).diagram.val rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (survivorItems : ItemSeq signature context.length rels)
    (survivorCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload state
        atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) fuel)
      context relBinders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion region)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some survivorItems)
    (survivorDenotes : denoteItemSeq model named env relEnv survivorItems) :
    let layout := (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).plugLayout
    ∃ targetItem : Item signature context.length rels,
      ConcreteElaboration.compileOccurrenceWith? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        (compileSurvivorRegion? signature
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible) fuel)
        context relBinders (layout.mapFrameOccurrence occurrence) =
          some targetItem ∧
      denoteItem model named env relEnv targetItem := by
  dsimp only
  let layout := (instantiateSpliceInput comprehension attachments binders
    payload state site arguments).plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let targetOccurrences :=
    (ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion region)).filter (dropOccurrenceSurvives next)
  have targetMember : layout.mapFrameOccurrence occurrence ∈ targetOccurrences :=
    advance_mapFrameOccurrence_mem_survivors comprehension attachments binders
      payload state atom tail site arguments node_eq hadmissible region
      occurrence sourceMember notCurrent
  obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ :=
    indexOf?_complete targetMember
  have occurrenceEq : targetOccurrences.get occurrenceIndex =
      layout.mapFrameOccurrence occurrence :=
    indexOf?_sound occurrenceIndexEq
  let itemIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature next fuel) context relBinders
      survivorCompiled).symm occurrenceIndex
  have targetCompiled := ConcreteElaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion? signature next fuel) context relBinders
    survivorCompiled occurrenceIndex
  rw [occurrenceEq] at targetCompiled
  refine ⟨survivorItems.get itemIndex, targetCompiled, ?_⟩
  exact (denoteItemSeq_iff_get model named env relEnv survivorItems).mp
    survivorDenotes itemIndex

end InstantiationSemantic

end VisualProof.Rule
