import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSurvivors

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Occurrence-level form of the frame-node survivor theorem.  Child regions
always survive, while the current frame atom is the single new rejection. -/
theorem advance_mapFrameOccurrence_survives_iff
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
    (occurrence : ConcreteElaboration.LocalOccurrence
      state.diagram.val.regionCount state.diagram.val.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    dropOccurrenceSurvives next (layout.mapFrameOccurrence occurrence) = true ↔
      dropOccurrenceSurvives state occurrence = true ∧
        occurrence ≠ .node atom := by
  cases occurrence with
  | node node =>
      simpa [Splice.Input.PlugLayout.mapFrameOccurrence] using
        (advance_frameNode_survives_iff comprehension attachments binders
          payload state atom tail site arguments hadmissible node)
  | child child =>
      dsimp only
      simp only [Splice.Input.PlugLayout.mapFrameOccurrence,
        dropOccurrenceSurvives]
      exact ⟨fun _ => by simp, fun _ => trivial⟩

/-- Every occurrence contributed by the inserted pattern survives the next
atom compaction. -/
theorem advance_mapPatternOccurrence_survives
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
    (occurrence : ConcreteElaboration.LocalOccurrence
      comprehension.val.diagram.regionCount
      comprehension.val.diagram.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    dropOccurrenceSurvives next
      (layout.mapPatternOccurrence occurrence) = true := by
  cases occurrence with
  | node node =>
      exact advance_patternNode_survives comprehension attachments binders
        payload state atom tail site arguments hadmissible node
  | child child => rfl

/-- Exact set-level description of the survivor occurrences at the splice
site: surviving old frame occurrences except the selected atom, followed (up
to the compiler's finite permutation) by every terminal pattern occurrence. -/
theorem advance_site_survivor_occurrences_iff
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
    (occurrence : ConcreteElaboration.LocalOccurrence
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.regionCount
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    occurrence ∈
        (ConcreteElaboration.localOccurrences next.diagram.val
          (layout.frameRegion site)).filter (dropOccurrenceSurvives next) ↔
      (∃ frameOccurrence,
        frameOccurrence ∈ ConcreteElaboration.localOccurrences
          state.diagram.val site ∧
        dropOccurrenceSurvives state frameOccurrence = true ∧
        frameOccurrence ≠ .node atom ∧
        occurrence = layout.mapFrameOccurrence frameOccurrence) ∨
      (∃ patternOccurrence,
        patternOccurrence ∈ ConcreteElaboration.localOccurrences
          comprehension.val.diagram payload.binderSpine.bodyContainer ∧
        occurrence = layout.mapPatternOccurrence patternOccurrence) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  constructor
  · intro member
    have fullMember : occurrence ∈ ConcreteElaboration.localOccurrences
        layout.plugRaw (layout.frameRegion site) := by
      exact (List.mem_filter.mp member).1
    have survives : dropOccurrenceSurvives next occurrence = true :=
      (List.mem_filter.mp member).2
    have semanticMember := layout.semanticSiteOccurrences_complete occurrence
      fullMember
    rw [Splice.Input.PlugLayout.semanticSiteOccurrences,
      List.mem_append] at semanticMember
    cases semanticMember with
    | inl frameMember =>
        obtain ⟨frameOccurrence, frameLocal, equality⟩ :=
          List.mem_map.mp frameMember
        subst occurrence
        have survivorFacts :=
          (advance_mapFrameOccurrence_survives_iff comprehension attachments
            binders payload state atom tail site arguments hadmissible
            frameOccurrence).mp survives
        exact Or.inl ⟨frameOccurrence, frameLocal, survivorFacts.1,
          survivorFacts.2, rfl⟩
    | inr patternMember =>
        obtain ⟨patternOccurrence, patternLocal, equality⟩ :=
          List.mem_map.mp patternMember
        exact Or.inr ⟨patternOccurrence, patternLocal, equality.symm⟩
  · intro represented
    rw [List.mem_filter]
    cases represented with
    | inl frame =>
        obtain ⟨frameOccurrence, frameLocal, frameSurvives, notCurrent,
          rfl⟩ := frame
        refine ⟨?_, ?_⟩
        · exact (layout.mapFrameOccurrence_mem_localOccurrences site
            frameOccurrence).2 frameLocal
        · exact (advance_mapFrameOccurrence_survives_iff comprehension
            attachments binders payload state atom tail site arguments
            hadmissible frameOccurrence).2 ⟨frameSurvives, notCurrent⟩
    | inr pattern =>
        obtain ⟨patternOccurrence, patternLocal, rfl⟩ := pattern
        refine ⟨?_, ?_⟩
        · exact layout.mapPatternOccurrence_mem_localOccurrences_of_mem
            patternOccurrence patternLocal
        · exact advance_mapPatternOccurrence_survives comprehension attachments
            binders payload state atom tail site arguments hadmissible
            patternOccurrence

end InstantiationSemantic

end VisualProof.Rule
