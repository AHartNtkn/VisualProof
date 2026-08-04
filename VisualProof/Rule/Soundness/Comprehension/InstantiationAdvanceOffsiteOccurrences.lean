import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceAtomSemantic
import VisualProof.Diagram.Concrete.Subgraph.Splice.Trace

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Diagram.Splice

namespace InstantiationSemantic

/-- Away from the active splice site, the next survivor occurrences are
exactly the injective frame images of the coalesced source survivors.  The
current atom cannot occur in an off-site local list. -/
theorem advance_offsite_survivor_occurrences_iff
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
    (hne : region ≠ site)
    (occurrence : ConcreteElaboration.LocalOccurrence
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.regionCount
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let coalesced := coalescedInstantiationState comprehension attachments
      binders payload state site arguments hadmissible
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    occurrence ∈
        (ConcreteElaboration.localOccurrences next.diagram.val
          (layout.frameRegion region)).filter (dropOccurrenceSurvives next) ↔
      ∃ sourceOccurrence,
        sourceOccurrence ∈
          (ConcreteElaboration.localOccurrences coalesced.diagram.val
            region).filter (dropOccurrenceSurvives coalesced) ∧
        occurrence = layout.mapFrameOccurrence sourceOccurrence := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  constructor
  · intro member
    have localMember := (List.mem_filter.mp member).1
    have survives := (List.mem_filter.mp member).2
    obtain ⟨sourceOccurrence, sourceLocal, mappedEq⟩ :=
      layout.frameSemanticOccurrences_complete region hne occurrence localMember
    subst occurrence
    have survivorFacts :=
      (advance_mapFrameOccurrence_survives_iff comprehension attachments binders
        payload state atom tail site arguments hadmissible sourceOccurrence).mp
        survives
    refine ⟨sourceOccurrence, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨sourceLocal, ?_⟩
    rw [coalesced_dropOccurrenceSurvives]
    exact survivorFacts.1
  · rintro ⟨sourceOccurrence, sourceMember, rfl⟩
    have sourceLocal := (List.mem_filter.mp sourceMember).1
    have sourceSurvives : dropOccurrenceSurvives state sourceOccurrence = true :=
      by
        rw [← coalesced_dropOccurrenceSurvives comprehension attachments
          binders payload state site arguments hadmissible]
        exact (List.mem_filter.mp sourceMember).2
    have notCurrent : sourceOccurrence ≠ .node atom := by
      intro equality
      subst sourceOccurrence
      have atomAtRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 sourceLocal
      have atomAtRegionState :
          (state.diagram.val.nodes atom).region = region := by
        simpa [coalesced, coalescedInstantiationState, spliceInput] using
          atomAtRegion
      rw [node_eq] at atomAtRegionState
      exact hne atomAtRegionState.symm
    rw [List.mem_filter]
    refine ⟨(layout.mapFrameOccurrence_mem_localOccurrences region
      sourceOccurrence).2 sourceLocal, ?_⟩
    exact (advance_mapFrameOccurrence_survives_iff comprehension attachments
      binders payload state atom tail site arguments hadmissible
      sourceOccurrence).2 ⟨sourceSurvives, notCurrent⟩

/-- Proof-relevant permutation between the two off-site filtered occurrence
lists.  It preserves conjunction semantics without imposing incidental dense
enumeration order as a logical requirement. -/
noncomputable def advanceOffsiteOccurrenceEquiv
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
    (hne : region ≠ site) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let coalesced := coalescedInstantiationState comprehension attachments
      binders payload state site arguments hadmissible
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    FiniteEquiv
      (Fin ((ConcreteElaboration.localOccurrences coalesced.diagram.val
        region).filter (dropOccurrenceSurvives coalesced)).length)
      (Fin ((ConcreteElaboration.localOccurrences next.diagram.val
        (layout.frameRegion region)).filter
          (dropOccurrenceSurvives next)).length) := by
  dsimp only
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
  exact listEmbeddingEquiv layout.mapFrameOccurrence sourceOccurrences
    targetOccurrences
    ((ConcreteElaboration.localOccurrences_nodup _ _).filter _)
    ((ConcreteElaboration.localOccurrences_nodup _ _).filter _)
    (fun source member =>
      (advance_offsite_survivor_occurrences_iff comprehension attachments binders
        payload state atom tail site arguments node_eq hadmissible region hne
        (layout.mapFrameOccurrence source)).2 ⟨source, member, rfl⟩)
    (fun target member => by
      obtain ⟨source, sourceMember, equality⟩ :=
        (advance_offsite_survivor_occurrences_iff comprehension attachments
          binders payload state atom tail site arguments node_eq hadmissible
          region hne target).1 member
      exact ⟨source, sourceMember, equality.symm⟩)
    (fun left _ right _ equality =>
      layout.mapFrameOccurrence_injective equality)

/-- At every source filtered position, the target filtered list contains its
exact frame image at the occurrence equivalence position. -/
theorem advanceOffsiteOccurrenceEquiv_spec
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
    (hne : region ≠ site)
    (index : Fin
      ((ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val region).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))).length) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let coalesced := coalescedInstantiationState comprehension attachments
      binders payload state site arguments hadmissible
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    ((ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion region)).filter
        (dropOccurrenceSurvives next)).get
      (advanceOffsiteOccurrenceEquiv comprehension attachments binders payload
        state atom tail site arguments node_eq hadmissible region hne index) =
      layout.mapFrameOccurrence
        (((ConcreteElaboration.localOccurrences coalesced.diagram.val
          region).filter (dropOccurrenceSurvives coalesced)).get index) := by
  dsimp only
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
  unfold advanceOffsiteOccurrenceEquiv
  exact listEmbeddingEquiv_spec layout.mapFrameOccurrence sourceOccurrences
    targetOccurrences
    ((ConcreteElaboration.localOccurrences_nodup _ _).filter _)
    ((ConcreteElaboration.localOccurrences_nodup _ _).filter _)
    (fun source member =>
      (advance_offsite_survivor_occurrences_iff comprehension attachments binders
        payload state atom tail site arguments node_eq hadmissible region hne
        (layout.mapFrameOccurrence source)).2 ⟨source, member, rfl⟩)
    (fun target member => by
      obtain ⟨source, sourceMember, equality⟩ :=
        (advance_offsite_survivor_occurrences_iff comprehension attachments
          binders payload state atom tail site arguments node_eq hadmissible
          region hne target).1 member
      exact ⟨source, sourceMember, equality.symm⟩)
    (fun left _ right _ equality =>
      layout.mapFrameOccurrence_injective equality)
    index

end InstantiationSemantic

end VisualProof.Rule
