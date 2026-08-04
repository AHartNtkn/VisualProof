import VisualProof.Rule.Soundness.Comprehension.InstantiationEmptySemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- The head selected by an executor step has not already been processed. -/
theorem step_atom_not_processed
    (state : InstantiationState origin parameterCount proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup) :
    atom ∉ state.processedAtoms := by
  rw [InstantiationState.ownedAtoms, pending_eq, List.nodup_append]
    at ownedNodup
  intro member
  exact ownedNodup.2.2 atom member atom (by simp) rfl

/-- A retained frame node survives the next compaction exactly when it already
survived and is not the atom processed by this splice. -/
theorem advance_frameNode_survives_iff
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
    (node : Fin state.diagram.val.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    dropOccurrenceSurvives next (.node (layout.frameNode node)) = true ↔
      dropOccurrenceSurvives state (.node node) = true ∧ node ≠ atom := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  simp only [dropOccurrenceSurvives, instantiationAtomDomain,
    decide_eq_true_eq, advanceInstantiationState]
  change layout.frameNode node ∉
      state.processedAtoms.map layout.frameNode ++ [layout.frameNode atom] ↔
    node ∉ state.processedAtoms ∧ node ≠ atom
  constructor
  · intro survives
    refine ⟨?_, ?_⟩
    · intro member
      apply survives
      rw [List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨node, member, rfl⟩)
    · intro equality
      apply survives
      rw [List.mem_append]
      exact Or.inr (by simpa [equality])
  · rintro ⟨oldSurvives, notCurrent⟩ member
    rw [List.mem_append] at member
    cases member with
    | inl mapped =>
        obtain ⟨original, originalMember, mappedEq⟩ := List.mem_map.mp mapped
        have originalEq : original = node :=
          layout.frameNode_injective mappedEq
        exact oldSurvives (originalEq ▸ originalMember)
    | inr current =>
        have mappedEq : layout.frameNode node = layout.frameNode atom := by
          simpa using current
        exact notCurrent (layout.frameNode_injective mappedEq)

/-- Material pattern nodes are disjoint from every processed frame-node image,
so the survivor compiler never filters newly inserted pattern nodes. -/
theorem advance_patternNode_survives
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
    (node : Fin comprehension.val.diagram.nodeCount) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    dropOccurrenceSurvives next (.node (layout.patternNode node)) = true := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  simp only [dropOccurrenceSurvives, instantiationAtomDomain,
    decide_eq_true_eq, advanceInstantiationState]
  change layout.patternNode node ∉
    state.processedAtoms.map layout.frameNode ++ [layout.frameNode atom]
  intro member
  rw [List.mem_append] at member
  cases member with
  | inl mapped =>
      obtain ⟨frameNode, _, equality⟩ := List.mem_map.mp mapped
      exact layout.frameNode_ne_patternNode frameNode node equality
  | inr current =>
      have reverse : layout.patternNode node = layout.frameNode atom := by
        simpa using current
      have equality : layout.frameNode atom = layout.patternNode node :=
        reverse.symm
      exact layout.frameNode_ne_patternNode atom node equality

/-- Child-region occurrences are never removed by atom compaction. -/
@[simp] theorem dropOccurrenceSurvives_child
    (state : InstantiationState origin parameterCount proxyCount)
    (region : Fin state.diagram.val.regionCount) :
    dropOccurrenceSurvives state (.child region) = true :=
  rfl

/-- Before the step, the selected pending atom is present in the survivor
compiler. -/
theorem step_atom_survives
    (state : InstantiationState origin parameterCount proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup) :
    dropOccurrenceSurvives state (.node atom) = true := by
  simp only [dropOccurrenceSurvives, instantiationAtomDomain,
    decide_eq_true_eq]
  exact step_atom_not_processed state atom tail pending_eq ownedNodup

end InstantiationSemantic

end VisualProof.Rule
