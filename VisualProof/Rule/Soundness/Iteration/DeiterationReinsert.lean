import VisualProof.Rule.Soundness.Iteration.DeiterationExtraction

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

noncomputable def deiterationExtraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    CheckedExtraction signature input selection where
  raw := {}
  fragment :=
    ⟨input.val.extractOpenRaw selection {},
      ConcreteDiagram.extractOpenRaw_wellFormed input selection {}⟩
  fragment_eq := rfl

noncomputable def deiterationDecomposition
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    Decomposition signature input selection where
  frameDomains := deiterationDomains input selection
  frame :=
    ⟨input.val.removeRaw selection (deiterationDomains input selection),
      ConcreteDiagram.removeRaw_wellFormed input selection
        (deiterationDomains input selection)⟩
  frame_eq := rfl
  extraction := deiterationExtraction input selection

noncomputable def deiterationRemoved
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) : CheckedDiagram signature :=
  (deiterationDecomposition input selection).frame

noncomputable def deiterationReinsertTarget
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    Fin (deiterationRemoved input selection).val.regionCount :=
  Splice.Decomposition.originalSite
    (deiterationDecomposition input selection)

noncomputable def deiterationReinsertInput
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) : Splice.Input signature :=
  iterationInput (deiterationRemoved input selection)
    (deiterationRetainedSelection input selection witness)
    (deiterationReinsertTarget input selection)

@[simp] theorem deiterationRemoved_val
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    (deiterationRemoved input selection).val =
      input.val.removeRaw selection (deiterationDomains input selection) := rfl

@[simp] theorem deiterationReinsertInput_frame
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationReinsertInput input selection witness).frame =
      deiterationRemoved input selection := rfl

@[simp] theorem deiterationReinsertInput_site
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationReinsertInput input selection witness).site =
      deiterationReinsertTarget input selection := rfl

theorem deiterationSelectedRegions_length_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    witness.justifier.selectedRegions.length =
      selection.selectedRegions.length := by
  have regionCountEq := witness.occurrence.diagram.regionCount_eq
  have externalCountEq := congrArg List.length witness.sameExternalBinders
  simp only [selectedFragment, ConcreteDiagram.extractOpenRaw,
    ConcreteDiagram.extractDiagramRaw, FragmentLayout.regionCount,
    FragmentLayout.proxyCount, FragmentLayout.materialRegionCount] at regionCountEq
  omega

theorem deiterationJustifier_not_selects_selectionAnchor
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    ¬ witness.justifier.val.SelectsRegion selection.val.anchor := by
  intro selectedAnchor
  have anchorMember : selection.val.anchor ∈
      witness.justifier.selectedRegions :=
    (witness.justifier.mem_selectedRegions selection.val.anchor).2
      selectedAnchor
  by_cases empty : selection.selectedRegions = []
  · have justifierEmpty : witness.justifier.selectedRegions = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro region member
      have positive : witness.justifier.selectedRegions.length ≠ 0 := by
        intro lengthZero
        have listZero : witness.justifier.selectedRegions = [] :=
          List.eq_nil_of_length_eq_zero lengthZero
        rw [listZero] at member
        contradiction
      have selectionZero : selection.selectedRegions.length = 0 := by
        simp [empty]
      rw [deiterationSelectedRegions_length_eq input selection witness,
        selectionZero] at positive
      omega
    rw [justifierEmpty] at anchorMember
    contradiction
  · cases regionsEq : selection.selectedRegions with
    | nil => exact False.elim (empty regionsEq)
    | cons region tail =>
      have regionMember : region ∈ selection.selectedRegions := by
        rw [regionsEq]
        exact List.mem_cons_self
      have anchorEnclosesRegion :
          input.val.Encloses selection.val.anchor region := by
        obtain ⟨child, childMember, childEncloses⟩ :=
          (selection.mem_selectedRegions region).1 regionMember
        have anchorEnclosesChild :
            input.val.Encloses selection.val.anchor child := by
          have positive := child.isLt
          refine ⟨⟨1, by omega⟩, ?_⟩
          simp [ConcreteDiagram.climb,
            selection.property.childRoots_direct child childMember]
        exact ConcreteElaboration.checked_encloses_trans input.property
          anchorEnclosesChild childEncloses
      have selectedRegion : witness.justifier.val.SelectsRegion region :=
        SelectionRequest.SelectsRegion.downward input.property selectedAnchor
          anchorEnclosesRegion
      exact witness.regions_disjoint region
        ((witness.justifier.mem_selectedRegions region).2 selectedRegion)
        regionMember

theorem deiterationSelectionAnchor_survives
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    (deiterationDomains input selection).regions.survives
        selection.val.anchor = true := by
  apply ((deiterationDomains input selection).region_survives_iff _).2
  right
  intro selected
  obtain ⟨child, childMember, childEncloses⟩ :=
    (selection.mem_selectedRegions selection.val.anchor).1 selected
  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
    input.property (selection.property.childRoots_direct child childMember)
    childEncloses

theorem deiterationReinsert_encloses
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRemoved input selection).val.Encloses
      (deiterationRetainedSelection input selection witness).val.anchor
      (deiterationReinsertTarget input selection) := by
  let domains := deiterationDomains input selection
  have transported := ConcreteDiagram.removeRaw_encloses input selection domains
    (deiterationJustifierAnchor_survives input selection witness)
    (deiterationSelectionAnchor_survives input selection)
    witness.ancestor
  simpa [domains, deiterationRemoved, deiterationDecomposition,
    deiterationReinsertTarget, Splice.Decomposition.originalSite,
    deiterationRetainedSelection, deiterationRetainedRequest] using transported

theorem deiterationReinsert_not_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    ¬ (deiterationRetainedSelection input selection witness).val.SelectsRegion
      (deiterationReinsertTarget input selection) := by
  change ¬ (deiterationRetainedRequest input selection witness).SelectsRegion
    (deiterationReinsertTarget input selection)
  rw [deiterationRetained_selectsRegion_iff]
  have survives := deiterationSelectionAnchor_survives input selection
  have targetEq : deiterationReinsertTarget input selection =
      (deiterationDomains input selection).regions.index
        selection.val.anchor survives := by
    rfl
  rw [targetEq]
  rw [(deiterationDomains input selection).regions.origin_index]
  exact deiterationJustifier_not_selects_selectionAnchor input selection witness

theorem deiterationReinsertInput_admissible
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationReinsertInput input selection witness).Admissible where
  attachments_visible := by
    intro position
    let frame := deiterationRemoved input selection
    let retained := deiterationRetainedSelection input selection witness
    let layout : FragmentLayout frame.val retained := {}
    let touch : Fin retained.touchingWires.length := Fin.cast (by
      change (frame.val.extractBoundaryRaw retained layout).length =
        retained.touchingWires.length
      exact frame.val.extractBoundaryRaw_length retained layout) position
    have touching := Splice.Decomposition.touchingWire_scope_encloses_anchor
      frame retained touch
    have target := deiterationReinsert_encloses input selection witness
    have combined := ConcreteElaboration.checked_encloses_trans frame.property
      touching target
    simpa [deiterationReinsertInput, iterationInput, frame, retained, layout,
      touch] using combined
  binder_targets_injective := by
    intro left right equality
    change (deiterationRetainedLayout input selection witness).externalBinders.get
        left =
      (deiterationRetainedLayout input selection witness).externalBinders.get
        right at equality
    exact (deiterationRetainedLayout input selection witness)
      |>.externalBinderTarget_injective equality
  binder_targets_match := by
    intro index
    exact ConcreteDiagram.extractedBinderSpine_target_region
      (deiterationRemoved input selection)
      (deiterationRetainedSelection input selection witness)
      (deiterationRetainedLayout input selection witness) index
  binder_targets_enclose := by
    intro index
    let frame := deiterationRemoved input selection
    let retained := deiterationRetainedSelection input selection witness
    let layout := deiterationRetainedLayout input selection witness
    have member : layout.externalBinders.get index ∈
        retained.externalBinders := by
      rw [← layout.externalBinders_exact]
      exact List.get_mem _ _
    have binderAnchor := retained.usesExternalBinder_encloses_anchor frame
      ((retained.mem_externalBinders_iff_uses frame
        (layout.externalBinders.get index)).1 member)
    have anchorTarget := deiterationReinsert_encloses input selection witness
    have combined := ConcreteElaboration.checked_encloses_trans frame.property
      binderAnchor anchorTarget
    simpa [deiterationReinsertInput, iterationInput, frame, retained, layout]
      using combined

/-- The certified inverse insertion is accepted by the splice checker for
every executor-accepted deiteration witness. -/
theorem deiterationReinsert_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    ∃ result, Splice.Input.spliceChecked signature
      (deiterationReinsertInput input selection witness) = .ok result :=
  (deiterationReinsertInput input selection witness).spliceChecked_complete
    (deiterationReinsertInput_admissible input selection witness)

noncomputable def deiterationReinsertResult
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) : CheckedDiagram signature :=
  Classical.choose (deiterationReinsert_complete input selection witness)

theorem deiterationReinsertResult_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    Splice.Input.spliceChecked signature
        (deiterationReinsertInput input selection witness) =
      .ok (deiterationReinsertResult input selection witness) :=
  Classical.choose_spec (deiterationReinsert_complete input selection witness)

/-- The public iteration executor accepts the certified inverse insertion;
the enclosing, non-selection, and checked-splice branches are all discharged
from the deiteration witness rather than assumed. -/
theorem applyIteration_deiterationReinsert_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    ∃ receipt, applyIteration (deiterationRemoved input selection)
      (deiterationRetainedSelection input selection witness)
      (deiterationReinsertTarget input selection) = .ok receipt := by
  unfold applyIteration
  rw [if_pos (deiterationReinsert_encloses input selection witness)]
  split
  · rename_i selected
    exact False.elim
      (deiterationReinsert_not_selected input selection witness selected)
  · split
    · rename_i error hsplice
      have accepted : Splice.Input.spliceChecked signature
          (iterationInput (deiterationRemoved input selection)
            (deiterationRetainedSelection input selection witness)
            (deiterationReinsertTarget input selection)) =
          .ok (deiterationReinsertResult input selection witness) :=
        deiterationReinsertResult_spec input selection witness
      rw [hsplice] at accepted
      contradiction
    · exact ⟨_, rfl⟩

noncomputable def deiterationReinsertReceipt
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    StepReceipt (deiterationRemoved input selection) :=
  Classical.choose
    (applyIteration_deiterationReinsert_complete input selection witness)

theorem deiterationReinsertReceipt_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    applyIteration (deiterationRemoved input selection)
        (deiterationRetainedSelection input selection witness)
        (deiterationReinsertTarget input selection) =
      .ok (deiterationReinsertReceipt input selection witness) :=
  Classical.choose_spec
    (applyIteration_deiterationReinsert_complete input selection witness)

end VisualProof.Rule.IterationSoundness
