import VisualProof.Rule.Soundness.Iteration.ExtractionOccurrence

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- The extracted iteration pattern has no repeated boundary wire identities. -/
theorem iterationPattern_boundary_get_injective
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Function.Injective
      (iterationInput input selection target).pattern.val.boundary.get := by
  let layout : FragmentLayout input.val selection := {}
  simpa [iterationInput, layout] using
    input.val.extractBoundaryRaw_get_injective selection layout

/-- Iteration attaches distinct extracted boundary positions to the
corresponding distinct touching host wires. -/
theorem iterationAttachment_injective
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Function.Injective (iterationInput input selection target).attachment := by
  intro left right equality
  let layout : FragmentLayout input.val selection := {}
  have origins :
      selection.touchingWires.get
          (Fin.cast
            (input.val.extractBoundaryRaw_length selection layout) left) =
        selection.touchingWires.get
          (Fin.cast
            (input.val.extractBoundaryRaw_length selection layout) right) := by
    simpa [iterationInput, layout] using equality
  have castEq :=
    (List.getElem_inj selection.touchingWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using origins)
  apply Fin.ext
  simpa using castEq

/-- Extraction-generated iteration inputs have a discrete attachment
partition: the splice compiler never coalesces two retained frame wires. -/
theorem iterationAttachmentPartition_related_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (left right : Fin input.val.wireCount) :
    (iterationInput input selection target).attachmentPartition.related
        left right = true ↔ left = right := by
  constructor
  · intro related
    apply FinitePartition.least (relation := fun first second => first = second)
      (fun _ => rfl) Eq.symm Eq.trans (closed := related)
    intro edge member
    obtain ⟨leftPosition, rightPosition, boundaryEq, edgeEq⟩ :=
      ((iterationInput input selection target).mem_attachmentEdges_iff edge).1
        member
    have positions := iterationPattern_boundary_get_injective input selection
      target boundaryEq
    subst rightPosition
    rw [edgeEq]
  · rintro rfl
    exact FinitePartition.related_refl _ _

theorem iterationAttachmentPartition_representative
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (wire : Fin input.val.wireCount) :
    (iterationInput input selection target).attachmentPartition.representative
        wire = wire := by
  let spliceInput := iterationInput input selection target
  have normalized := spliceInput.attachmentPartition_normalized wire
  exact ((iterationAttachmentPartition_related_iff input selection target wire
    (spliceInput.attachmentPartition.representative wire)).1
      ((FinitePartition.related_eq_true_iff _ _ _).2 normalized.symm)).symm

/-- Canonical identification of the iteration quotient carrier with the
unchanged frame-wire carrier. -/
def iterationQuotientWireEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    FiniteEquiv
      (iterationInput input selection target).wireQuotient.Carrier
      (Fin input.val.wireCount) where
  toFun := (iterationInput input selection target).wireQuotient.origin
  invFun := fun wire =>
    (iterationInput input selection target).wireQuotient.index wire (by
      change ((iterationInput input selection target).attachmentPartition
        |>.quotientDomain).survives wire = true
      exact (FinitePartition.quotientDomain_survives_iff _ _).2
        (iterationAttachmentPartition_representative input selection target
          wire))
  left_inv := (iterationInput input selection target).wireQuotient.index_origin
  right_inv := by
    intro wire
    exact (iterationInput input selection target).wireQuotient.origin_index
      wire _

private theorem iterationQuotientWire_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (quotient : (iterationInput input selection target).wireQuotient.Carrier) :
    (iterationInput input selection target).quotientWire
        (iterationQuotientWireEquiv input selection target quotient) =
      quotient := by
  have classEq : ((iterationInput input selection target).attachmentPartition
      |>.classIndex
        (iterationInput input selection target).attachmentPartition_normalized
        ((iterationInput input selection target).wireQuotient.origin quotient)) =
      quotient := by
    apply (iterationInput input selection target).wireQuotient.origin_injective
    change (iterationInput input selection target).attachmentPartition.quotientDomain.origin
      ((iterationInput input selection target).attachmentPartition.classIndex
        (iterationInput input selection target).attachmentPartition_normalized
        ((iterationInput input selection target).attachmentPartition.quotientDomain.origin
          quotient)) =
      (iterationInput input selection target).attachmentPartition.quotientDomain.origin
        quotient
    rw [FinitePartition.quotientOrigin_classIndex]
    have survives :=
      (iterationInput input selection target).wireQuotient.origin_survives quotient
    exact (FinitePartition.quotientDomain_survives_iff
      (iterationInput input selection target).attachmentPartition _).1 survives
  simpa only [Splice.Input.quotientWire, iterationQuotientWireEquiv] using classEq

private theorem iterationClassWire_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (quotient : (iterationInput input selection target).wireQuotient.Carrier)
    (wire : Fin input.val.wireCount)
    (member : wire ∈
      (iterationInput input selection target).classWires quotient) :
    wire = iterationQuotientWireEquiv input selection target quotient := by
  apply (iterationAttachmentPartition_related_iff input selection target _ _).1
  rw [← (iterationInput input selection target).quotientWire_eq_iff]
  exact ((iterationInput input selection target).mem_classWires quotient wire).1
      member |>.trans
        (iterationQuotientWire_eq input selection target quotient).symm

private theorem iterationClassWires_eq_singleton
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (quotient : (iterationInput input selection target).wireQuotient.Carrier) :
    (iterationInput input selection target).classWires quotient =
      [iterationQuotientWireEquiv input selection target quotient] := by
  let retained := iterationQuotientWireEquiv input selection target quotient
  have present : retained ∈
      (iterationInput input selection target).classWires quotient :=
    ((iterationInput input selection target).mem_classWires quotient retained).2
      (iterationQuotientWire_eq input selection target quotient)
  cases classEq : (iterationInput input selection target).classWires quotient with
  | nil =>
      have impossible : retained ∈ ([] : List (Fin input.val.wireCount)) :=
        classEq ▸ present
      exact False.elim (List.not_mem_nil impossible)
  | cons head tail =>
      have headEq : head = retained := iterationClassWire_eq input selection
        target quotient head (by rw [classEq]; exact List.mem_cons_self)
      subst head
      cases tailEq : tail with
      | nil => rfl
      | cons second rest =>
          have secondEq : second = retained := iterationClassWire_eq input
            selection target quotient second (by
              rw [classEq, tailEq]
              exact List.mem_cons_of_mem retained List.mem_cons_self)
          subst second
          have nodup :=
            (iterationInput input selection target).classWires_nodup quotient
          rw [classEq, tailEq] at nodup
          simp at nodup

private theorem iterationCoalescedScope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (quotient : (iterationInput input selection target).wireQuotient.Carrier) :
    (iterationInput input selection target).coalescedScope quotient =
      (input.val.wires
        (iterationQuotientWireEquiv input selection target quotient)).scope := by
  have firstEq :
      (iterationInput input selection target).firstClassWire quotient =
        iterationQuotientWireEquiv input selection target quotient :=
    iterationClassWire_eq input selection target quotient _ (List.get_mem _ _)
  unfold Splice.Input.coalescedScope
  dsimp only
  rw [firstEq]
  split
  · rw [iterationClassWires_eq_singleton input selection target quotient]
    simp [iterationInput, Splice.Input.outermostFrom,
      Splice.Input.chooseOuter, ConcreteDiagram.Encloses.refl]
  · rfl

private theorem iterationCoalescedEndpoints_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (quotient : (iterationInput input selection target).wireQuotient.Carrier) :
    (iterationInput input selection target).coalescedEndpoints quotient =
      (input.val.wires
        (iterationQuotientWireEquiv input selection target quotient)).endpoints := by
  rw [Splice.Input.coalescedEndpoints,
    iterationClassWires_eq_singleton input selection target quotient]
  simp [iterationInput]

@[simp] theorem iterationQuotientWireEquiv_quotientWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (wire : Fin input.val.wireCount) :
    iterationQuotientWireEquiv input selection target
        ((iterationInput input selection target).quotientWire wire) = wire := by
  change (iterationInput input selection target).attachmentPartition.quotientDomain.origin
      ((iterationInput input selection target).attachmentPartition.classIndex
        (iterationInput input selection target).attachmentPartition_normalized
        wire) = wire
  rw [FinitePartition.quotientOrigin_classIndex,
    iterationAttachmentPartition_representative]

private theorem fin_count_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

/-- Because extraction gives a discrete attachment quotient, the canonical
coalesced frame used by the splice compiler is isomorphic to the original
input diagram, with regions and nodes fixed pointwise. -/
noncomputable def iterationCoalescedFrameIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    ConcreteIso (iterationInput input selection target).coalesceFrameRaw
      input.val where
  regionCount_eq := rfl
  nodeCount_eq := rfl
  wireCount_eq := fin_count_eq_of_equiv
    (iterationQuotientWireEquiv input selection target)
  regions := .refl _
  nodes := .refl _
  wires := iterationQuotientWireEquiv input selection target
  root_eq := rfl
  regions_eq := by
    intro region
    change (input.val.regions region).rename (.refl _) = input.val.regions region
    simp
  nodes_eq := by
    intro node
    change (input.val.nodes node).rename (.refl _) = input.val.nodes node
    simp
  wire_scope_eq := by
    intro quotient
    simpa only [FiniteEquiv.refl_apply,
      Splice.Input.coalesceFrameRaw_wire] using
      iterationCoalescedScope_eq input selection target quotient
  wire_endpoints_perm := by
    intro quotient
    rw [Splice.Input.coalesceFrameRaw_wire,
      iterationCoalescedEndpoints_eq input selection target quotient]
    change ((input.val.wires
      (iterationQuotientWireEquiv input selection target quotient)).endpoints.map
        (CEndpoint.rename (.refl _))).Perm
      (input.val.wires
        (iterationQuotientWireEquiv input selection target quotient)).endpoints
    exact (ConcreteIso.refl input.val).wire_endpoints_perm
      (iterationQuotientWireEquiv input selection target quotient)

/-- The canonical coalesced open frame for iteration is the original open
frame, including the caller's ordered and potentially repeated boundary. -/
noncomputable def iterationCoalescedOpenIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (boundary : List (Fin input.val.wireCount)) :
    OpenConcreteIso
      (Splice.Input.PlugLayout.coalescedOpenRoot
        (iterationInput input selection target) boundary)
      { diagram := input.val, boundary := boundary } where
  diagram := iterationCoalescedFrameIso input selection target
  boundary := by
    simp only [Splice.Input.PlugLayout.coalescedOpenRoot, List.map_map]
    change boundary.map
        (iterationQuotientWireEquiv input selection target ∘
          (iterationInput input selection target).quotientWire) = boundary
    induction boundary with
    | nil => rfl
    | cons wire tail induction =>
        change iterationQuotientWireEquiv input selection target
              ((iterationInput input selection target).quotientWire wire) ::
            tail.map
              (iterationQuotientWireEquiv input selection target ∘
                (iterationInput input selection target).quotientWire) =
          wire :: tail
        rw [iterationQuotientWireEquiv_quotientWire, induction]

end VisualProof.Rule.IterationSoundness
