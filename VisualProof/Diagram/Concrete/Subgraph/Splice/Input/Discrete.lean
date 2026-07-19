import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.RootCompiler

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- An alias-free ordered pattern boundary generates only reflexive attachment
equations, regardless of whether the attachment function itself is injective. -/
theorem attachmentPartition_related_iff_of_boundary_nodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (left right : Fin input.frame.val.wireCount) :
    input.attachmentPartition.related left right = true ↔ left = right := by
  constructor
  · intro related
    apply FinitePartition.least (relation := fun first second => first = second)
      (fun _ => rfl) Eq.symm Eq.trans (closed := related)
    intro edge member
    obtain ⟨leftPosition, rightPosition, boundaryEq, rfl⟩ :=
      (input.mem_attachmentEdges_iff edge).1 member
    have positionsEq : leftPosition = rightPosition := by
      apply Fin.ext
      exact (List.getElem_inj boundaryNodup).mp (by
        simpa only [List.get_eq_getElem] using boundaryEq)
    subst rightPosition
    rfl
  · rintro rfl
    exact FinitePartition.related_refl _ _

theorem attachmentPartition_representative_of_boundary_nodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (wire : Fin input.frame.val.wireCount) :
    input.attachmentPartition.representative wire = wire := by
  have normalized := input.attachmentPartition_normalized wire
  exact ((attachmentPartition_related_iff_of_boundary_nodup input boundaryNodup
    wire (input.attachmentPartition.representative wire)).1
      ((FinitePartition.related_eq_true_iff _ _ _).2 normalized.symm)).symm

/-- Canonical cancellation of the finite carrier introduced by a discrete
attachment quotient. -/
def discreteQuotientWireEquiv (input : Input signature)
    (boundaryNodup : input.pattern.val.boundary.Nodup) :
    FiniteEquiv input.wireQuotient.Carrier
      (Fin input.frame.val.wireCount) where
  toFun := input.wireQuotient.origin
  invFun := input.quotientWire
  left_inv := input.quotientWire_wireQuotient_origin
  right_inv := by
    intro wire
    change input.attachmentPartition.quotientDomain.origin
        (input.attachmentPartition.classIndex
          input.attachmentPartition_normalized wire) = wire
    rw [FinitePartition.quotientOrigin_classIndex,
      attachmentPartition_representative_of_boundary_nodup input
        boundaryNodup]

@[simp] theorem discreteQuotientWireEquiv_quotientWire
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (wire : Fin input.frame.val.wireCount) :
    discreteQuotientWireEquiv input boundaryNodup (input.quotientWire wire) =
      wire := by
  change input.attachmentPartition.quotientDomain.origin
      (input.attachmentPartition.classIndex
        input.attachmentPartition_normalized wire) = wire
  rw [FinitePartition.quotientOrigin_classIndex,
    attachmentPartition_representative_of_boundary_nodup input boundaryNodup]

private theorem discreteClassWire_eq
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (quotient : input.wireQuotient.Carrier)
    (wire : Fin input.frame.val.wireCount)
    (member : wire ∈ input.classWires quotient) :
    wire = discreteQuotientWireEquiv input boundaryNodup quotient := by
  apply (attachmentPartition_related_iff_of_boundary_nodup input boundaryNodup
    _ _).1
  rw [← input.quotientWire_eq_iff]
  exact ((input.mem_classWires quotient wire).1 member).trans
    (input.quotientWire_wireQuotient_origin quotient).symm

private theorem discreteClassWires_eq_singleton
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (quotient : input.wireQuotient.Carrier) :
    input.classWires quotient =
      [discreteQuotientWireEquiv input boundaryNodup quotient] := by
  let retained := discreteQuotientWireEquiv input boundaryNodup quotient
  have retainedMember : retained ∈ input.classWires quotient :=
    (input.mem_classWires quotient retained).2 (by
      exact input.quotientWire_wireQuotient_origin quotient)
  cases classEq : input.classWires quotient with
  | nil => simp [classEq] at retainedMember
  | cons head tail =>
      have headEq : head = retained :=
        discreteClassWire_eq input boundaryNodup quotient head (by
          rw [classEq]
          exact List.mem_cons_self)
      subst head
      cases tailEq : tail with
      | nil => simp [classEq, tailEq, retained]
      | cons second rest =>
          have secondEq : second = retained :=
            discreteClassWire_eq input boundaryNodup quotient second (by
              rw [classEq, tailEq]
              exact List.mem_cons_of_mem retained List.mem_cons_self)
          subst second
          have nodup := input.classWires_nodup quotient
          rw [classEq, tailEq] at nodup
          simp at nodup

theorem coalescedScope_eq_of_boundary_nodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (quotient : input.wireQuotient.Carrier) :
    input.coalescedScope quotient =
      (input.frame.val.wires
        (discreteQuotientWireEquiv input boundaryNodup quotient)).scope := by
  have firstEq : input.firstClassWire quotient =
      discreteQuotientWireEquiv input boundaryNodup quotient :=
    discreteClassWire_eq input boundaryNodup quotient _ (List.get_mem _ _)
  unfold coalescedScope
  dsimp only
  rw [firstEq]
  split
  · rw [discreteClassWires_eq_singleton input boundaryNodup quotient]
    simp [outermostFrom, chooseOuter, ConcreteDiagram.Encloses.refl]
  · rfl

theorem coalescedEndpoints_eq_of_boundary_nodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (quotient : input.wireQuotient.Carrier) :
    input.coalescedEndpoints quotient =
      (input.frame.val.wires
        (discreteQuotientWireEquiv input boundaryNodup quotient)).endpoints := by
  rw [coalescedEndpoints,
    discreteClassWires_eq_singleton input boundaryNodup quotient]
  simp

private theorem fin_count_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

/-- With an alias-free pattern boundary, the executor's coalesced frame is
canonically isomorphic to the unchanged frame. -/
noncomputable def coalescedFrameIsoOfBoundaryNodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup) :
    ConcreteIso input.coalesceFrameRaw input.frame.val where
  regionCount_eq := rfl
  nodeCount_eq := rfl
  wireCount_eq := fin_count_eq_of_equiv
    (discreteQuotientWireEquiv input boundaryNodup)
  regions := .refl _
  nodes := .refl _
  wires := discreteQuotientWireEquiv input boundaryNodup
  root_eq := rfl
  regions_eq := by
    intro region
    change (input.frame.val.regions region).rename (.refl _) =
      input.frame.val.regions region
    simp
  nodes_eq := by
    intro node
    change (input.frame.val.nodes node).rename (.refl _) =
      input.frame.val.nodes node
    simp
  wire_scope_eq := by
    intro quotient
    simpa only [FiniteEquiv.refl_apply, coalesceFrameRaw_wire] using
      coalescedScope_eq_of_boundary_nodup input boundaryNodup quotient
  wire_endpoints_perm := by
    intro quotient
    rw [coalesceFrameRaw_wire,
      coalescedEndpoints_eq_of_boundary_nodup input boundaryNodup quotient]
    change (((input.frame.val.wires
      (discreteQuotientWireEquiv input boundaryNodup quotient)).endpoints.map
        (CEndpoint.rename (.refl _))).Perm
      ((input.frame.val.wires
        (discreteQuotientWireEquiv input boundaryNodup quotient)).endpoints))
    exact (ConcreteIso.refl input.frame.val).wire_endpoints_perm
      (discreteQuotientWireEquiv input boundaryNodup quotient)

theorem discreteCoalescedBoundary_map
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (boundary : List (Fin input.frame.val.wireCount)) :
    (boundary.map input.quotientWire).map
        (discreteQuotientWireEquiv input boundaryNodup) = boundary := by
  induction boundary with
  | nil => rfl
  | cons wire tail ih =>
      simp only [List.map_cons]
      rw [discreteQuotientWireEquiv_quotientWire, ih]

/-- Ordered-open form of the discrete-frame cancellation. Repeated caller
boundary positions are preserved as list positions. -/
noncomputable def coalescedFrameOpenIsoOfBoundaryNodup
    (input : Input signature) (boundaryNodup : input.pattern.val.boundary.Nodup)
    (boundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteIso (PlugLayout.coalescedOpenRoot input boundary)
      { diagram := input.frame.val, boundary := boundary } where
  diagram := coalescedFrameIsoOfBoundaryNodup input boundaryNodup
  boundary := discreteCoalescedBoundary_map input boundaryNodup boundary

end VisualProof.Diagram.Splice.Input
