import VisualProof.Refinement.Implementation.WireJoinRootOpen

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Diagram
open VisualProof.Rule
open VisualProof.Data.Finite

noncomputable def swapWireMap
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Fin (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wireCount →
      Fin (VisualProof.Refinement.Implementation.WireJoin.Target input inner outer).wireCount :=
  fun target =>
    VisualProof.Refinement.Implementation.WireJoin.wireMap input inner outer distinct.symm
      (Classical.choose
        (VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct target))

theorem swapWireMap_wireMap
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    swapWireMap input outer inner distinct
        (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire) =
      VisualProof.Refinement.Implementation.WireJoin.wireMap input inner outer distinct.symm wire := by
  unfold swapWireMap
  let preimage := Classical.choose
    (VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct
      (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire))
  have preimage_spec : VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct
      preimage = VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire :=
    Classical.choose_spec
      (VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct
        (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire))
  have cases := (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff input outer inner
    preimage wire distinct).1 preimage_spec
  apply (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff input inner outer
    preimage wire distinct.symm).2
  rcases cases with same | outerInner | innerOuter
  · exact Or.inl same
  · exact Or.inr (Or.inr outerInner)
  · exact Or.inr (Or.inl innerOuter)

theorem swapWireMap_injective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Function.Injective (swapWireMap input outer inner distinct) := by
  intro left right equality
  obtain ⟨leftSource, leftEq⟩ :=
    VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct left
  obtain ⟨rightSource, rightEq⟩ :=
    VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct right
  rw [← leftEq, swapWireMap_wireMap, ← rightEq,
    swapWireMap_wireMap] at equality
  have cases := (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff input inner outer
    leftSource rightSource distinct.symm).1 equality
  apply leftEq.symm.trans
  apply Eq.trans _ rightEq
  apply (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff input outer inner
    leftSource rightSource distinct).2
  rcases cases with same | innerOuter | outerInner
  · exact Or.inl same
  · exact Or.inr (Or.inr innerOuter)
  · exact Or.inr (Or.inl outerInner)

theorem swapWireMap_surjective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Function.Surjective (swapWireMap input outer inner distinct) := by
  intro target
  obtain ⟨source, sourceEq⟩ :=
    VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input inner outer distinct.symm target
  refine ⟨VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct source, ?_⟩
  rw [swapWireMap_wireMap, sourceEq]

noncomputable def swapWireEquiv
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wireCount)
      (Fin (VisualProof.Refinement.Implementation.WireJoin.Target input inner outer).wireCount) where
  toFun := swapWireMap input outer inner distinct
  invFun := fun target => Classical.choose
    (swapWireMap_surjective input outer inner distinct target)
  left_inv := by
    intro source
    apply swapWireMap_injective input outer inner distinct
    exact Classical.choose_spec
      (swapWireMap_surjective input outer inner distinct
        (swapWireMap input outer inner distinct source))
  right_inv := by
    intro target
    exact Classical.choose_spec
      (swapWireMap_surjective input outer inner distinct target)

theorem target_wire_endpoints
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wires
      (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire)).endpoints =
      if wire = inner then
        (input.wires outer).endpoints ++ (input.wires inner).endpoints
      else if wire = outer then
        (input.wires outer).endpoints ++ (input.wires inner).endpoints
      else
        (input.wires wire).endpoints := by
  change
    (if (Concrete.joinWireDomain input inner).origin
          (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire) = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires ((Concrete.joinWireDomain input inner).origin
          (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire))).endpoints = _
  rw [VisualProof.Refinement.Implementation.WireJoin.origin_wireMap]
  by_cases isInner : wire = inner
  · subst wire
    simp
  · by_cases isOuter : wire = outer
    · subst wire
      simp [distinct]
    · simp [isInner, isOuter]

noncomputable def joinWireSwapIso
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (sameScope : (input.wires outer).scope = (input.wires inner).scope) :
    Concrete.Iso
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (VisualProof.Refinement.Implementation.WireJoin.Target input inner outer) := by
  classical
  refine {
    regionCount_eq := rfl
    nodeCount_eq := rfl
    wireCount_eq := by
      apply Nat.le_antisymm
      · exact fin_card_le_of_injective
          (swapWireEquiv input outer inner distinct)
          (swapWireEquiv input outer inner distinct).injective
      · exact fin_card_le_of_injective
          (swapWireEquiv input outer inner distinct).symm
          (swapWireEquiv input outer inner distinct).symm.injective
    regions := FiniteEquiv.refl _
    nodes := FiniteEquiv.refl _
    wires := swapWireEquiv input outer inner distinct
    root_eq := rfl
    regions_eq := by
      intro region
      exact Concrete.CRegion.rename_refl (input.regions region)
    nodes_eq := by
      intro node
      exact Concrete.CNode.rename_refl (input.nodes node)
    wire_scope_eq := ?_
    wire_endpoints_perm := ?_
  }
  · intro targetWire
    obtain ⟨sourceWire, sourceEq⟩ :=
      VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct
        targetWire
    subst targetWire
    change
      ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wires
        (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct sourceWire)
      ).scope =
      ((VisualProof.Refinement.Implementation.WireJoin.Target input inner outer).wires
        (swapWireMap input outer inner distinct
          (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct sourceWire))
      ).scope
    rw [swapWireMap_wireMap]
    rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope,
      VisualProof.Refinement.Implementation.WireJoin.target_wire_scope]
    by_cases isOuter : sourceWire = outer
    · subst sourceWire
      simp [distinct, sameScope]
    · by_cases isInner : sourceWire = inner
      · subst sourceWire
        simp [sameScope]
      · simp [isOuter, isInner]
  · intro targetWire
    obtain ⟨sourceWire, sourceEq⟩ :=
      VisualProof.Refinement.Implementation.WireJoin.wireMap_surjective input outer inner distinct
        targetWire
    subst targetWire
    change
      (((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wires
        (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct sourceWire)
      ).endpoints.map
        (Concrete.CEndpoint.rename (FiniteEquiv.refl _))).Perm
      ((VisualProof.Refinement.Implementation.WireJoin.Target input inner outer).wires
        (swapWireMap input outer inner distinct
          (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct sourceWire))
      ).endpoints
    rw [swapWireMap_wireMap]
    rw [target_wire_endpoints, target_wire_endpoints]
    have renameRefl :
        Concrete.CEndpoint.rename (FiniteEquiv.refl
          (Fin (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).nodeCount)) =
          id := by
      funext endpoint
      exact Concrete.CEndpoint.rename_refl endpoint
    rw [renameRefl, List.map_id]
    by_cases isOuter : sourceWire = outer
    · subst sourceWire
      simpa [distinct] using
        (List.perm_append_comm :
          ((input.wires outer).endpoints ++
            (input.wires inner).endpoints).Perm
          ((input.wires inner).endpoints ++
            (input.wires outer).endpoints))
    · by_cases isInner : sourceWire = inner
      · subst sourceWire
        simpa using
          (List.perm_append_comm :
            ((input.wires outer).endpoints ++
              (input.wires inner).endpoints).Perm
            ((input.wires inner).endpoints ++
              (input.wires outer).endpoints))
      · simp [isOuter, isInner]

noncomputable def joinWireSwapOpenIso
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (sameScope : (source.diagram.wires outer).scope =
      (source.diagram.wires inner).scope) :
    Concrete.OpenIso
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct)
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source inner outer distinct.symm) := by
  classical
  let diagramIso := joinWireSwapIso source.diagram outer inner distinct
    sameScope
  refine {
    diagram := diagramIso
    boundary := ?_
  }
  unfold VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw
  change (source.boundary.map
    (VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner distinct)).map
      (swapWireEquiv source.diagram outer inner distinct) =
    source.boundary.map
      (VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram inner outer distinct.symm)
  rw [List.map_map]
  apply List.map_congr_left
  intro wire _member
  exact swapWireMap_wireMap source.diagram outer inner wire distinct

end VisualProof.Refinement.Implementation.WireJoin
