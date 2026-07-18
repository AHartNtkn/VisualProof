import VisualProof.Rule.Soundness.Equational.AnchoredWireContractBatchSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

theorem anchoredContractRootAvailable_eq
    (input : CheckedDiagram signature)
    (survivor : Fin input.val.nodeCount)
    (survivorRegion : Fin input.val.regionCount)
    (survivorTerm : Lambda.Term 0 (Fin 0))
    (keep : Fin input.val.wireCount)
    (shape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm) :
    anchoredContractRootAvailable input survivor keep =
      anchorAvailableAt input.val (input.val.wires keep).scope
        survivorRegion input.val.root := by
  simp [anchoredContractRootAvailable, shape]

theorem anchoredContractRootAvailable_keep_root
    (input : CheckedDiagram signature)
    (survivor : Fin input.val.nodeCount)
    (keep : Fin input.val.wireCount)
    (available : anchoredContractRootAvailable input survivor keep = true) :
    (input.val.wires keep).scope = input.val.root := by
  cases shape : input.val.nodes survivor with
  | term survivorRegion ports survivorTerm =>
      have gate : anchorAvailableAt input.val (input.val.wires keep).scope
          survivorRegion input.val.root = true := by
        simpa [anchoredContractRootAvailable, shape] using available
      let witness := Classical.choice
        (AnchoredWireSoundness.SplitAvailability.of_gate input keep
          survivorRegion input.val.root gate)
      exact ConcreteElaboration.encloses_sheet_eq input.property.root_is_sheet
        witness.wire_encloses_target
  | atom => simp [anchoredContractRootAvailable, shape] at available
  | named => simp [anchoredContractRootAvailable, shape] at available

theorem anchoredWireContractRaw_index_scope
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep wire : Fin input.val.wireCount)
    (survives : (anchoredContractWireDomain input.val drop).survives wire = true) :
    ((anchoredWireContractRaw input redundant drop keep).wires
      ((anchoredContractWireDomain input.val drop).index wire survives)).scope =
      (input.val.wires wire).scope := by
  simp only [anchoredWireContractRaw]
  rw [(anchoredContractWireDomain input.val drop).origin_index wire survives]

theorem anchoredWireContract_interface_image_of_root
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep wire : Fin input.val.wireCount)
    (wireRoot : (input.val.wires wire).scope = input.val.root) :
    (anchoredWireContractInterfaceTransport input redundant survivor drop keep
      ).image? wire =
      if anchoredContractRootAvailable input survivor keep then
        if wire = drop then
          (anchoredContractWireDomain input.val drop).index? keep
        else
          (anchoredContractWireDomain input.val drop).index? wire
      else
        (anchoredContractWireDomain input.val drop).index? wire := by
  unfold anchoredWireContractInterfaceTransport InterfaceTransport.rootFiltered
  dsimp only
  split
  · rename_i rootAvailable
    split
    · rename_i wireDrop
      subst wire
      cases hindex : (anchoredContractWireDomain input.val drop).index? keep with
      | none => rfl
      | some mapped =>
          have origin :=
            (anchoredContractWireDomain input.val drop).index?_eq_some_iff
              keep mapped |>.mp hindex
          have keepRoot : (input.val.wires keep).scope = input.val.root :=
            anchoredContractRootAvailable_keep_root input survivor keep
              rootAvailable
          have mappedRoot :
              ((anchoredWireContractRaw input redundant drop keep).wires mapped
                ).scope =
                (anchoredWireContractRaw input redundant drop keep).root := by
            change (input.val.wires
              ((anchoredContractWireDomain input.val drop).origin mapped)).scope =
                input.val.root
            rw [origin]
            exact keepRoot
          change (if
            ((anchoredWireContractRaw input redundant drop keep).wires mapped
              ).scope =
                (anchoredWireContractRaw input redundant drop keep).root then
              some mapped else none) = some mapped
          rw [if_pos mappedRoot]
    · rename_i wireNe
      cases hindex : (anchoredContractWireDomain input.val drop).index? wire with
      | none => rfl
      | some mapped =>
          have origin :=
            (anchoredContractWireDomain input.val drop).index?_eq_some_iff
              wire mapped |>.mp hindex
          have mappedRoot :
              ((anchoredWireContractRaw input redundant drop keep).wires mapped
                ).scope =
                (anchoredWireContractRaw input redundant drop keep).root := by
            change (input.val.wires
              ((anchoredContractWireDomain input.val drop).origin mapped)).scope =
                input.val.root
            rw [origin]
            exact wireRoot
          change (if
            ((anchoredWireContractRaw input redundant drop keep).wires mapped
              ).scope =
                (anchoredWireContractRaw input redundant drop keep).root then
              some mapped else none) = some mapped
          rw [if_pos mappedRoot]
  · rename_i rootUnavailable
    cases hindex : (anchoredContractWireDomain input.val drop).index? wire with
    | none => rfl
    | some mapped =>
        have origin :=
          (anchoredContractWireDomain input.val drop).index?_eq_some_iff
            wire mapped |>.mp hindex
        have mappedRoot :
            ((anchoredWireContractRaw input redundant drop keep).wires mapped
              ).scope =
              (anchoredWireContractRaw input redundant drop keep).root := by
          change (input.val.wires
            ((anchoredContractWireDomain input.val drop).origin mapped)).scope =
              input.val.root
          rw [origin]
          exact wireRoot
        change (if
          ((anchoredWireContractRaw input redundant drop keep).wires mapped
            ).scope =
              (anchoredWireContractRaw input redundant drop keep).root then
            some mapped else none) = some mapped
        rw [if_pos mappedRoot]

theorem anchoredWireContract_hidden_boundary_excludes_drop
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (unavailable : anchoredContractRootAvailable input survivor keep = false)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped) :
    drop ∉ boundary := by
  intro member
  obtain ⟨index, get⟩ := List.mem_iff_get.mp member
  have point :=
    (anchoredWireContractInterfaceTransport input redundant survivor drop keep
      ).transportBoundary_get transport index
  rw [get] at point
  rw [anchoredWireContract_interface_image_of_root input redundant survivor drop
    keep drop (boundaryRoot drop member), unavailable] at point
  have hnone : (anchoredContractWireDomain input.val drop).index? drop = none := by
    rw [(anchoredContractWireDomain input.val drop).index?_eq_none_iff]
    simp [anchoredContractWireDomain]
  rw [hnone] at point
  contradiction

theorem anchoredWireContract_transportBoundary_eq_map
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (distinct : drop ≠ keep)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped) :
    mapped = boundary.map fun wire =>
      if equality : wire = drop then
        (anchoredContractWireDomain input.val drop).index keep (by
          simp [anchoredContractWireDomain, distinct.symm])
      else
        (anchoredContractWireDomain input.val drop).index wire (by
          simp [anchoredContractWireDomain, equality]) := by
  let image : Fin input.val.wireCount → Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount := fun wire =>
    if equality : wire = drop then
      (anchoredContractWireDomain input.val drop).index keep (by
        simp [anchoredContractWireDomain, distinct.symm])
    else
      (anchoredContractWireDomain input.val drop).index wire (by
        simp [anchoredContractWireDomain, equality])
  have imagePoint : ∀ wire, wire ∈ boundary →
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).image? wire = some (image wire) := by
    intro wire member
    rw [anchoredWireContract_interface_image_of_root input redundant survivor
      drop keep wire (boundaryRoot wire member)]
    by_cases available : anchoredContractRootAvailable input survivor keep = true
    · rw [if_pos available]
      by_cases wireDrop : wire = drop
      · rw [if_pos wireDrop]
        simpa [image, wireDrop] using
          (anchoredContractWireDomain input.val drop).index?_index keep (by
            simp [anchoredContractWireDomain, distinct.symm])
      · rw [if_neg wireDrop]
        simpa [image, wireDrop] using
          (anchoredContractWireDomain input.val drop).index?_index wire (by
            simp [anchoredContractWireDomain, wireDrop])
    · have unavailable : anchoredContractRootAvailable input survivor keep = false :=
        by cases h : anchoredContractRootAvailable input survivor keep <;>
          simp_all
      rw [if_neg available]
      have wireNe : wire ≠ drop := by
        intro equality
        subst wire
        have excluded := anchoredWireContract_hidden_boundary_excludes_drop input
          redundant survivor drop keep boundary boundaryRoot unavailable mapped
          transport
        exact excluded member
      simpa [image, wireNe] using
        (anchoredContractWireDomain input.val drop).index?_index wire (by
          simp [anchoredContractWireDomain, wireNe])
  have canonical :=
    (anchoredWireContractInterfaceTransport input redundant survivor drop keep
      ).transportBoundary_eq_map image imagePoint
  exact Option.some.inj (transport.symm.trans canonical)

end AnchoredWireContractSoundness

end VisualProof.Rule
