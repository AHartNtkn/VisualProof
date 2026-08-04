import VisualProof.Rule.Soundness.Equational.AnchoredWireContractCompaction

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

def anchoredContractCompactedOpen
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount)) :
    OpenConcreteDiagram where
  diagram := anchoredWireContractRaw input redundant drop keep
  boundary := boundary

def anchoredContractExpandedOpen
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount)) :
    OpenConcreteDiagram :=
  spawnNodeRawOpen
    (anchoredContractCompactedOpen input redundant drop keep boundary)
    (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
    (fun _ => .output)

def anchoredContractBatchOpen
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := moveEndpointsRaw input.val drop keep
    (movedEndpoints input redundant drop)
  boundary := boundary

/-- When the removed identity is not externally named, the carrier
isomorphism also preserves the complete ordered-open boundary. -/
def anchoredContractExpandedBatchOpenIso
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (distinct : drop ≠ keep)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (dropAbsent : drop ∉ boundary)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped) :
    OpenConcreteIso
      (anchoredContractExpandedOpen input redundant redundantRegion
        redundantTerm drop keep mapped)
      (anchoredContractBatchOpen input redundant drop keep boundary) where
  diagram := anchoredContractExpandedIso input redundant redundantRegion
    redundantTerm drop keep shape redundantOccurs
  boundary := by
    let image : Fin input.val.wireCount → Fin
        (anchoredWireContractRaw input redundant drop keep).wireCount :=
      fun wire =>
        if equality : wire = drop then
          (anchoredContractWireDomain input.val drop).index keep (by
            simp [anchoredContractWireDomain, distinct.symm])
        else
          (anchoredContractWireDomain input.val drop).index wire (by
            simp [anchoredContractWireDomain, equality])
    have mappedEq : mapped = boundary.map image := by
      simpa [image] using
        anchoredWireContract_transportBoundary_eq_map input redundant survivor
          drop keep distinct boundary boundaryRoot mapped transport
    unfold anchoredContractExpandedOpen anchoredContractCompactedOpen
      anchoredContractBatchOpen spawnNodeRawOpen
    rw [mappedEq]
    dsimp only
    change ((boundary.map image).map (Fin.castAdd 1)).map
      (anchoredContractExpandedIso input redundant redundantRegion
        redundantTerm drop keep shape redundantOccurs).wires = boundary
    let combined := Fin.castAdd 1 ∘ image
    let restore :=
      (anchoredContractExpandedIso input redundant redundantRegion
        redundantTerm drop keep shape redundantOccurs).wires
    have point : ∀ wire, wire ∈ boundary →
        (restore ∘ combined) wire = id wire := by
      intro wire member
      have wireNe : wire ≠ drop := by
        intro equality
        subst wire
        exact dropAbsent member
      change restore (Fin.castAdd 1 (image wire)) = wire
      rw [show image wire =
          (anchoredContractWireDomain input.val drop).index wire (by
            simp [anchoredContractWireDomain, wireNe]) by
        simp [image, wireNe]]
      change anchoredContractWireRestore input drop
        ((anchoredContractWireDomain input.val drop).index wire (by
          simp [anchoredContractWireDomain, wireNe])).castSucc = wire
      rw [anchoredContractWireRestore]
      calc
        restoreDeletedEquiv (anchoredContractWireDomain input.val drop) drop
            (by intro candidate; rfl)
            ((anchoredContractWireDomain input.val drop).index wire (by
              simp [anchoredContractWireDomain, wireNe])).castSucc =
          (anchoredContractWireDomain input.val drop).origin
            ((anchoredContractWireDomain input.val drop).index wire (by
              simp [anchoredContractWireDomain, wireNe])) :=
                restoreDeletedEquiv_survivor
                  (anchoredContractWireDomain input.val drop) drop
                  (by intro candidate; rfl) _
        _ = wire :=
          (anchoredContractWireDomain input.val drop).origin_index wire
            (by simp [anchoredContractWireDomain, wireNe])
    have mappedResult : (boundary.map combined).map restore = boundary := by
      calc
        (boundary.map combined).map restore =
          boundary.map (restore ∘ combined) := List.map_map
        _ = boundary.map id := List.map_congr_left point
        _ = boundary := List.map_id boundary
    simpa [combined, restore, Function.comp_def] using mappedResult

/-- If the redundant equation is introduced at its own wire scope and the
removed identity is not on the ordered boundary, ordinary closed-term
introduction plus the carrier isomorphism proves exact compaction semantics. -/
theorem anchoredContract_sameSite_hidden_denote_iff
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (distinct : drop ≠ keep)
    (sameSite : (input.val.wires drop).scope = redundantRegion)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (dropAbsent : drop ∉ boundary)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped)
    (mappedRoot : ∀ wire, wire ∈ mapped →
      ((anchoredWireContractRaw input redundant drop keep).wires wire).scope =
        (anchoredWireContractRaw input redundant drop keep).root)
    (compactedWellFormed :
      (anchoredWireContractRaw input redundant drop keep).WellFormed signature)
    (batchWellFormed :
      (moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin mapped.length → model.Carrier) :
    let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
    let batch := anchoredContractBatchOpen input redundant drop keep boundary
    compacted.denote
        { diagram_well_formed := compactedWellFormed
          boundary_is_root_scoped := mappedRoot }
        model named args ↔
      batch.denote
        { diagram_well_formed := batchWellFormed
          boundary_is_root_scoped := by
            intro wire member
            change wire ∈ boundary at member
            change ((moveEndpointsRaw input.val drop keep
              (movedEndpoints input redundant drop)).wires wire).scope =
                input.val.root
            rw [moveEndpointsRaw_wire_scope]
            exact boundaryRoot wire member }
        model named (args ∘ Fin.cast (by
          exact ((anchoredWireContractInterfaceTransport input redundant
            survivor drop keep).transportBoundary_length transport).symm)
        ) := by
  dsimp only
  let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
  let compactedWf : compacted.WellFormed signature := {
    diagram_well_formed := compactedWellFormed
    boundary_is_root_scoped := mappedRoot
  }
  let compactedChecked : CheckedOpenDiagram signature :=
    ⟨compacted, compactedWf⟩
  have expandedWellFormed :
      (anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
        drop keep).WellFormed signature :=
    anchoredContractExpandedRaw_wellFormed input redundant redundantRegion
      redundantTerm drop keep shape redundantOccurs batchWellFormed
  have spawnedWellFormed :
      (spawnNodeRaw
        (anchoredWireContractRaw input redundant drop keep)
        (.term redundantRegion 0 redundantTerm) redundantRegion 1
        (fun _ => .output)).WellFormed signature := by
    simpa [anchoredContractExpandedRaw, sameSite] using expandedWellFormed
  let view := Classical.choice
    (Diagram.Splice.openSiteView_complete compactedChecked redundantRegion)
  have introduced := closedTermIntroOpen_equiv compactedChecked redundantRegion
    redundantTerm spawnedWellFormed view.route view.cutDepth model named args
  let iso := anchoredContractExpandedBatchOpenIso input redundant survivor
    redundantRegion redundantTerm drop keep shape redundantOccurs distinct
    boundary boundaryRoot dropAbsent mapped transport
  let canonicalExpanded := spawnNodeRawOpen compactedChecked.val
    (.term redundantRegion 0 redundantTerm) redundantRegion 1
    (fun _ => .output)
  let canonicalIso : OpenConcreteIso canonicalExpanded
      (anchoredContractBatchOpen input redundant drop keep boundary) := by
    simpa [canonicalExpanded, compactedChecked, compacted,
      anchoredContractExpandedOpen, anchoredContractCompactedOpen,
      sameSite] using iso
  let canonicalWf : canonicalExpanded.WellFormed signature :=
    spawnNodeRawOpen_wellFormed compactedChecked
      (.term redundantRegion 0 redundantTerm) redundantRegion 1
      (fun _ => .output) spawnedWellFormed
  let batchWf :
      (anchoredContractBatchOpen input redundant drop keep boundary).WellFormed
        signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      change wire ∈ boundary at member
      change ((moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).wires wire).scope = input.val.root
      rw [moveEndpointsRaw_wire_scope]
      exact boundaryRoot wire member
  }
  have relabeled := canonicalIso.denote_iff canonicalWf batchWf model named
    (args ∘ Fin.cast (by
      simp [canonicalExpanded, compactedChecked, compacted,
        anchoredContractCompactedOpen, spawnNodeRawOpen]))
  apply introduced.trans
  simpa [compactedChecked, compacted, compactedWf,
    canonicalExpanded, canonicalIso, canonicalWf, batchWf,
    Function.comp_def] using relabeled

end AnchoredWireContractSoundness

end VisualProof.Rule
