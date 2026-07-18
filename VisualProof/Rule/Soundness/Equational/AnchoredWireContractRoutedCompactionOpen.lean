import VisualProof.Rule.Soundness.Equational.RoutedClosedAnchorOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- If the removed identity is hidden from the ordered boundary, restoring its
closed equation anywhere below the wire scope along a zero-cut route gives the
exact pre-compaction batch, up to the certified carrier isomorphism. -/
theorem anchoredContract_routed_hidden_denote_iff
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
    (regionNeScope : redundantRegion ≠ (input.val.wires drop).scope)
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
    (scopeEnclosesRegion :
      (anchoredWireContractRaw input redundant drop keep).Encloses
        (input.val.wires drop).scope redundantRegion)
    {nodePath : List Nat}
    (nodeRoute : Diagram.Splice.RegionRoute
      (anchoredWireContractRaw input redundant drop keep)
      (input.val.wires drop).scope redundantRegion nodePath)
    {nodeDepth : Nat} (nodeRouteDepth : nodeRoute.HasCutDepth nodeDepth)
    (nodeDepthZero : nodeDepth = 0)
    {rootPath : List Nat}
    (rootRoute : Diagram.Splice.RegionRoute
      (anchoredWireContractRaw input redundant drop keep)
      (anchoredWireContractRaw input redundant drop keep).root
      (input.val.wires drop).scope rootPath)
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
            survivor drop keep).transportBoundary_length transport).symm)) := by
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
        (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
        (fun _ => .output)).WellFormed signature := by
    simpa [anchoredContractExpandedRaw] using expandedWellFormed
  have introduced :=
    RoutedClosedAnchorSoundness.routedClosedAnchorOpen_equiv compactedChecked
      redundantRegion (input.val.wires drop).scope redundantTerm
      spawnedWellFormed scopeEnclosesRegion regionNeScope nodeRoute
      nodeRouteDepth nodeDepthZero rootRoute model named args
  let iso := anchoredContractExpandedBatchOpenIso input redundant survivor
    redundantRegion redundantTerm drop keep shape redundantOccurs distinct
    boundary boundaryRoot dropAbsent mapped transport
  let canonicalExpanded := spawnNodeRawOpen compactedChecked.val
    (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
    (fun _ => .output)
  let canonicalIso : OpenConcreteIso canonicalExpanded
      (anchoredContractBatchOpen input redundant drop keep boundary) := by
    simpa [canonicalExpanded, compactedChecked, compacted,
      anchoredContractExpandedOpen, anchoredContractCompactedOpen] using iso
  let canonicalWf : canonicalExpanded.WellFormed signature :=
    spawnNodeRawOpen_wellFormed compactedChecked
      (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
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
  simpa [compactedChecked, compacted, compactedWf, canonicalExpanded,
    canonicalIso, canonicalWf, batchWf, Function.comp_def] using relabeled

end AnchoredWireContractSoundness

end VisualProof.Rule
