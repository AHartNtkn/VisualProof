import VisualProof.Refinement.Implementation.WireSever

namespace VisualProof.Refinement.Implementation.WireSever

open VisualProof

theorem separatedOpen_eq_canonical_of_nested
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (nested : source.checked.val.diagram.root ≠
      (source.checked.val.diagram.wires wire).scope) :
    separatedOpen source wire keep boundary targetWellFormed =
      canonicalOpen source.checked wire keep targetWellFormed := by
  apply Subtype.ext
  unfold separatedOpen canonicalOpen VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
  dsimp only
  congr 1
  apply List.ext_get
  · simpa [separatedOpen, canonicalOpen, VisualProof.Refinement.Implementation.WireSever.severWireRawOpen] using
      source.boundary_length.symm
  · intro index separatedBound canonicalBound
    let position : Fin arity := ⟨index, by
      simpa [separatedOpen] using separatedBound⟩
    have sourceRoot := source.checked.property.boundary_is_root_scoped
      (source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position))
      (List.get_mem _ _)
    have distinct : source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm position) ≠ wire := by
      intro equality
      have scope := congrArg
        (fun candidate => (source.checked.val.diagram.wires candidate).scope)
        equality
      exact nested (sourceRoot.symm.trans scope)
    simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
    unfold Concrete.severBoundaryImage
    rw [if_neg]
    · rfl
    · intro selected
      apply distinct
      simpa [position, List.get_eq_getElem] using selected.1

end VisualProof.Refinement.Implementation.WireSever
