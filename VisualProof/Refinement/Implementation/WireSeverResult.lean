import VisualProof.Refinement.Implementation.WireSeverCanonical

namespace VisualProof.Refinement.Implementation.WireSever

open VisualProof

private def concreteIsoOfEq
    {source target : Concrete.Diagram}
    (equality : source = target) : Concrete.Iso source target := by
  subst target
  exact Concrete.Iso.refl source

private theorem concreteIsoOfEq_wires_val
    {source target : Concrete.Diagram}
    (equality : source = target)
    (wire : Fin source.wireCount) :
    ((concreteIsoOfEq equality).wires wire).val = wire.val := by
  subst target
  rfl

def separatedOpen_resultOpen_iso
    {orientation : Concrete.Orientation}
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (result : Concrete.OperationReceipt source.diagram)
    (success : Concrete.applyWireSever orientation source.diagram wire keep =
      .ok result) :
    let targetWellFormed :
        (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed :=
      (Concrete.applyWireSever_preserves_raw success).symm ▸ result.result.property
    Concrete.OpenIso
      (separatedOpen source wire keep boundary targetWellFormed).val
      (Concrete.wireSeverResultOpen orientation source wire keep boundary
        result success).val := by
  dsimp only
  let rawEq : result.result.val =
      Concrete.severWireRaw source.checked.val.diagram wire keep :=
    Concrete.applyWireSever_preserves_raw success
  let diagramIso := concreteIsoOfEq rawEq.symm
  refine {
    diagram := diagramIso
    boundary := ?_
  }
  apply List.ext_get
  · simp [separatedOpen, Concrete.wireSeverResultOpen]
  · intro index sourceBound targetBound
    let position : Fin arity := ⟨index, by
      simpa [separatedOpen] using sourceBound⟩
    simp only [separatedOpen, Concrete.wireSeverResultOpen,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
    apply Fin.ext
    rw [concreteIsoOfEq_wires_val]
    rfl

end VisualProof.Refinement.Implementation.WireSever
