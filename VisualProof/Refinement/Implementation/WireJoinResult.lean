import VisualProof.Concrete.Step
import VisualProof.Refinement.Implementation.WireJoin

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof

def targetOpen_result_iso
    {arity : Nat}
    (source : Concrete.State arity)
    (outer inner : Fin source.checked.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.checked.val.diagram.Encloses
      (source.checked.val.diagram.wires outer).scope
      (source.checked.val.diagram.wires inner).scope)
    {result : Concrete.OperationReceipt source.diagram}
    {receipt : Concrete.Receipt source}
    (realizes : result.Realizes
      (Concrete.joinWireRaw source.checked.val.diagram outer inner)
      (Concrete.joinWireProvenance source.checked.val.diagram outer inner)
      (Concrete.joinWireWireTransport source.checked.val.diagram outer inner))
    (packed : result.toReceipt source = some receipt) :
    let targetWellFormed :
        (Concrete.joinWireRaw source.checked.val.diagram outer inner).WellFormed :=
      realizes.result_eq ▸ result.result.property
    Concrete.OpenIso
      (VisualProof.Refinement.Implementation.WireJoin.targetOpen source.checked outer inner distinct
        ordered targetWellFormed).val
      receipt.target.checked.val := by
  dsimp only
  let targetWellFormed :
      (Concrete.joinWireRaw source.checked.val.diagram outer inner).WellFormed :=
    realizes.result_eq ▸ result.result.property
  unfold Concrete.OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i mapped transport
  cases packed
  have expected := realizes.transportBoundary_expected transport
  have mappedEq := VisualProof.Refinement.Implementation.WireJoin.interface_transportBoundary_eq_map
    source.checked.val.diagram outer inner distinct source.checked.val.boundary
      _ expected
  have canonicalToRaw := realizes.operationalIso_to_rawResultOpen transport
    (source.checked.val.boundary.map
      (VisualProof.Refinement.Implementation.WireJoin.wireMap source.checked.val.diagram outer inner
        distinct)) (by simpa [mappedEq] using expected)
  exact canonicalToRaw.trans (realizes.rawResultOpenIso mapped)

end VisualProof.Refinement.Implementation.WireJoin
