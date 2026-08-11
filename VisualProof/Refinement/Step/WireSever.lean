import VisualProof.Concrete.Step
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.WireSever

theorem wireSever
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.wireSever wire keep boundary) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

theorem wireJoin
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (first second : Fin source.checked.val.diagram.wireCount)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.wireJoin first second) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

end VisualProof.Refinement.WireSever
