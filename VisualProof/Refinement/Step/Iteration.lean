import VisualProof.Concrete.Step
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.Iteration

theorem iteration
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.iteration selection target) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

theorem deiteration
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    (certificate : Concrete.DeiterationCertificate source.diagram selection)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.deiteration selection certificate) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

end VisualProof.Refinement.Iteration
