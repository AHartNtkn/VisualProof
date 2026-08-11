import VisualProof.Refinement.Step.Core
import VisualProof.Refinement.Step.Erasure
import VisualProof.Refinement.Step.WireSever
import VisualProof.Refinement.Step.DoubleCut
import VisualProof.Refinement.Step.Iteration

namespace VisualProof.Refinement

open VisualProof.Diagram

/-- Canonical refinement for every concrete request. -/
theorem execute_refinesCanonical
    {arity : Nat}
    {orientation : Concrete.Orientation}
    {source : Concrete.State arity}
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source request = .ok receipt) :
    DirectedStep orientation
      (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

/-- Representation transport for every successful concrete request. -/
theorem execute_refines
    {arity : Nat}
    {orientation : Concrete.Orientation}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    (sourceRep : StateRepresents source sourceDiagram)
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source request = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      StateRepresents receipt.target targetDiagram ∧
      DirectedStep orientation sourceDiagram targetDiagram := by
  sorry

end VisualProof.Refinement

/-! Canonical execution refinement is dispatched here. -/
