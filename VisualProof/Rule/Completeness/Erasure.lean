import VisualProof.Rule.Erasure
import VisualProof.Rule.Step

namespace VisualProof.Rule.Erasure

open Diagram

/-- Every declarative erasure step is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : _root_.VisualProof.Rule.Erasure source target) :
    Relation.TransGen Step source target := by
  sorry

end VisualProof.Rule.Erasure
