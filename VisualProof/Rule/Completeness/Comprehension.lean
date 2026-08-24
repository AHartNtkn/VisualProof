import VisualProof.Rule.Comprehension.Relation
import VisualProof.Rule.Step

namespace VisualProof.Rule.Comprehension

open Diagram

/-- Every declarative comprehension step is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : _root_.VisualProof.Rule.Comprehension source target) :
    Relation.TransGen Step source target := by
  sorry

end VisualProof.Rule.Comprehension
