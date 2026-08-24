import VisualProof.Rule.Completeness.Comprehension.Complete

namespace VisualProof.Rule.Comprehension

open Diagram

/-- Every declarative comprehension step is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : Comprehension source target) :
    Relation.TransGen Step source target := by
  sorry

end VisualProof.Rule.Comprehension
