import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- The cut constructor is derivable from the recursively derived body. -/
theorem supportCutDerives
    {wires : List Sig} (body : Region wires)
    (bodyIH : SupportDerives body) :
    SupportDerives (Region.singleton (.cut body)) := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
