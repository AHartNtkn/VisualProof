import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- A region is derivable from its recursively derived item sequence at any
inherited and local wire context. -/
theorem supportRegionDerives
    {outer : List Sig} (locals : List Sig)
    (materialItems : ItemSeq (outer ++ locals))
    (materialItemsIH : SupportDerives (Region.ofItems materialItems)) :
    SupportDerives (Region.mk locals materialItems : Region outer) := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
