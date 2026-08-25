import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- A nonempty item sequence is derivable by recursively deriving its head
and tail and joining their support binders with ParallelShape. -/
theorem supportParallelDerives
    {wires : List Sig} (materialHead : Item wires)
    (materialTail : ItemSeq wires)
    (materialHeadIH : SupportDerives (Region.singleton materialHead))
    (materialTailIH : SupportDerives (Region.ofItems materialTail)) :
    SupportDerives (Region.ofItems (.cons materialHead materialTail)) := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
