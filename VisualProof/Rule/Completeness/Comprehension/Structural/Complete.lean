import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete
import VisualProof.Rule.Completeness.Comprehension.Structural.Blank

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- Derive the exact support-completed material pattern selected by
comprehension evidence. The material syntax and its canonicality determine
the structural recursion; the caller contributes only the authoritative
instantiation evidence and the actual telescope request. -/
theorem supportPatternDerives
    {materialWires structuralOuter structuralBefore structuralAfter :
        List Sig}
    (material : Region materialWires)
    (materialCanonical : material.Canonical)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel materialWires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter materialWires)
        (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter materialWires)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
        items)) :
    request.Result := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
