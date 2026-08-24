import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- The boundary-wire constructor is the remaining boundary completeness obligation. -/
theorem supportBoundaryWireDerives
    {firstBoundary : Sig} {remainingBoundary : List Sig}
    (material : Region (firstBoundary :: remainingBoundary))
    (materialCanonical : material.Canonical)
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++
          .rel (firstBoundary :: remainingBoundary) :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter
          (firstBoundary :: remainingBoundary))
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter
          (firstBoundary :: remainingBoundary))
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++
        .rel (firstBoundary :: remainingBoundary) :: structuralAfter) items)) :
    request.Result := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
