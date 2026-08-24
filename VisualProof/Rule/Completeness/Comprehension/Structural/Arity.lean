import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- The local-wire constructor is the remaining Arity completeness obligation. -/
theorem supportArityDerives
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems : Region []).Canonical)
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel [] :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (Region.mk (firstLocal :: locals) materialItems : Region [])
          materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter [])
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter [])
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel [] :: structuralAfter)
        items)) :
    request.Result := by
  sorry

end Structural

end VisualProof.Rule.Completeness.Comprehension
