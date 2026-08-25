import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- The exact production claim used as the structural recursion motive. -/
def SupportDerives {materialWires : List Sig}
    (material : Region materialWires) : Prop :=
  ∀ (materialCanonical : material.Canonical)
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel materialWires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter materialWires)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter materialWires)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
        items)),
    request.Result

theorem polaritySource_property
    (polarity : Polarity) (property : α → Prop) (before after : α)
    (beforeProperty : property before) (afterProperty : property after) :
    property (polaritySource polarity before after) := by
  cases polarity
  · exact beforeProperty
  · exact afterProperty

end Structural

end VisualProof.Rule.Completeness.Comprehension
