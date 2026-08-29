import VisualProof.Rule.Completeness.Comprehension.Structural.Atom
import VisualProof.Rule.Completeness.Comprehension.Structural.Blank
import VisualProof.Rule.Completeness.Comprehension.Structural.Cut
import VisualProof.Rule.Completeness.Comprehension.Structural.Identity
import VisualProof.Rule.Completeness.Comprehension.Lambda.Structural.Term
import VisualProof.Rule.Completeness.Comprehension.Structural.ParallelDerives
import VisualProof.Rule.Completeness.Comprehension.Structural.Region

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- Derive the exact support-completed material pattern selected by
comprehension evidence. The recursion only dispatches semantic constructors
to their owning production theorems. -/
theorem supportPatternDerives
    {materialWires structuralOuter structuralBefore structuralAfter : List Sig}
    (material : Region materialWires)
    (materialCanonical : material.Canonical)
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
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter) items)) :
    request.Result := by
  refine (Region.rec
    (motive_1 := fun _ region => SupportDerives region)
    (motive_2 := fun _ item => SupportDerives (Region.singleton item))
    (motive_3 := fun _ materialItems =>
      SupportDerives (Region.ofItems materialItems))
    supportRegionDerives supportAtomDerives supportIdentityDerives
      LambdaTerm.Structural.supportTermDerives supportCutDerives supportBlankDerives
      supportParallelDerives material) materialCanonical evidence request
end Structural

end VisualProof.Rule.Completeness.Comprehension
