import VisualProof.Rule.Completeness.Comprehension.Structural.Arity
import VisualProof.Rule.Completeness.Comprehension.Structural.Atom
import VisualProof.Rule.Completeness.Comprehension.Structural.Blank
import VisualProof.Rule.Completeness.Comprehension.Structural.Boundary
import VisualProof.Rule.Completeness.Comprehension.Structural.Cut
import VisualProof.Rule.Completeness.Comprehension.Structural.Identity
import VisualProof.Rule.Completeness.Comprehension.Structural.ParallelDerives

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
    (motive_2 := fun wires item =>
      wires = [] → SupportDerives (Region.singleton item))
    (motive_3 := fun wires materialItems =>
      wires = [] → SupportDerives (Region.ofItems materialItems))
    ?_ (fun head ports _ => supportAtomDerives head ports)
      supportIdentityDerives supportCutDerives supportBlankDerives
      supportParallelDerives material) materialCanonical evidence request
  · intro outer locals materialItems materialItemsIH materialCanonical
      structuralOuter structuralBefore structuralAfter items result evidence
      structuralRequest
    cases outer with
    | nil =>
        cases locals with
        | nil =>
            exact supportItemsDerives (materialItemsIH rfl) materialCanonical
              evidence structuralRequest
        | cons firstLocal locals =>
            exact supportArityDerives materialItems materialCanonical
              (supportBoundaryWireDerives
                (Region.mk locals materialItems : Region [firstLocal]))
              evidence structuralRequest
    | cons firstBoundary remainingOuter =>
        simpa only [List.cons_append] using
          supportBoundaryWireDerives
            (material := Region.mk locals materialItems) materialCanonical
            evidence structuralRequest
end Structural

end VisualProof.Rule.Completeness.Comprehension
