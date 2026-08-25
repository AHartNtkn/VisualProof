import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Normalization.Sites

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- Compile the support-completed singleton-atom material at any inherited
wire context. -/
theorem supportAtomDerives
    {wires arguments : List Sig}
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    SupportDerives (Region.singleton (.atom head ports)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence structuralRequest
  have patternEq :
      Erasure.Exposure.supportPattern
          (Region.singleton (.atom head ports)) materialCanonical =
        Erasure.Exposure.supportPattern
          (supportAtomMaterial head ports)
          (supportAtomMaterial_canonical head ports) := by
    apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
  rw [patternEq] at evidence
  obtain ⟨atomSites⟩ := normalizationItemsSites_nonempty
    (frame := normalizationFrame structuralOuter structuralBefore
      structuralAfter wires) evidence
  exact supportAtomFormalAt head ports evidence atomSites structuralRequest

end Structural

end VisualProof.Rule.Completeness.Comprehension
