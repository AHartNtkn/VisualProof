import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Normalization.Sites

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- Compile the support-completed singleton-identity material at any inherited
wire context. -/
theorem supportIdentityDerives
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    SupportDerives (Region.singleton (.identity signature arity ports)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence structuralRequest
  have patternEq :
      Erasure.Exposure.supportPattern
          (Region.singleton (.identity signature arity ports))
          materialCanonical =
        Erasure.Exposure.supportPattern
          (supportIdentityMaterial signature arity ports)
          (supportIdentityMaterial_canonical signature arity ports) := by
    apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
  rw [patternEq] at evidence
  obtain ⟨identitySites⟩ := normalizationItemsSites_nonempty
    (frame := normalizationFrame structuralOuter structuralBefore
      structuralAfter wires) evidence
  exact supportIdentityFormalAt signature arity ports evidence identitySites
    structuralRequest

end Structural

end VisualProof.Rule.Completeness.Comprehension
