import VisualProof.Rule.Completeness.Comprehension.Lambda.TermComplete
import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Normalization.Sites

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory

namespace Structural

/-- Compile support-completed singleton Lambda-term material at any inherited
wire context. -/
theorem supportTermDerives
    {wires : List Sig} (output : Var wires .iota) (freeArity : Nat)
    (ports : Fin freeArity → Var wires .iota)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    VisualProof.Rule.Completeness.Comprehension.Structural.SupportDerives
      (Region.singleton (.term output freeArity ports term)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence structuralRequest
  have patternEq :
      Erasure.Exposure.supportPattern
          (Region.singleton (.term output freeArity ports term))
          materialCanonical =
        Erasure.Exposure.supportPattern
          (supportTermMaterial freeArity term output ports)
          (supportTermMaterial_canonical freeArity term output ports) := by
    apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
  rw [patternEq] at evidence
  obtain ⟨termSites⟩ := normalizationItemsSites_nonempty
    (frame := normalizationFrame structuralOuter structuralBefore
      structuralAfter wires) evidence
  exact supportTermFormalAt freeArity term output ports evidence termSites
    structuralRequest

end Structural

end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
