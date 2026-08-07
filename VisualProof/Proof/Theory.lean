import VisualProof.Proof.Theorem

namespace VisualProof.Proof

/-- An ordered collection of theorem schemas carrying concrete replay
certificates. -/
inductive VerifiedTheorems : List TheoremSchema → Type
  | empty : VerifiedTheorems []
  | append {prior : List TheoremSchema}
      (verified : VerifiedTheorems prior)
      (checked : CheckedTheorem) :
      VerifiedTheorems (prior ++ [checked.schema])

/-- A collection of theorem schemas and their concrete replay certificates.
Its semantic interpretation is established in the proof layer by composing
execution refinement with aggregate rule soundness. -/
structure VerifiedTheory where
  theorems : List TheoremSchema
  verification : VerifiedTheorems theorems

end VisualProof.Proof
