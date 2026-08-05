import VisualProof.Proof.Theorem

namespace VisualProof.Proof

open VisualProof

/-- An ordered collection of independently checked theorem schemas. -/
inductive VerifiedTheorems : List TheoremSchema → Type
  | empty : VerifiedTheorems []
  | append {prior : List TheoremSchema}
      (verified : VerifiedTheorems prior)
      (checked : CheckedTheorem) :
      VerifiedTheorems (prior ++ [checked.schema])

namespace VerifiedTheorems

/-- Every schema in an ordered checked collection is semantically valid. -/
theorem get_sound
    {theorems : List TheoremSchema}
    (verified : VerifiedTheorems theorems)
    (index : Fin theorems.length) :
    (theorems.get index).Valid model := by
  induction verified with
  | empty =>
      exact Fin.elim0 index
  | @append prior verified checked ih =>
      by_cases hprior : index.val < prior.length
      · let priorIndex : Fin prior.length := ⟨index.val, hprior⟩
        have hget : (prior ++ [checked.schema]).get index =
            prior.get priorIndex := by
          simp [List.get_eq_getElem, List.getElem_append_left hprior,
            priorIndex]
        rw [hget]
        exact ih priorIndex
      · have hlast : index.val = prior.length := by
          have hin := index.isLt
          simp only [List.length_append, List.length_cons, List.length_nil]
            at hin
          omega
        have hget : (prior ++ [checked.schema]).get index =
            checked.schema := by
          simp [List.get_eq_getElem, hlast]
        rw [hget]
        exact checkedTheorem_sound checked

end VerifiedTheorems

/-- A complete verified logical theory represented by its ordered theorem
schemas and their independent certifications. -/
structure VerifiedTheory where
  theorems : List TheoremSchema
  verification : VerifiedTheorems theorems

namespace VerifiedTheory

/-- Every indexed theorem in a verified theory is semantically valid. -/
theorem sound (theory : VerifiedTheory) (model : Model) :
    ∀ index : Fin theory.theorems.length,
      (theory.theorems.get index).Valid model :=
  theory.verification.get_sound

theorem theorem_sound (theory : VerifiedTheory)
    (model : Model)
    (index : Fin theory.theorems.length) :
    (theory.theorems.get index).Valid model :=
  theory.sound model index

end VerifiedTheory

/-- Membership in a verified theory entails semantic validity. -/
theorem verifiedTheory_sound
    (theory : VerifiedTheory)
    (model : Model)
    (schema : TheoremSchema) (member : schema ∈ theory.theorems) :
    schema.Valid model := by
  obtain ⟨index, hget⟩ := List.mem_iff_get.mp member
  rw [← hget]
  exact theory.theorem_sound model index

end VisualProof.Proof
