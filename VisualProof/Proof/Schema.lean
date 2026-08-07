import VisualProof.Concrete.Semantics

namespace VisualProof.Proof

open VisualProof.Concrete

open VisualProof
open Diagram

/-- A meta-level theorem claim between checked open diagrams with one ordered
boundary interface. The schema is certification data, not primitive rule
content. -/
structure TheoremSchema where
  left : Concrete.CheckedOpen
  right : Concrete.CheckedOpen
  sameBoundaryArity : left.val.boundary.length = right.val.boundary.length

/-- Semantic validity of a meta-level theorem schema. -/
def TheoremSchema.Valid (schema : TheoremSchema) (model : Model) : Prop :=
  ∀ args : Fin schema.left.val.boundary.length → model.Carrier,
    schema.left.denote model args →
      schema.right.denote model
        (args ∘ Fin.cast schema.sameBoundaryArity.symm)

end VisualProof.Proof
