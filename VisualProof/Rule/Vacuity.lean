import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Vacuity

def wrap
    (arity : Nat)
    (body : Region wires rels) :
    Region wires rels :=
  .mk 0
    (.cons
      (.bubble arity
        (body.renameRelations
          (RelationRenaming.weaken arity)))
      .nil)

inductive Local : LocalRule
  | introduce
      (arity : Nat)
      (body : Region wires rels) :
      Local body (wrap arity body)

end Vacuity

end VisualProof.Rule
