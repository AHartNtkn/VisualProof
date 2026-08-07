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

def Vacuity : Rule :=
  Contextual (symmetric Vacuity.Local)

theorem Vacuity.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : Vacuity source target)
    (targetIso : OpenDiagramIso target target') :
    Vacuity source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule
