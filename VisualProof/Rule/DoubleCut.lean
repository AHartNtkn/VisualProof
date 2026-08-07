import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace DoubleCut

def wrap (body : Region wires rels) :
    Region wires rels :=
  .mk 0
    (.cons
      (.cut (.mk 0 (.cons (.cut body) .nil)))
      .nil)

inductive Local : LocalRule
  | introduce
      (body : Region wires rels) :
      Local body (wrap body)

end DoubleCut

def DoubleCut : Rule :=
  Contextual (symmetric DoubleCut.Local)

theorem DoubleCut.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : DoubleCut source target)
    (targetIso : OpenDiagramIso target target') :
    DoubleCut source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule
