import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

inductive Local : LocalRule
  | erase
      (kept removed : Region wires rels) :
      Local (kept.conjoin removed) kept

end Erasure

def Erasure : Rule :=
  Contextual Erasure.Local

theorem Erasure.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Erasure source target)
    (targetIso : OpenDiagramIso target target') :
    Erasure source' target' := by
  exact Contextual.iso sourceIso step targetIso

end VisualProof.Rule
