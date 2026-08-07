import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

inductive Local : LocalRule
  | erase
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems material wireMap relationMap)
        (.mk hostLocal hostItems)

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
