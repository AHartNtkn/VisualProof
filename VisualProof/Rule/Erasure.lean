import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace UncappedErasure

structure Description (outer : List Sig) where
  materialWires : List Sig
  hostLocals : List Sig
  hostItems : ItemSeq (outer ++ hostLocals)
  material : Region materialWires
  wireMap : WireRenaming materialWires (outer ++ hostLocals)

def Description.source (description : Description outer) : Region outer :=
  Region.spliceAt description.hostLocals description.hostItems
    description.material description.wireMap

def Description.target (description : Description outer) : Region outer :=
  .mk description.hostLocals description.hostItems

inductive Local : LocalRule
  | erase (description : Description wires) :
      Local description.source description.target

end UncappedErasure

def UncappedErasure : Rule :=
  Contextual UncappedErasure.Local

theorem UncappedErasure.iso
    (sourceIso : OpenDiagramIso source source')
    (step : UncappedErasure source target)
    (targetIso : OpenDiagramIso target target') :
    UncappedErasure source' target' :=
  Contextual.iso sourceIso step targetIso

theorem UncappedErasure.respectsTargetIso
    (step : UncappedErasure source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    UncappedErasure source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact UncappedErasure.iso (OpenDiagramIso.refl source) step targetIso

theorem UncappedErasure.backward_respectsTargetIso
    (step : UncappedErasure target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    UncappedErasure target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact UncappedErasure.iso targetIso step (OpenDiagramIso.refl source)

end VisualProof.Rule
