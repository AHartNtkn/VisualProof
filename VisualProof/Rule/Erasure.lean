import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

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

end Erasure

def Erasure : Rule :=
  Contextual Erasure.Local

theorem Erasure.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Erasure source target)
    (targetIso : OpenDiagramIso target target') :
    Erasure source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Erasure.respectsTargetIso
    (step : Erasure source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Erasure source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Erasure.iso (OpenDiagramIso.refl source) step targetIso

theorem Erasure.backward_respectsTargetIso
    (step : Erasure target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Erasure target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Erasure.iso targetIso step (OpenDiagramIso.refl source)

end VisualProof.Rule
