import VisualProof.Diagram.Algebra
import VisualProof.Diagram.UnaryIdentity
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

namespace Erasure

abbrev Description (outer : List Sig) :=
  UncappedErasure.Description outer

def Description.source (description : Description outer) : Region outer :=
  UncappedErasure.Description.source description

/-- Unary caps for every surviving host wire the erasure would leave
under-rooted: at least one incidence, but not rooted-two. -/
def Description.caps (description : Description outer) :
    ItemSeq (outer ++ description.hostLocals) :=
  ItemSeq.pinWires (outer ++ description.hostLocals) WireRenaming.id
    (fun wire => decide
      (1 ≤ (description.hostItems.incidencePaths wire.index.val 0).length ∧
        ¬ RegionPath.RootedTwo
          (description.hostItems.incidencePaths wire.index.val 0)))

def Description.target (description : Description outer) : Region outer :=
  .mk description.hostLocals
    (description.hostItems.append description.caps)

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
