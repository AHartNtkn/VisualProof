import VisualProof.Diagram.Algebra
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace DoubleCut

private def siteLocalTarget (outer hostLocals : List Sig) :
    WireRenaming hostLocals (outer ++ hostLocals) :=
  ⟨fun wire => Var.appendRight outer wire⟩

/-- Exactly the site-owned wires whose selected incidences would otherwise
move wholly below the new outer cut. -/
def passPins (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (selected : Region (outer ++ hostLocals)) :
    ItemSeq (outer ++ hostLocals) :=
  ItemSeq.pinWires hostLocals (siteLocalTarget outer hostLocals)
    (fun localWire => decide
      (selected.incidencePaths
          (outer.length + localWire.index.val) ≠ [] ∧
        hostItems.incidencePaths
          (outer.length + localWire.index.val) 0 = []))

/-- The zero-local material inserted at the selected site. -/
def wrappedMaterial (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (selected : Region (outer ++ hostLocals)) :
    Region (outer ++ hostLocals) :=
  let appendNil : WireRenaming (outer ++ hostLocals)
      ((outer ++ hostLocals) ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  let inner : Region (outer ++ hostLocals) :=
    .mk [] ((ItemSeq.cons (.cut selected) .nil).renameWires appendNil)
  .mk [] (((passPins hostLocals hostItems selected).append
    (.cons (.cut inner) .nil)).renameWires appendNil)

def introducedAt (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (selected : Region (outer ++ hostLocals)) : Region outer :=
  Region.adjoinAt hostLocals hostItems
    (wrappedMaterial hostLocals hostItems selected)

inductive Local : LocalRule
  | introduce
      (hostLocals : List Sig)
      (hostItems : ItemSeq (outer ++ hostLocals))
      (selected : Region (outer ++ hostLocals)) :
      Local
        (Region.adjoinAt hostLocals hostItems selected)
        (introducedAt hostLocals hostItems selected)

end DoubleCut

def DoubleCut : Rule :=
  Contextual (symmetric DoubleCut.Local)

theorem DoubleCut.iso
    (sourceIso : OpenDiagramIso source source')
    (step : DoubleCut source target)
    (targetIso : OpenDiagramIso target target') :
    DoubleCut source' target' :=
  Contextual.iso sourceIso step targetIso

theorem DoubleCut.respectsTargetIso
    (step : DoubleCut source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    DoubleCut source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact DoubleCut.iso (OpenDiagramIso.refl source) step targetIso

theorem DoubleCut.backward_respectsTargetIso
    (step : DoubleCut target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    DoubleCut target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact DoubleCut.iso targetIso step (OpenDiagramIso.refl source)

theorem DoubleCut.symm
    (step : DoubleCut source target) : DoubleCut target source := by
  rcases step with ⟨wires, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    host_iso := targetIso
  }
  refine ⟨wires, after, before, reverseOccurrence,
    occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse, symmetric] at localEvidence ⊢
  · exact localEvidence.elim Or.inr Or.inl
  · exact localEvidence.elim Or.inr Or.inl

end VisualProof.Rule
