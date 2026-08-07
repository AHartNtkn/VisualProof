import VisualProof.Diagram.Algebra
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
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems body wireMap relationMap)
        (Region.spliceAt hostLocal hostItems
          (wrap arity body) wireMap relationMap)

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

theorem Vacuity.symm
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Vacuity source target) :
    Vacuity target source := by
  rcases step with ⟨wires, rels, before, after, occurrence, targetIso,
    localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    host_iso := targetIso
  }
  refine ⟨wires, rels, after, before, reverseOccurrence,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse, symmetric] at localEvidence ⊢
  · exact localEvidence.elim Or.inr Or.inl
  · exact localEvidence.elim Or.inr Or.inl

end VisualProof.Rule
