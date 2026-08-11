import VisualProof.Diagram.Algebra
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
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems body wireMap relationMap)
        (Region.spliceAt hostLocal hostItems
          (wrap body) wireMap relationMap)

end DoubleCut

def DoubleCut : Rule :=
  Contextual (symmetric DoubleCut.Local)

/-- Introduce a double cut at an already presented occurrence.  The
occurrence and target isomorphism are the complete endpoint authority; the
rule layer only packages the local introduction and its contextual lift. -/
theorem DoubleCut.introduceAt
    {arity wires hostLocal materialWires : Nat}
    {rels materialRels : RelCtx}
    {source target : OpenDiagram arity}
    (hostItems : ItemSeq (wires + hostLocal) rels)
    (body : Region materialWires materialRels)
    (wireMap : Fin materialWires → Fin (wires + hostLocal))
    (relationMap : RelationRenaming materialRels rels)
    (occurrence : Occurrence
      (Region.spliceAt hostLocal hostItems body wireMap relationMap) source)
    (targetIso : OpenDiagramIso target
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems (DoubleCut.wrap body)
            wireMap relationMap)))) :
    DoubleCut source target := by
  refine ⟨wires, rels,
    Region.spliceAt hostLocal hostItems body wireMap relationMap,
    Region.spliceAt hostLocal hostItems (DoubleCut.wrap body)
      wireMap relationMap,
    occurrence, targetIso, ?_⟩
  cases polarity : occurrence.context.polarity with
  | positive =>
      exact Or.inl (.introduce hostLocal hostItems body wireMap relationMap)
  | negative =>
      exact Or.inr (.introduce hostLocal hostItems body wireMap relationMap)

theorem DoubleCut.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : DoubleCut source target)
    (targetIso : OpenDiagramIso target target') :
    DoubleCut source' target' :=
  Contextual.iso sourceIso step targetIso

theorem DoubleCut.symm
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : DoubleCut source target) :
    DoubleCut target source := by
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
