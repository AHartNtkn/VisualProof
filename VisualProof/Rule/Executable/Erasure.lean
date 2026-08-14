import VisualProof.Rule.Erasure

namespace VisualProof.Rule.Erasure

open Theory
open Diagram

inductive ForwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | erase
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems material wireMap relationMap)
        source)
      (polarity : occurrence.context.polarity = .positive) :
      ForwardIndex source
  | insert
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence (.mk hostLocal hostItems) source)
      (polarity : occurrence.context.polarity = .negative) :
      ForwardIndex source

inductive BackwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | insert
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence (.mk hostLocal hostItems) source)
      (polarity : occurrence.context.polarity = .positive) :
      BackwardIndex source
  | erase
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems material wireMap relationMap)
        source)
      (polarity : occurrence.context.polarity = .negative) :
      BackwardIndex source

def runForward (source : OpenDiagram arity) :
    ForwardIndex source → OpenDiagram arity
  | .erase _ hostItems _ _ _ occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _ hostItems))
  | .insert hostLocal hostItems material wireMap relationMap occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems material wireMap relationMap))

def runBackward (source : OpenDiagram arity) :
    BackwardIndex source → OpenDiagram arity
  | .insert hostLocal hostItems material wireMap relationMap occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems material wireMap relationMap))
  | .erase _ hostItems _ _ _ occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _ hostItems))

theorem forward_exact (source target : OpenDiagram arity) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.Erasure source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | erase hostLocal hostItems material wireMap relationMap occurrence
        polarity =>
        refine ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.erase hostLocal hostItems material wireMap relationMap
    | insert hostLocal hostItems material wireMap relationMap occurrence
        polarity =>
        refine ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.erase hostLocal hostItems material wireMap relationMap
  · rintro ⟨wires, rels, before, after, occurrence, targetIso,
      localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity] at localEvidence
        cases localEvidence with
        | erase hostLocal hostItems material wireMap relationMap =>
            exact ⟨.erase hostLocal hostItems material wireMap relationMap
              occurrence polarity, ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, converse] at localEvidence
        cases localEvidence with
        | erase hostLocal hostItems material wireMap relationMap =>
            exact ⟨.insert hostLocal hostItems material wireMap relationMap
              occurrence polarity, ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram arity) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.Erasure target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply backward_respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | insert hostLocal hostItems material wireMap relationMap occurrence
        polarity =>
        let outputOccurrence : Occurrence
            (Region.spliceAt hostLocal hostItems material wireMap relationMap)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Region.spliceAt hostLocal hostItems material wireMap
                  relationMap))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine ⟨_, _, _, _, outputOccurrence, occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.erase hostLocal hostItems material wireMap relationMap
    | erase hostLocal hostItems material wireMap relationMap occurrence
        polarity =>
        let outputOccurrence : Occurrence (.mk hostLocal hostItems)
            (occurrence.interface.withBody
              (occurrence.context.fill (.mk hostLocal hostItems))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine ⟨_, _, _, _, outputOccurrence, occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.erase hostLocal hostItems material wireMap relationMap
  · rintro ⟨wires, rels, before, after, occurrence, sourceIso,
      localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity] at localEvidence
        cases localEvidence with
        | erase hostLocal hostItems material wireMap relationMap =>
            let sourceOccurrence : Occurrence (.mk hostLocal hostItems)
                source := {
              interface := occurrence.interface
              context := occurrence.context
              host_iso := sourceIso
            }
            exact ⟨.insert hostLocal hostItems material wireMap relationMap
              sourceOccurrence polarity, ⟨occurrence.host_iso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, converse] at localEvidence
        cases localEvidence with
        | erase hostLocal hostItems material wireMap relationMap =>
            let sourceOccurrence : Occurrence
                (Region.spliceAt hostLocal hostItems material wireMap
                  relationMap) source := {
              interface := occurrence.interface
              context := occurrence.context
              host_iso := sourceIso
            }
            exact ⟨.erase hostLocal hostItems material wireMap relationMap
              sourceOccurrence polarity, ⟨occurrence.host_iso.symm⟩⟩

end VisualProof.Rule.Erasure
