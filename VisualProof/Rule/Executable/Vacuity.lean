import VisualProof.Rule.Vacuity

namespace VisualProof.Rule.Vacuity

open Theory
open Diagram

inductive ForwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | introduce
      (binderArity hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems body wireMap relationMap) source) :
      ForwardIndex source
  | eliminate
      (binderArity hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems (wrap binderArity body)
          wireMap relationMap) source) :
      ForwardIndex source

inductive BackwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | introduce
      (binderArity hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems body wireMap relationMap) source) :
      BackwardIndex source
  | eliminate
      (binderArity hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels)
      (occurrence : Occurrence
        (Region.spliceAt hostLocal hostItems (wrap binderArity body)
          wireMap relationMap) source) :
      BackwardIndex source

def runForward (source : OpenDiagram arity) :
    ForwardIndex source → OpenDiagram arity
  | .introduce binderArity hostLocal hostItems body wireMap relationMap
      occurrence =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems (wrap binderArity body)
            wireMap relationMap))
  | .eliminate _ hostLocal hostItems body wireMap relationMap occurrence =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems body wireMap relationMap))

def runBackward (source : OpenDiagram arity) :
    BackwardIndex source → OpenDiagram arity
  | .introduce binderArity hostLocal hostItems body wireMap relationMap
      occurrence =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems (wrap binderArity body)
            wireMap relationMap))
  | .eliminate _ hostLocal hostItems body wireMap relationMap occurrence =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocal hostItems body wireMap relationMap))

theorem forward_exact (source target : OpenDiagram arity) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.Vacuity source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | introduce binderArity hostLocal hostItems body wireMap relationMap
        occurrence =>
        refine ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.introduce binderArity hostLocal hostItems body wireMap
            relationMap)
    | eliminate binderArity hostLocal hostItems body wireMap relationMap
        occurrence =>
        refine ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr
            (Local.introduce binderArity hostLocal hostItems body wireMap
              relationMap)
        · exact Or.inl
            (Local.introduce binderArity hostLocal hostItems body wireMap
              relationMap)
  · rintro ⟨wires, rels, before, after, occurrence, targetIso,
      localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · cases direct with
          | introduce binderArity hostLocal hostItems body wireMap relationMap =>
              exact ⟨.introduce binderArity hostLocal hostItems body wireMap
                relationMap occurrence, ⟨targetIso.symm⟩⟩
        · cases reverse with
          | introduce binderArity hostLocal hostItems body wireMap relationMap =>
              exact ⟨.eliminate binderArity hostLocal hostItems body wireMap
                relationMap occurrence, ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · cases reverse with
          | introduce binderArity hostLocal hostItems body wireMap relationMap =>
              exact ⟨.eliminate binderArity hostLocal hostItems body wireMap
                relationMap occurrence, ⟨targetIso.symm⟩⟩
        · cases direct with
          | introduce binderArity hostLocal hostItems body wireMap relationMap =>
              exact ⟨.introduce binderArity hostLocal hostItems body wireMap
                relationMap occurrence, ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram arity) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.Vacuity target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    have forwardWitness :
        ∃ forwardIndex : ForwardIndex source,
          OpenDiagram.Isomorphic (runForward source forwardIndex) target := by
      cases index with
      | introduce binderArity hostLocal hostItems body wireMap relationMap
          occurrence =>
          exact ⟨.introduce binderArity hostLocal hostItems body wireMap
            relationMap occurrence, isomorphic⟩
      | eliminate binderArity hostLocal hostItems body wireMap relationMap
          occurrence =>
          exact ⟨.eliminate binderArity hostLocal hostItems body wireMap
            relationMap occurrence, isomorphic⟩
    exact Rule.Vacuity.symm ((forward_exact source target).mp forwardWitness)
  · intro step
    rcases (forward_exact source target).mpr (Rule.Vacuity.symm step) with
      ⟨index, isomorphic⟩
    cases index with
    | introduce binderArity hostLocal hostItems body wireMap relationMap
        occurrence =>
        exact ⟨.introduce binderArity hostLocal hostItems body wireMap
          relationMap occurrence, isomorphic⟩
    | eliminate binderArity hostLocal hostItems body wireMap relationMap
        occurrence =>
        exact ⟨.eliminate binderArity hostLocal hostItems body wireMap
          relationMap occurrence, isomorphic⟩

end VisualProof.Rule.Vacuity
