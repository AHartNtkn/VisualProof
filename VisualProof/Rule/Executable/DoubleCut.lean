import VisualProof.Rule.DoubleCut

namespace VisualProof.Rule.DoubleCut

open Theory
open Diagram

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | introduce
      (hostLocals : List Sig)
      (hostItems : ItemSeq (wires ++ hostLocals))
      (selected : Region (wires ++ hostLocals))
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems selected) source)
      (targetCanonical : (occurrence.context.fill
        (introducedAt hostLocals hostItems selected)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill
          (introducedAt hostLocals hostItems selected))) :
      ForwardIndex source
  | eliminate
      (hostLocals : List Sig)
      (hostItems : ItemSeq (wires ++ hostLocals))
      (selected : Region (wires ++ hostLocals))
      (occurrence : Occurrence
        (introducedAt hostLocals hostItems selected) source)
      (targetCanonical : (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems selected)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems selected))) :
      ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .introduce hostLocals hostItems selected occurrence targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (introducedAt hostLocals hostItems selected))
        targetCanonical targetExternalTwoEnded
  | .eliminate hostLocals hostItems selected occurrence targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems selected))
        targetCanonical targetExternalTwoEnded

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.DoubleCut source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply Rule.DoubleCut.respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | introduce hostLocals hostItems selected occurrence targetCanonical
        targetExternalTwoEnded =>
        refine ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.introduce hostLocals hostItems selected)
    | eliminate hostLocals hostItems selected occurrence targetCanonical
        targetExternalTwoEnded =>
        refine ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr (Local.introduce hostLocals hostItems selected)
        · exact Or.inl (Local.introduce hostLocals hostItems selected)
  · rintro ⟨wires, before, after, occurrence, targetCanonical,
      targetExternalTwoEnded, targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · cases direct with
          | introduce hostLocals hostItems selected =>
              exact ⟨.introduce hostLocals hostItems selected occurrence
                targetCanonical targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
        · cases reverse with
          | introduce hostLocals hostItems selected =>
              exact ⟨.eliminate hostLocals hostItems selected occurrence
                targetCanonical targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · cases reverse with
          | introduce hostLocals hostItems selected =>
              exact ⟨.eliminate hostLocals hostItems selected occurrence
                targetCanonical targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
        · cases direct with
          | introduce hostLocals hostItems selected =>
              exact ⟨.introduce hostLocals hostItems selected occurrence
                targetCanonical targetExternalTwoEnded, ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.DoubleCut target source := by
  constructor
  · intro witness
    have forwardWitness : ∃ index : ForwardIndex source,
        OpenDiagram.Isomorphic (runForward source index) target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.DoubleCut.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.DoubleCut.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.DoubleCut
