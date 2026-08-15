import VisualProof.Rule.Presentation

namespace VisualProof.Rule.Presentation

open Theory
open Diagram

/-- Exact source-indexed presentation replacement.  The index contains the
source suffix configuration and replacement data, never a target diagram,
occurrence search, or normalization witness. -/
inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | replace
      (locals : List Sig)
      (retained : ItemSeq (wires ++ locals))
      (signature : Sig)
      (sourceConfiguration targetConfiguration :
        Configuration (wires ++ locals) signature)
      (occurrence : Occurrence
        (region locals retained sourceConfiguration) source)
      (applicability : Applicability wires locals retained
        sourceConfiguration targetConfiguration) :
      ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .replace locals retained _ _ targetConfiguration
      occurrence applicability =>
      let validity := replacementValidity occurrence applicability
      occurrence.interface.withBody
        (occurrence.context.fill
          (region locals retained targetConfiguration))
        validity.1 validity.2

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.Presentation source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply Rule.Presentation.respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | replace locals retained signature sourceConfiguration
        targetConfiguration occurrence applicability =>
        let validity := replacementValidity occurrence applicability
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.replace locals retained signature sourceConfiguration
            targetConfiguration applicability)
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · cases direct with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              exact ⟨.replace locals retained signature sourceConfiguration
                targetConfiguration occurrence applicability,
                ⟨targetIso.symm⟩⟩
        · cases reverse with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              exact ⟨.replace locals retained signature targetConfiguration
                sourceConfiguration occurrence
                (applicability.symm
                  ((occurrence.context.holeCanonical _
                    canonical).1)), ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · cases reverse with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              exact ⟨.replace locals retained signature targetConfiguration
                sourceConfiguration occurrence
                (applicability.symm
                  ((occurrence.context.holeCanonical _
                    canonical).1)), ⟨targetIso.symm⟩⟩
        · cases direct with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              exact ⟨.replace locals retained signature sourceConfiguration
                targetConfiguration occurrence applicability,
                ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.Presentation target source := by
  constructor
  · intro witness
    have forwardWitness : ∃ index : ForwardIndex source,
        OpenDiagram.Isomorphic (runForward source index) target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.Presentation.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.Presentation.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.Presentation
