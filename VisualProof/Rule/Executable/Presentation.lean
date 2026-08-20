import VisualProof.Rule.Presentation

namespace VisualProof.Rule.Presentation

open Theory
open Diagram

/-- Exact source-indexed presentation replacement data. Applicability is
decided by the runner and is not supplied by its caller. -/
inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | replace
      (locals : List Sig)
      (retained : ItemSeq (wires ++ locals))
      (signature : Sig)
      (sourceConfiguration targetConfiguration :
        Configuration (wires ++ locals) signature)
      (occurrence : Occurrence
        (region locals retained sourceConfiguration) source) :
      ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .replace locals retained _ sourceConfiguration targetConfiguration
      occurrence =>
      if applicability : Applicability _ locals retained
          sourceConfiguration targetConfiguration then
        let validity := replacementValidity occurrence applicability
        some (occurrence.interface.withBody
          (occurrence.context.fill
            (region locals retained targetConfiguration))
          validity.1 validity.2)
      else none

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Presentation source target := by
  constructor
  · rintro ⟨index, output, computed, isomorphic⟩
    apply Rule.Presentation.respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | replace locals retained signature sourceConfiguration
        targetConfiguration occurrence =>
        simp only [runForward] at computed
        split at computed
        next applicability =>
          let validity := replacementValidity occurrence applicability
          simp only [Option.some.injEq] at computed
          subst output
          refine ⟨_, _, _, occurrence, validity.1, validity.2,
            OpenDiagramIso.refl _, ?_⟩
          exact atPolarity_symmetric_of occurrence.context.polarity
            (Local.replace locals retained signature sourceConfiguration
              targetConfiguration applicability)
        next => simp at computed
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · cases direct with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              let validity := replacementValidity occurrence applicability
              refine ⟨.replace locals retained signature sourceConfiguration
                targetConfiguration occurrence,
                occurrence.interface.withBody
                  (occurrence.context.fill
                    (region locals retained targetConfiguration))
                  validity.1 validity.2, ?_, ⟨targetIso.symm⟩⟩
              simp [runForward, applicability]
        · cases reverse with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              let reverseApplicability := applicability.symm
                ((occurrence.context.holeCanonical _ canonical).1)
              let validity := replacementValidity occurrence reverseApplicability
              refine ⟨.replace locals retained signature targetConfiguration
                sourceConfiguration occurrence,
                occurrence.interface.withBody
                  (occurrence.context.fill
                    (region locals retained sourceConfiguration))
                  validity.1 validity.2, ?_, ⟨targetIso.symm⟩⟩
              simp [runForward, reverseApplicability]
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · cases reverse with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              let reverseApplicability := applicability.symm
                ((occurrence.context.holeCanonical _ canonical).1)
              let validity := replacementValidity occurrence reverseApplicability
              refine ⟨.replace locals retained signature targetConfiguration
                sourceConfiguration occurrence,
                occurrence.interface.withBody
                  (occurrence.context.fill
                    (region locals retained sourceConfiguration))
                  validity.1 validity.2, ?_, ⟨targetIso.symm⟩⟩
              simp [runForward, reverseApplicability]
        · cases direct with
          | replace locals retained signature sourceConfiguration
              targetConfiguration applicability =>
              let validity := replacementValidity occurrence applicability
              refine ⟨.replace locals retained signature sourceConfiguration
                targetConfiguration occurrence,
                occurrence.interface.withBody
                  (occurrence.context.fill
                    (region locals retained targetConfiguration))
                  validity.1 validity.2, ?_, ⟨targetIso.symm⟩⟩
              simp [runForward, applicability]

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Presentation target source := by
  constructor
  · intro witness
    have forwardWitness :
        ∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
          runForward source index = some output ∧
            OpenDiagram.Isomorphic output target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.Presentation.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.Presentation.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.Presentation
