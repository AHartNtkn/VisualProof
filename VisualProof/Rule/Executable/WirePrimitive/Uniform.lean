import VisualProof.Rule.Relation

namespace VisualProof.Rule.WirePrimitive.Executable

open Theory
open Diagram

namespace Symmetric

inductive ForwardIndex (localRule : LocalRule) {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | direct
      (evidence : localRule before after)
      (occurrence : Occurrence before source)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      ForwardIndex localRule source
  | reverse
      (evidence : localRule after before)
      (occurrence : Occurrence before source)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      ForwardIndex localRule source

def BackwardIndex (localRule : LocalRule) {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex localRule source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex localRule source → OpenDiagram boundary
  | .direct _ occurrence targetCanonical targetExternalTwoEnded
  | .reverse _ occurrence targetCanonical targetExternalTwoEnded =>
      occurrence.interface.withBody (occurrence.context.fill _)
        targetCanonical targetExternalTwoEnded

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex localRule source → OpenDiagram boundary := runForward source

theorem contextual_symm
    (localRule : LocalRule)
    (step : Contextual (fun {wires} before after =>
      symmetric (@localRule wires) before after) source target) :
    Contextual (fun {wires} before after =>
      symmetric (@localRule wires) before after) target source := by
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

theorem forward_exact (localRule : LocalRule)
    (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex localRule source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Contextual (fun {wires} before after =>
        symmetric (@localRule wires) before after) source target := by
  constructor
  · rintro ⟨index, ⟨targetIso⟩⟩
    cases index with
    | direct evidence occurrence targetCanonical targetExternalTwoEnded =>
        exact ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, targetIso.symm,
          atPolarity_symmetric_of occurrence.context.polarity evidence⟩
    | reverse evidence occurrence targetCanonical targetExternalTwoEnded =>
        refine ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, targetIso.symm, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr evidence
        · exact Or.inl evidence
  · rintro ⟨wires, before, after, occurrence, targetCanonical,
      targetExternalTwoEnded, targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · exact ⟨.direct direct occurrence targetCanonical
            targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
        · exact ⟨.reverse reverse occurrence targetCanonical
            targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · exact ⟨.reverse reverse occurrence targetCanonical
            targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
        · exact ⟨.direct direct occurrence targetCanonical
            targetExternalTwoEnded, ⟨targetIso.symm⟩⟩

theorem backward_exact (localRule : LocalRule)
    (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex localRule source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Contextual (fun {wires} before after =>
        symmetric (@localRule wires) before after) target source := by
  constructor
  · intro witness
    exact contextual_symm localRule
      ((forward_exact localRule source target).mp witness)
  · intro step
    exact (forward_exact localRule source target).mpr
      (contextual_symm localRule step)

def compileForward (localRule : LocalRule) (source : OpenDiagram boundary) :=
  runForward (localRule := localRule) source
def compileBackward (localRule : LocalRule) (source : OpenDiagram boundary) :=
  runBackward (localRule := localRule) source

end Symmetric

namespace Directed

inductive ForwardIndex (localRule : LocalRule) {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | positive
      (evidence : localRule before after)
      (occurrence : Occurrence before source)
      (polarity : occurrence.context.polarity = .positive)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      ForwardIndex localRule source
  | negative
      (evidence : localRule after before)
      (occurrence : Occurrence before source)
      (polarity : occurrence.context.polarity = .negative)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      ForwardIndex localRule source

inductive BackwardIndex (localRule : LocalRule) {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | positive
      (evidence : localRule after before)
      (occurrence : Occurrence before source)
      (polarity : occurrence.context.polarity = .positive)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      BackwardIndex localRule source
  | negative
      (evidence : localRule before after)
      (occurrence : Occurrence before source)
      (polarity : occurrence.context.polarity = .negative)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.context.fill after)) :
      BackwardIndex localRule source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex localRule source → OpenDiagram boundary
  | .positive _ occurrence _ targetCanonical targetExternalTwoEnded
  | .negative _ occurrence _ targetCanonical targetExternalTwoEnded =>
      occurrence.interface.withBody (occurrence.context.fill _)
        targetCanonical targetExternalTwoEnded

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex localRule source → OpenDiagram boundary
  | .positive _ occurrence _ targetCanonical targetExternalTwoEnded
  | .negative _ occurrence _ targetCanonical targetExternalTwoEnded =>
      occurrence.interface.withBody (occurrence.context.fill _)
        targetCanonical targetExternalTwoEnded

theorem forward_exact (localRule : LocalRule)
    (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex localRule source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Contextual localRule source target := by
  constructor
  · rintro ⟨index, ⟨targetIso⟩⟩
    cases index with
    | positive evidence occurrence polarity targetCanonical twoEnded =>
        refine ⟨_, _, _, occurrence, targetCanonical, twoEnded,
          targetIso.symm, ?_⟩
        simpa [polarity, atPolarity] using evidence
    | negative evidence occurrence polarity targetCanonical twoEnded =>
        refine ⟨_, _, _, occurrence, targetCanonical, twoEnded,
          targetIso.symm, ?_⟩
        simpa [polarity, atPolarity, converse] using evidence
  · rintro ⟨wires, before, after, occurrence, targetCanonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        have evidence : localRule before after := by
          simpa [polarity, atPolarity] using localEvidence
        exact ⟨.positive evidence occurrence polarity targetCanonical twoEnded,
          ⟨targetIso.symm⟩⟩
    | negative =>
        have evidence : localRule after before := by
          simpa [polarity, atPolarity, converse] using localEvidence
        exact ⟨.negative evidence occurrence polarity targetCanonical twoEnded,
          ⟨targetIso.symm⟩⟩

theorem backward_exact (localRule : LocalRule)
    (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex localRule source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Contextual localRule target source := by
  constructor
  · rintro ⟨index, ⟨targetIso⟩⟩
    cases index with
    | positive evidence occurrence polarity targetCanonical twoEnded =>
        let reverseOccurrence : Occurrence _ target := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := twoEnded
          host_iso := targetIso.symm
        }
        refine ⟨_, _, _, reverseOccurrence, occurrence.sourceCanonical,
          occurrence.sourceExternalTwoEnded, occurrence.host_iso, ?_⟩
        simpa [reverseOccurrence, polarity, atPolarity] using evidence
    | negative evidence occurrence polarity targetCanonical twoEnded =>
        let reverseOccurrence : Occurrence _ target := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := twoEnded
          host_iso := targetIso.symm
        }
        refine ⟨_, _, _, reverseOccurrence, occurrence.sourceCanonical,
          occurrence.sourceExternalTwoEnded, occurrence.host_iso, ?_⟩
        simpa [reverseOccurrence, polarity, atPolarity, converse] using evidence
  · rintro ⟨wires, before, after, occurrence, targetCanonical, twoEnded,
      targetIso, localEvidence⟩
    let reverseOccurrence : Occurrence after source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := targetCanonical
      sourceExternalTwoEnded := twoEnded
      host_iso := targetIso
    }
    cases polarity : occurrence.context.polarity with
    | positive =>
        have evidence : localRule before after := by
          simpa [polarity, atPolarity] using localEvidence
        exact ⟨.positive evidence reverseOccurrence polarity
          occurrence.sourceCanonical occurrence.sourceExternalTwoEnded,
          ⟨occurrence.host_iso.symm⟩⟩
    | negative =>
        have evidence : localRule after before := by
          simpa [polarity, atPolarity, converse] using localEvidence
        exact ⟨.negative evidence reverseOccurrence polarity
          occurrence.sourceCanonical occurrence.sourceExternalTwoEnded,
          ⟨occurrence.host_iso.symm⟩⟩

def compileForward (localRule : LocalRule) (source : OpenDiagram boundary) :=
  runForward (localRule := localRule) source
def compileBackward (localRule : LocalRule) (source : OpenDiagram boundary) :=
  runBackward (localRule := localRule) source

end Directed

end VisualProof.Rule.WirePrimitive.Executable
