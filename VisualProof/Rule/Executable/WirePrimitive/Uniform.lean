import VisualProof.Rule.Relation

namespace VisualProof.Rule.WirePrimitive.Executable

open Theory
open Diagram

def validateBody (interface : OpenDiagram boundary)
    (body : Region interface.external) : Option (OpenDiagram boundary) :=
  if canonical : body.Canonical then
    if twoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire body then
      some (interface.withBody body canonical twoEnded)
    else none
  else none

@[simp] theorem validateBody_of_valid
    (interface : OpenDiagram boundary) (body : Region interface.external)
    (canonical : body.Canonical)
    (twoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire body) :
    validateBody interface body =
      some (interface.withBody body canonical twoEnded) := by
  simp [validateBody, canonical, twoEnded]

structure Family.{u} where
  Description : List Sig → Type u
  source : {wires : List Sig} → Description wires → Region wires
  target : {wires : List Sig} → Description wires → Region wires

theorem contextualSymmetric_symm
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

namespace ComputedSymmetric

inductive Index.{u} (family : Family.{u}) {boundary : List Sig}
    (source : OpenDiagram boundary) : Type u
  | direct
      (description : family.Description wires)
      (occurrence : Occurrence (family.source description) source) :
      Index family source
  | reverse
      (description : family.Description wires)
      (occurrence : Occurrence (family.target description) source) :
      Index family source

def run (source : OpenDiagram boundary) :
    Index family source → Option (OpenDiagram boundary)
  | .direct description occurrence =>
      validateBody occurrence.interface
        (occurrence.context.fill (family.target description))
  | .reverse description occurrence =>
      validateBody occurrence.interface
        (occurrence.context.fill (family.source description))

theorem forward_exact (family : Family) (localRule : LocalRule)
    (build : ∀ {wires} (description : family.Description wires),
      localRule (family.source description) (family.target description))
    (view : ∀ {wires} {before after : Region wires},
      localRule before after →
        ∃ description : family.Description wires,
          before = family.source description ∧
            after = family.target description)
    (source target : OpenDiagram boundary) :
    (∃ (index : Index family source) (output : OpenDiagram boundary),
      run source index = some output ∧ OpenDiagram.Isomorphic output target) ↔
      Contextual (fun {wires} before after =>
        symmetric (@localRule wires) before after) source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | direct description occurrence =>
        simp only [run, validateBody] at computed
        split at computed
        next canonical =>
          split at computed
          next twoEnded =>
            simp only [Option.some.injEq] at computed
            subst output
            refine ⟨_, _, _, occurrence, canonical, twoEnded,
              outputIso.symm, ?_⟩
            exact atPolarity_symmetric_of occurrence.context.polarity
              (build description)
          next => simp at computed
        next => simp at computed
    | reverse description occurrence =>
        simp only [run, validateBody] at computed
        split at computed
        next canonical =>
          split at computed
          next twoEnded =>
            simp only [Option.some.injEq] at computed
            subst output
            refine ⟨_, _, _, occurrence, canonical, twoEnded,
              outputIso.symm, ?_⟩
            cases occurrence.context.polarity <;>
              simp only [atPolarity, symmetric, converse]
            · exact Or.inr (build description)
            · exact Or.inl (build description)
          next => simp at computed
        next => simp at computed
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · obtain ⟨description, beforeEq, afterEq⟩ := view direct
          subst before
          subst after
          refine ⟨.direct description occurrence,
            occurrence.interface.withBody
              (occurrence.context.fill (family.target description))
              canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
          exact validateBody_of_valid _ _ canonical twoEnded
        · obtain ⟨description, afterEq, beforeEq⟩ := view reverse
          subst before
          subst after
          refine ⟨.reverse description occurrence,
            occurrence.interface.withBody
              (occurrence.context.fill (family.source description))
              canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
          exact validateBody_of_valid _ _ canonical twoEnded
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · obtain ⟨description, afterEq, beforeEq⟩ := view reverse
          subst before
          subst after
          refine ⟨.reverse description occurrence,
            occurrence.interface.withBody
              (occurrence.context.fill (family.source description))
              canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
          exact validateBody_of_valid _ _ canonical twoEnded
        · obtain ⟨description, beforeEq, afterEq⟩ := view direct
          subst before
          subst after
          refine ⟨.direct description occurrence,
            occurrence.interface.withBody
              (occurrence.context.fill (family.target description))
              canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
          exact validateBody_of_valid _ _ canonical twoEnded

theorem backward_exact (family : Family) (localRule : LocalRule)
    (build : ∀ {wires} (description : family.Description wires),
      localRule (family.source description) (family.target description))
    (view : ∀ {wires} {before after : Region wires},
      localRule before after →
        ∃ description : family.Description wires,
          before = family.source description ∧
            after = family.target description)
    (source target : OpenDiagram boundary) :
    (∃ (index : Index family source) (output : OpenDiagram boundary),
      run source index = some output ∧ OpenDiagram.Isomorphic output target) ↔
      Contextual (fun {wires} before after =>
        symmetric (@localRule wires) before after) target source := by
  constructor
  · intro witness
    exact contextualSymmetric_symm localRule
      ((forward_exact family localRule build view source target).mp witness)
  · intro step
    exact (forward_exact family localRule build view source target).mpr
      (contextualSymmetric_symm localRule step)

end ComputedSymmetric

namespace ComputedDirected

inductive Index.{u} (family : Family.{u}) {boundary : List Sig}
    (source : OpenDiagram boundary) : Type u
  | direct
      (description : family.Description wires)
      (occurrence : Occurrence (family.source description) source) :
      Index family source
  | reverse
      (description : family.Description wires)
      (occurrence : Occurrence (family.target description) source) :
      Index family source

def runForward (source : OpenDiagram boundary) :
    Index family source → Option (OpenDiagram boundary)
  | .direct description occurrence =>
      match occurrence.context.polarity with
      | .positive =>
          validateBody occurrence.interface
            (occurrence.context.fill (family.target description))
      | .negative => none
  | .reverse description occurrence =>
      match occurrence.context.polarity with
      | .positive => none
      | .negative =>
          validateBody occurrence.interface
            (occurrence.context.fill (family.source description))

def runBackward (source : OpenDiagram boundary) :
    Index family source → Option (OpenDiagram boundary)
  | .direct description occurrence =>
      match occurrence.context.polarity with
      | .positive => none
      | .negative =>
          validateBody occurrence.interface
            (occurrence.context.fill (family.target description))
  | .reverse description occurrence =>
      match occurrence.context.polarity with
      | .positive =>
          validateBody occurrence.interface
            (occurrence.context.fill (family.source description))
      | .negative => none

theorem forward_exact (family : Family) (localRule : LocalRule)
    (build : ∀ {wires} (description : family.Description wires),
      localRule (family.source description) (family.target description))
    (view : ∀ {wires} {before after : Region wires},
      localRule before after →
        ∃ description : family.Description wires,
          before = family.source description ∧
            after = family.target description)
    (source target : OpenDiagram boundary) :
    (∃ (index : Index family source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Contextual localRule source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | direct description occurrence =>
        cases polarity : occurrence.context.polarity with
        | positive =>
            simp only [runForward, polarity, validateBody] at computed
            split at computed
            next canonical =>
              split at computed
              next twoEnded =>
                simp only [Option.some.injEq] at computed
                subst output
                refine ⟨_, _, _, occurrence, canonical, twoEnded,
                  outputIso.symm, ?_⟩
                simpa [polarity, atPolarity] using build description
              next => simp at computed
            next => simp at computed
        | negative => simp [runForward, polarity] at computed
    | reverse description occurrence =>
        cases polarity : occurrence.context.polarity with
        | positive => simp [runForward, polarity] at computed
        | negative =>
            simp only [runForward, polarity, validateBody] at computed
            split at computed
            next canonical =>
              split at computed
              next twoEnded =>
                simp only [Option.some.injEq] at computed
                subst output
                refine ⟨_, _, _, occurrence, canonical, twoEnded,
                  outputIso.symm, ?_⟩
                simpa [polarity, atPolarity, converse] using build description
              next => simp at computed
            next => simp at computed
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        have evidence : localRule before after := by
          simpa [polarity, atPolarity] using localEvidence
        obtain ⟨description, beforeEq, afterEq⟩ := view evidence
        subst before
        subst after
        refine ⟨.direct description occurrence,
          occurrence.interface.withBody
            (occurrence.context.fill (family.target description))
            canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
        simp only [runForward, polarity]
        exact validateBody_of_valid _ _ canonical twoEnded
    | negative =>
        have evidence : localRule after before := by
          simpa [polarity, atPolarity, converse] using localEvidence
        obtain ⟨description, afterEq, beforeEq⟩ := view evidence
        subst before
        subst after
        refine ⟨.reverse description occurrence,
          occurrence.interface.withBody
            (occurrence.context.fill (family.source description))
            canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
        simp only [runForward, polarity]
        exact validateBody_of_valid _ _ canonical twoEnded

theorem backward_exact (family : Family) (localRule : LocalRule)
    (build : ∀ {wires} (description : family.Description wires),
      localRule (family.source description) (family.target description))
    (view : ∀ {wires} {before after : Region wires},
      localRule before after →
        ∃ description : family.Description wires,
          before = family.source description ∧
            after = family.target description)
    (source target : OpenDiagram boundary) :
    (∃ (index : Index family source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Contextual localRule target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | direct description occurrence =>
        cases polarity : occurrence.context.polarity with
        | positive => simp [runBackward, polarity] at computed
        | negative =>
            simp only [runBackward, polarity, validateBody] at computed
            split at computed
            next canonical =>
              split at computed
              next twoEnded =>
                simp only [Option.some.injEq] at computed
                subst output
                let reverseOccurrence : Occurrence _ target := {
                  interface := occurrence.interface
                  context := occurrence.context
                  sourceCanonical := canonical
                  sourceExternalTwoEnded := twoEnded
                  host_iso := outputIso.symm
                }
                refine ⟨_, _, _, reverseOccurrence,
                  occurrence.sourceCanonical,
                  occurrence.sourceExternalTwoEnded,
                  occurrence.host_iso, ?_⟩
                simpa [reverseOccurrence, polarity, atPolarity, converse] using
                  build description
              next => simp at computed
            next => simp at computed
    | reverse description occurrence =>
        cases polarity : occurrence.context.polarity with
        | positive =>
            simp only [runBackward, polarity, validateBody] at computed
            split at computed
            next canonical =>
              split at computed
              next twoEnded =>
                simp only [Option.some.injEq] at computed
                subst output
                let reverseOccurrence : Occurrence _ target := {
                  interface := occurrence.interface
                  context := occurrence.context
                  sourceCanonical := canonical
                  sourceExternalTwoEnded := twoEnded
                  host_iso := outputIso.symm
                }
                refine ⟨_, _, _, reverseOccurrence,
                  occurrence.sourceCanonical,
                  occurrence.sourceExternalTwoEnded,
                  occurrence.host_iso, ?_⟩
                simpa [reverseOccurrence, polarity, atPolarity] using
                  build description
              next => simp at computed
            next => simp at computed
        | negative => simp [runBackward, polarity] at computed
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    let reverseOccurrence : Occurrence after source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := canonical
      sourceExternalTwoEnded := twoEnded
      host_iso := targetIso
    }
    cases polarity : occurrence.context.polarity with
    | positive =>
        have evidence : localRule before after := by
          simpa [polarity, atPolarity] using localEvidence
        obtain ⟨description, beforeEq, afterEq⟩ := view evidence
        subst before
        subst after
        refine ⟨.reverse description reverseOccurrence,
          occurrence.interface.withBody
            (occurrence.context.fill (family.source description))
            occurrence.sourceCanonical occurrence.sourceExternalTwoEnded,
          ?_, ⟨occurrence.host_iso.symm⟩⟩
        simp only [runBackward, reverseOccurrence, polarity]
        exact validateBody_of_valid _ _ occurrence.sourceCanonical
          occurrence.sourceExternalTwoEnded
    | negative =>
        have evidence : localRule after before := by
          simpa [polarity, atPolarity, converse] using localEvidence
        obtain ⟨description, afterEq, beforeEq⟩ := view evidence
        subst before
        subst after
        refine ⟨.direct description reverseOccurrence,
          occurrence.interface.withBody
            (occurrence.context.fill (family.target description))
            occurrence.sourceCanonical occurrence.sourceExternalTwoEnded,
          ?_, ⟨occurrence.host_iso.symm⟩⟩
        simp only [runBackward, reverseOccurrence, polarity]
        exact validateBody_of_valid _ _ occurrence.sourceCanonical
          occurrence.sourceExternalTwoEnded

end ComputedDirected

end VisualProof.Rule.WirePrimitive.Executable
