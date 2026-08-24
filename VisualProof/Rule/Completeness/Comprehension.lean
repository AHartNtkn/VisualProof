import VisualProof.Rule.Completeness.Comprehension.Complete

namespace VisualProof.Rule.Comprehension

open Diagram

/-- Every declarative comprehension step is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : Comprehension source target) :
    Relation.TransGen Step source target := by
  rcases step with ⟨wires, before, after, occurrence,
    targetCanonical, targetExternalTwoEnded, targetIso, localEvidence⟩
  cases polarityEq : occurrence.context.polarity with
  | positive =>
      rw [polarityEq] at localEvidence
      change Local before after at localEvidence
      cases localEvidence with
      | comprehend arguments localBefore localAfter pattern instantiates =>
          let continuation :=
            Completeness.Comprehension.Telescope.refl .positive
              occurrence.interface occurrence.context (region := after)
              targetCanonical
              targetExternalTwoEnded polarityEq
          let request : Completeness.Comprehension.Telescope.Request
              before after := {
            boundary := boundary
            source := source
            endpoint := after
            polarity := .positive
            occurrence := occurrence
            instantiatedCanonical := occurrence.sourceCanonical
            instantiatedExternalTwoEnded :=
              occurrence.sourceExternalTwoEnded
            pendingCanonical := targetCanonical
            pendingExternalTwoEnded := targetExternalTwoEnded
            endpointCanonical := targetCanonical
            endpointExternalTwoEnded := targetExternalTwoEnded
            continuation := continuation
          }
          have derived := Completeness.Comprehension.complete pattern
            instantiates request
          exact Completeness.transGen_iso (OpenDiagramIso.refl _) derived
            targetIso.symm
  | negative =>
      rw [polarityEq] at localEvidence
      change Local after before at localEvidence
      cases localEvidence with
      | comprehend arguments localBefore localAfter pattern instantiates =>
          let continuation :=
            Completeness.Comprehension.Telescope.refl .negative
              occurrence.interface occurrence.context (region := before)
              occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
              polarityEq
          let request : Completeness.Comprehension.Telescope.Request
              after before := {
            boundary := boundary
            source := source
            endpoint := before
            polarity := .negative
            occurrence := occurrence
            instantiatedCanonical := targetCanonical
            instantiatedExternalTwoEnded := targetExternalTwoEnded
            pendingCanonical := occurrence.sourceCanonical
            pendingExternalTwoEnded := occurrence.sourceExternalTwoEnded
            endpointCanonical := occurrence.sourceCanonical
            endpointExternalTwoEnded := occurrence.sourceExternalTwoEnded
            continuation := continuation
          }
          have derived := Completeness.Comprehension.complete pattern
            instantiates request
          exact Completeness.transGen_iso (OpenDiagramIso.refl _) derived
            targetIso.symm

end VisualProof.Rule.Comprehension
