import VisualProof.Diagram.Semantics.Context
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

theorem Contextual.sound
    {source target : OpenDiagram boundary}
    {«local» : LocalRule}
    (localSound :
      ∀ {wires : List Sig} {before after : Region wires},
        «local» before after →
        ∀ (model : Model) (env : Values model wires),
          denoteRegion model env before → denoteRegion model env after)
    (step : Contextual «local» source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  rcases step with ⟨wires, before, after, occurrence,
    targetCanonical, targetIso, localStep⟩
  intro model args sourceDenotes
  have filledSource :
      denoteOpen model
        (occurrence.interface.withBody
          (occurrence.context.fill before) occurrence.sourceCanonical) args :=
    (occurrence.host_iso.denoteOpen_iff model args).mp sourceDenotes
  have filledTarget :
      denoteOpen model
        (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical) args := by
    apply OpenDiagram.denote_body (diagram := occurrence.interface)
    intro env
    cases polarityEq : occurrence.context.polarity with
    | positive =>
        have evidence : «local» before after := by
          simpa [atPolarity, polarityEq] using localStep
        have transported := occurrence.context.denote_fill model before after
          (fun holeEnv => localSound evidence model holeEnv) env
        simpa [polarityEq] using transported
    | negative =>
        have evidence : «local» after before := by
          simpa [atPolarity, polarityEq, converse] using localStep
        have transported := occurrence.context.denote_fill model after before
          (fun holeEnv => localSound evidence model holeEnv) env
        simpa [polarityEq] using transported
    exact filledSource
  exact (targetIso.denoteOpen_iff model args).mpr filledTarget

end VisualProof.Rule
