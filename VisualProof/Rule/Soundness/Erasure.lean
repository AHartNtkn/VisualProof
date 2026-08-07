import VisualProof.Rule.Erasure
import VisualProof.Rule.Laws

namespace VisualProof.Rule

open Theory
open Diagram

theorem Contextual.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    {«local» : LocalRule}
    (localSound :
      ∀ {wires rels}
        {before after : Region wires rels},
        «local» before after →
        ∀ (model : Model)
          (env : Fin wires → model.Carrier)
          (relEnv : RelEnv model.Carrier rels),
          denoteRegion model env relEnv before →
          denoteRegion model env relEnv after)
    (step : Contextual «local» source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  rcases step with ⟨wires, rels, before, after, occurrence,
    targetIso, localStep⟩
  intro model args sourceDenotes
  have filledSource :
      denoteOpen model
        (occurrence.interface.withBody
          (occurrence.context.fill before)) args :=
    (occurrence.host_iso.denoteOpen_iff model args).mp sourceDenotes
  have filledTarget :
      denoteOpen model
        (occurrence.interface.withBody
          (occurrence.context.fill after)) args := by
    apply OpenDiagram.denote_body (diagram := occurrence.interface)
    intro env
    cases polarityEq : occurrence.context.polarity with
    | positive =>
        have evidence : «local» before after := by
          simpa [atPolarity, polarityEq] using localStep
        intro denotes
        have transported := occurrence.context.denote_fill model
          (localSound evidence model) env PUnit.unit
        rw [polarityEq] at transported
        exact transported denotes
    | negative =>
        have evidence : «local» after before := by
          simpa [atPolarity, polarityEq, converse] using localStep
        intro denotes
        have transported := occurrence.context.denote_fill model
          (localSound evidence model) env PUnit.unit
        rw [polarityEq] at transported
        exact transported denotes
    exact filledSource
  exact (targetIso.denoteOpen_iff model args).mpr filledTarget

namespace Erasure.Local

theorem sound
    {wires : Nat}
    {rels : RelCtx}
    {before after : Region wires rels}
    (step : Erasure.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before →
      denoteRegion model env relEnv after := by
  cases step
  intro model env relEnv denotes
  exact (Region.denote_conjoin model env relEnv _ _).mp denotes |>.1

end Erasure.Local

theorem Erasure.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Erasure source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args :=
  Contextual.sound Erasure.Local.sound step

end VisualProof.Rule
