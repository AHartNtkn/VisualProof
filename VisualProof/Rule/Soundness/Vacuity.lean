import VisualProof.Rule.Vacuity
import VisualProof.Rule.Laws
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Vacuity.Local

theorem sound_iff
    {wires : Nat}
    {rels : RelCtx}
    {before after : Region wires rels}
    (step : Vacuity.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before ↔
      denoteRegion model env relEnv after := by
  cases step with
  | introduce arity hostLocal hostItems body wireMap relationMap =>
      intro model env relEnv
      constructor
      · apply Region.denote_spliceAt_mono model env relEnv hostLocal hostItems
          body (Vacuity.wrap arity body) wireMap relationMap
        intro patternEnv bodyDenotes
        exact (denote_vacuousBubbleRegion arity body model patternEnv
          (RelEnv.pullback relationMap relEnv)).mpr bodyDenotes
      · apply Region.denote_spliceAt_mono model env relEnv hostLocal hostItems
          (Vacuity.wrap arity body) body wireMap relationMap
        intro patternEnv wrappedDenotes
        exact (denote_vacuousBubbleRegion arity body model patternEnv
          (RelEnv.pullback relationMap relEnv)).mp wrappedDenotes

end Vacuity.Local

theorem Vacuity.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Vacuity source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires rels before after localStep model env relEnv
  cases localStep with
  | inl forward =>
      exact (Vacuity.Local.sound_iff forward model env relEnv).mp
  | inr backward =>
      exact (Vacuity.Local.sound_iff backward model env relEnv).mpr

end VisualProof.Rule
