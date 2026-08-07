import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Laws
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace DoubleCut.Local

theorem sound_iff
    {wires : Nat}
    {rels : RelCtx}
    {before after : Region wires rels}
    (step : DoubleCut.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before ↔
      denoteRegion model env relEnv after := by
  cases step with
  | introduce hostLocal hostItems body wireMap relationMap =>
      intro model env relEnv
      constructor
      · apply Region.denote_spliceAt_mono model env relEnv hostLocal hostItems
          body (DoubleCut.wrap body) wireMap relationMap
        intro patternEnv bodyDenotes
        exact (denote_doubleCutRegion body model patternEnv
          (RelEnv.pullback relationMap relEnv)).mpr bodyDenotes
      · apply Region.denote_spliceAt_mono model env relEnv hostLocal hostItems
          (DoubleCut.wrap body) body wireMap relationMap
        intro patternEnv wrappedDenotes
        exact (denote_doubleCutRegion body model patternEnv
          (RelEnv.pullback relationMap relEnv)).mp wrappedDenotes

end DoubleCut.Local

theorem DoubleCut.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : DoubleCut source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires rels before after localStep model env relEnv
  cases localStep with
  | inl forward =>
      exact (DoubleCut.Local.sound_iff forward model env relEnv).mp
  | inr backward =>
      exact (DoubleCut.Local.sound_iff backward model env relEnv).mpr

end VisualProof.Rule
