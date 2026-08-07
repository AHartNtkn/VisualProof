import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Laws
import VisualProof.Rule.Soundness.Erasure

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
  cases step
  intro model env relEnv
  exact (denote_doubleCutRegion _ model env relEnv).symm

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
