import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

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
  exact Region.denote_spliceAt_host model env relEnv _ _ _ _ _ denotes

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
