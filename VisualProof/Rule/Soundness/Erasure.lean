import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure.Local

theorem sound
    {before after : Region wires}
    (step : Erasure.Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | erase description =>
      intro model env sourceDenotes
      rw [Erasure.Description.source, Region.denote_spliceAt] at sourceDenotes
      rw [Erasure.Description.target, denoteRegion_mk]
      rcases sourceDenotes with ⟨hostEnv, hostDenotes, _⟩
      exact ⟨hostEnv, hostDenotes⟩

end Erasure.Local

theorem Erasure.sound
    {source target : OpenDiagram boundary}
    (step : Erasure source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound Erasure.Local.sound step

end VisualProof.Rule
