import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace UncappedErasure.Local

theorem sound
    {before after : Region wires}
    (step : UncappedErasure.Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | erase description =>
      intro model env sourceDenotes
      rw [UncappedErasure.Description.source, Region.denote_spliceAt] at sourceDenotes
      rw [UncappedErasure.Description.target, denoteRegion_mk]
      rcases sourceDenotes with ⟨hostEnv, hostDenotes, _⟩
      exact ⟨hostEnv, hostDenotes⟩

end UncappedErasure.Local

theorem UncappedErasure.sound
    {source target : OpenDiagram boundary}
    (step : UncappedErasure source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound UncappedErasure.Local.sound step

end VisualProof.Rule
