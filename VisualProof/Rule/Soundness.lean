import VisualProof.Rule.Step
import VisualProof.Rule.Soundness.Erasure
import VisualProof.Rule.Soundness.WireSever
import VisualProof.Rule.Soundness.Iteration
import VisualProof.Rule.Soundness.DoubleCut
import VisualProof.Rule.Soundness.Comprehension
import VisualProof.Rule.Soundness.Vacuity
import VisualProof.Rule.Soundness.Presentation
import VisualProof.Rule.Soundness.Identification

namespace VisualProof.Rule

open VisualProof.Theory
open VisualProof.Diagram

theorem Step.sound
    {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : Step source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  cases step with
  | erasure step =>
      exact Erasure.sound step
  | wireSever step =>
      exact WireSever.sound step
  | iteration step =>
      exact Iteration.sound step
  | doubleCut step =>
      exact DoubleCut.sound step
  | comprehension step =>
      exact Comprehension.sound step
  | vacuity step =>
      exact Vacuity.sound step
  | presentation step =>
      exact Presentation.sound step
  | identification step =>
      exact Identification.sound step

end VisualProof.Rule
