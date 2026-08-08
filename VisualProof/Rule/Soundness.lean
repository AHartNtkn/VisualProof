import VisualProof.Rule.Step
import VisualProof.Rule.Soundness.Erasure
import VisualProof.Rule.Soundness.WireSever
import VisualProof.Rule.Soundness.Iteration
import VisualProof.Rule.Soundness.DoubleCut
import VisualProof.Rule.Soundness.Comprehension
import VisualProof.Rule.Soundness.Vacuity

namespace VisualProof.Rule

open VisualProof.Theory
open VisualProof.Diagram

theorem Step.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Step source target) :
    ∀ (model : Model) (args : Fin arity → model.Carrier),
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
  | vacuity step =>
      exact Vacuity.sound step

end VisualProof.Rule
