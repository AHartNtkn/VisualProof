import VisualProof.Rule.Step
import VisualProof.Rule.Soundness.Erasure
import VisualProof.Rule.Soundness.WireSever
import VisualProof.Rule.Soundness.Iteration
import VisualProof.Rule.Soundness.DoubleCut
import VisualProof.Rule.Soundness.Comprehension
import VisualProof.Rule.Soundness.Vacuity
import VisualProof.Rule.Soundness.Presentation
import VisualProof.Rule.Soundness.Identification
import VisualProof.Rule.Soundness.WirePrimitive

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
  | cutShape step =>
      exact WirePrimitive.CutShape.sound step
  | parallelShape step =>
      exact WirePrimitive.ParallelShape.sound step
  | ends step =>
      exact WirePrimitive.Ends.sound step
  | arity step =>
      exact WirePrimitive.Arity.sound step
  | argumentPermutation step =>
      exact WirePrimitive.ArgumentPermutation.sound step
  | argumentDuplicate step =>
      exact WirePrimitive.ArgumentDuplicate.sound step
  | argumentProjection step =>
      exact WirePrimitive.ArgumentProjection.sound step
  | formalApplication step =>
      exact WirePrimitive.FormalApplication.sound step
  | identityLeaf step =>
      exact WirePrimitive.IdentityLeaf.sound step

end VisualProof.Rule
