import VisualProof.Rule.Erasure
import VisualProof.Rule.WireSever
import VisualProof.Rule.Iteration
import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Comprehension.Relation
import VisualProof.Rule.Vacuity
import VisualProof.Rule.Presentation
import VisualProof.Rule.Identification
import VisualProof.Rule.WirePrimitive

namespace VisualProof.Rule

open Diagram
open Theory

inductive Step {boundary : List Sig} :
    OpenDiagram boundary → OpenDiagram boundary → Prop
  | erasure : Erasure source target → Step source target
  | wireSever : WireSever source target → Step source target
  | iteration : Iteration source target → Step source target
  | doubleCut : DoubleCut source target → Step source target
  | comprehension : Comprehension source target → Step source target
  | vacuity : Vacuity source target → Step source target
  | presentation : Presentation source target → Step source target
  | identification : Identification source target → Step source target
  | cutShape : WirePrimitive.CutShape source target → Step source target
  | parallelShape : WirePrimitive.ParallelShape source target →
      Step source target
  | ends : WirePrimitive.Ends source target → Step source target
  | arity : WirePrimitive.Arity source target → Step source target
  | argumentPermutation : WirePrimitive.ArgumentPermutation source target →
      Step source target
  | argumentDuplicate : WirePrimitive.ArgumentDuplicate source target →
      Step source target
  | argumentProjection : WirePrimitive.ArgumentProjection source target →
      Step source target
  | formalApplication : WirePrimitive.FormalApplication source target →
      Step source target
  | identityLeaf : WirePrimitive.IdentityLeaf source target →
      Step source target

theorem Step.iso
    {boundary : List Sig}
    {source source' target target' : OpenDiagram boundary}
    (sourceIso : OpenDiagramIso source source')
    (step : Step source target)
    (targetIso : OpenDiagramIso target target') :
    Step source' target' := by
  cases step with
  | erasure step =>
      exact .erasure (Erasure.iso sourceIso step targetIso)
  | wireSever step =>
      exact .wireSever (WireSever.iso sourceIso step targetIso)
  | iteration step =>
      exact .iteration (Iteration.iso sourceIso step targetIso)
  | doubleCut step =>
      exact .doubleCut (DoubleCut.iso sourceIso step targetIso)
  | comprehension step =>
      exact .comprehension (Comprehension.iso sourceIso step targetIso)
  | vacuity step =>
      exact .vacuity (Vacuity.iso sourceIso step targetIso)
  | presentation step =>
      exact .presentation (Presentation.iso sourceIso step targetIso)
  | identification step =>
      exact .identification (Identification.iso sourceIso step targetIso)
  | cutShape step =>
      exact .cutShape (WirePrimitive.CutShape.iso sourceIso step targetIso)
  | parallelShape step =>
      exact .parallelShape
        (WirePrimitive.ParallelShape.iso sourceIso step targetIso)
  | ends step =>
      exact .ends (WirePrimitive.Ends.iso sourceIso step targetIso)
  | arity step =>
      exact .arity (WirePrimitive.Arity.iso sourceIso step targetIso)
  | argumentPermutation step =>
      exact .argumentPermutation
        (WirePrimitive.ArgumentPermutation.iso sourceIso step targetIso)
  | argumentDuplicate step =>
      exact .argumentDuplicate
        (WirePrimitive.ArgumentDuplicate.iso sourceIso step targetIso)
  | argumentProjection step =>
      exact .argumentProjection
        (WirePrimitive.ArgumentProjection.iso sourceIso step targetIso)
  | formalApplication step =>
      exact .formalApplication
        (WirePrimitive.FormalApplication.iso sourceIso step targetIso)
  | identityLeaf step =>
      exact .identityLeaf
        (WirePrimitive.IdentityLeaf.iso sourceIso step targetIso)

end VisualProof.Rule
