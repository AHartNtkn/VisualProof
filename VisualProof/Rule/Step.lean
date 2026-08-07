import VisualProof.Rule.Erasure
import VisualProof.Rule.WireSever
import VisualProof.Rule.Iteration
import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Comprehension.Relation
import VisualProof.Rule.Vacuity

namespace VisualProof.Rule

open Diagram

inductive Step : OpenDiagram arity → OpenDiagram arity → Prop
  | erasure : Erasure source target → Step source target
  | wireSever : WireSever source target → Step source target
  | iteration : Iteration source target → Step source target
  | doubleCut : DoubleCut source target → Step source target
  | comprehension : Comprehension source target → Step source target
  | vacuity : Vacuity source target → Step source target

theorem Step.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
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

end VisualProof.Rule
