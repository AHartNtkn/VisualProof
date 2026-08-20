import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Executable.WirePrimitive.Uniform

namespace VisualProof.Rule.DoubleCut

open Theory
open Diagram

private def family : WirePrimitive.Executable.Family where
  Description := Description
  source := Description.source
  target := Description.target

private theorem build {wires : List Sig} (description : Description wires) :
    Local description.source description.target :=
  .introduce description

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | introduce description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  ForwardIndex source

def introduce (description : Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def eliminate (description : Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .reverse description occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedSymmetric.run source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.DoubleCut source target := by
  simpa only [Rule.DoubleCut] using
    (WirePrimitive.Executable.ComputedSymmetric.forward_exact family Local
      build view source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.DoubleCut target source := by
  simpa only [Rule.DoubleCut] using
    (WirePrimitive.Executable.ComputedSymmetric.backward_exact family Local
      build view source target)

end VisualProof.Rule.DoubleCut
