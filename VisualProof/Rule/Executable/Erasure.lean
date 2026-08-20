import VisualProof.Rule.Erasure
import VisualProof.Rule.Executable.WirePrimitive.Uniform

namespace VisualProof.Rule.Erasure

open Theory
open Diagram

private def family : WirePrimitive.Executable.Family where
  Description := Description
  source := Description.source
  target := Description.target

private theorem build {wires : List Sig} (description : Description wires) :
    Local description.source description.target :=
  .erase description

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | erase description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Erasure source target := by
  exact WirePrimitive.Executable.ComputedDirected.forward_exact family Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Erasure target source := by
  exact WirePrimitive.Executable.ComputedDirected.backward_exact family Local
    build view source target

end VisualProof.Rule.Erasure
