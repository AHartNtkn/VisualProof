import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Arity

namespace VisualProof.Rule.WirePrimitive.Arity

open Theory
open Diagram

private def family : Executable.Family where
  Description := Shift.Description
  source := Shift.Description.source
  target := Shift.Description.target

private theorem build {wires : List Sig}
    (description : Shift.Description wires) :
    Local description.source description.target :=
  .shift (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Shift.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | shift step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

def arityShift (description : Shift.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def arityUnshift (description : Shift.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .reverse description occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  Executable.ComputedSymmetric.run source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  Executable.ComputedSymmetric.run source

def compileForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) := runForward source

def compileBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) := runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.Arity source target := by
  simpa only [Rule.WirePrimitive.Arity] using
    (Executable.ComputedSymmetric.forward_exact family Local build view
      source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.Arity target source := by
  simpa only [Rule.WirePrimitive.Arity] using
    (Executable.ComputedSymmetric.backward_exact family Local build view
      source target)

theorem respectsTargetIso
    (step : Rule.WirePrimitive.Arity source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.Arity source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.Arity.iso (OpenDiagramIso.refl source) step
    targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.Arity target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.Arity target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.Arity.iso targetIso step
    (OpenDiagramIso.refl source)

end VisualProof.Rule.WirePrimitive.Arity
