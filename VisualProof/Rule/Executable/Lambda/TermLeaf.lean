import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.Lambda.TermLeaf

namespace VisualProof.Rule.Lambda.TermLeaf

open Diagram
open Theory

private def family : WirePrimitive.Executable.Family where
  Description := Leaves.Description
  source := Leaves.Description.target
  target := Leaves.Description.source

private theorem build {wires : List Sig}
    (description : Leaves.Description wires) :
    Local description.target description.source :=
  .abstractTerm (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Leaves.Description wires,
      before = description.target ∧ after = description.source := by
  cases step with
  | abstractTerm step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

def abstractTerm (description : Leaves.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .direct description occurrence

def termLeaf (description : Leaves.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .reverse description occurrence

def backwardTermLeaf (description : Leaves.Description wires)
    (occurrence : Occurrence description.source source) :
    BackwardIndex source :=
  .reverse description occurrence

def backwardAbstractTerm (description : Leaves.Description wires)
    (occurrence : Occurrence description.target source) :
    BackwardIndex source :=
  .direct description occurrence

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
      VisualProof.Rule.Lambda.TermLeaf source target := by
  exact WirePrimitive.Executable.ComputedDirected.forward_exact family Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.TermLeaf target source := by
  exact WirePrimitive.Executable.ComputedDirected.backward_exact family Local
    build view source target

end VisualProof.Rule.Lambda.TermLeaf
