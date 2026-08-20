import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Argument

namespace VisualProof.Rule.WirePrimitive.ArgumentDuplicate

open Theory
open Diagram

private def family : Executable.Family where
  Description := Argument.Duplicate.Duplicates.Description
  source := Argument.Duplicate.Duplicates.Description.source
  target := Argument.Duplicate.Duplicates.Description.target

private theorem build {wires : List Sig}
    (description : Argument.Duplicate.Duplicates.Description wires) :
    Argument.Duplicate.Local description.source description.target :=
  .duplicate (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Argument.Duplicate.Local before after) :
    ∃ description : Argument.Duplicate.Duplicates.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | duplicate step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

def argumentDuplicate
    (description : Argument.Duplicate.Duplicates.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def argumentContract
    (description : Argument.Duplicate.Duplicates.Description wires)
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
      Rule.WirePrimitive.ArgumentDuplicate source target := by
  simpa only [Rule.WirePrimitive.ArgumentDuplicate] using
    (Executable.ComputedSymmetric.forward_exact family
      Argument.Duplicate.Local build view source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.ArgumentDuplicate target source := by
  simpa only [Rule.WirePrimitive.ArgumentDuplicate] using
    (Executable.ComputedSymmetric.backward_exact family
      Argument.Duplicate.Local build view source target)

theorem respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentDuplicate source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentDuplicate source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentDuplicate.iso
    (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentDuplicate target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentDuplicate target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentDuplicate.iso targetIso step
    (OpenDiagramIso.refl source)

end VisualProof.Rule.WirePrimitive.ArgumentDuplicate

namespace VisualProof.Rule.WirePrimitive.ArgumentProjection

open Theory
open Diagram

private def family : Executable.Family where
  Description := Argument.Projection.Local.Description
  source := Argument.Projection.Local.Description.source
  target := Argument.Projection.Local.Description.target

private theorem build {wires : List Sig}
    (description : Argument.Projection.Local.Description wires) :
    Argument.Projection.Local description.source description.target :=
  .mk description

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Argument.Projection.Local before after) :
    ∃ description : Argument.Projection.Local.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

def argumentExtend
    (description : Argument.Projection.Drops.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .direct (.extend description) occurrence

def argumentDrop
    (description : Argument.Projection.Drops.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .reverse (.extend description) occurrence

def uniformArgumentDrop
    (description : Argument.Projection.UniformDrops.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source := by
  cases occurrence.context.polarity with
  | positive =>
      exact .direct (.uniformDrop description) occurrence
  | negative =>
      exact .reverse (.uniformExtend description) occurrence

def uniformArgumentExtend
    (description : Argument.Projection.UniformDrops.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source := by
  cases occurrence.context.polarity with
  | positive =>
      exact .direct (.uniformExtend description) occurrence
  | negative =>
      exact .reverse (.uniformDrop description) occurrence

def backwardArgumentDrop
    (description : Argument.Projection.Drops.Description wires)
    (occurrence : Occurrence description.source source) :
    BackwardIndex source :=
  .reverse (.extend description) occurrence

def backwardArgumentExtend
    (description : Argument.Projection.Drops.Description wires)
    (occurrence : Occurrence description.target source) :
    BackwardIndex source :=
  .direct (.extend description) occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  Executable.ComputedDirected.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  Executable.ComputedDirected.runBackward source

def compileForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) := runForward source

def compileBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) := runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.ArgumentProjection source target := by
  exact Executable.ComputedDirected.forward_exact family
    Argument.Projection.Local build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.ArgumentProjection target source := by
  exact Executable.ComputedDirected.backward_exact family
    Argument.Projection.Local build view source target

theorem respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentProjection source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentProjection source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentProjection.iso
    (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentProjection target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentProjection target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentProjection.iso targetIso step
    (OpenDiagramIso.refl source)

end VisualProof.Rule.WirePrimitive.ArgumentProjection
