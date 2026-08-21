import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Content

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace CutShape

private def family : Executable.Family where
  Description := Content.Cut.Wrap.Description
  source := Content.Cut.Wrap.Description.source
  target := Content.Cut.Wrap.Description.target

private theorem build {wires : List Sig}
    (description : Content.Cut.Wrap.Description wires) :
    Content.Cut.Local description.source description.target :=
  .wrap (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Content.Cut.Local before after) :
    ∃ description : Content.Cut.Wrap.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | wrap step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  ForwardIndex source

def cutWrap (description : Content.Cut.Wrap.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def cutAbsorb (description : Content.Cut.Wrap.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .reverse description occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  Executable.ComputedSymmetric.run source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) := runForward source

def compileForward (source : OpenDiagram boundary) := runForward source
def compileBackward (source : OpenDiagram boundary) := runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.CutShape source target := by
  simpa only [Rule.WirePrimitive.CutShape] using
    (Executable.ComputedSymmetric.forward_exact family Content.Cut.Local
      build view source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.CutShape target source := by
  simpa only [Rule.WirePrimitive.CutShape] using
    (Executable.ComputedSymmetric.backward_exact family Content.Cut.Local
      build view source target)

theorem respectsTargetIso
    (step : Rule.WirePrimitive.CutShape source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.CutShape source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.CutShape.iso (OpenDiagramIso.refl source) step
    targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.CutShape target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.CutShape target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.CutShape.iso targetIso step
    (OpenDiagramIso.refl source)

end CutShape

namespace ParallelShape

private def family : Executable.Family where
  Description := Content.Parallel.Split.Description
  source := Content.Parallel.Split.Description.source
  target := Content.Parallel.Split.Description.target

private theorem build {wires : List Sig}
    (description : Content.Parallel.Split.Description wires) :
    Content.Parallel.Local description.source description.target :=
  .split (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Content.Parallel.Local before after) :
    ∃ description : Content.Parallel.Split.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | split step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

def parallelSplit (description : Content.Parallel.Split.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def parallelFuse (description : Content.Parallel.Split.Description wires)
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
      Rule.WirePrimitive.ParallelShape source target := by
  simpa only [Rule.WirePrimitive.ParallelShape] using
    (Executable.ComputedSymmetric.forward_exact family Content.Parallel.Local
      build view source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.ParallelShape target source := by
  simpa only [Rule.WirePrimitive.ParallelShape] using
    (Executable.ComputedSymmetric.backward_exact family Content.Parallel.Local
      build view source target)

theorem respectsTargetIso
    (step : Rule.WirePrimitive.ParallelShape source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ParallelShape source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ParallelShape.iso (OpenDiagramIso.refl source) step
    targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.ParallelShape target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ParallelShape target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ParallelShape.iso targetIso step
    (OpenDiagramIso.refl source)

end ParallelShape

namespace Ends

private inductive Description (wires : List Sig) where
  | spawn (description : Content.Ends.Delete.Description wires)
  | absorb (description : Content.Ends.Absorb.Description wires)

private def Description.source : Description wires → Region wires
  | .spawn description => description.target
  | .absorb description => description.source

private def Description.target : Description wires → Region wires
  | .spawn description => description.source
  | .absorb description => description.target

private def family : Executable.Family where
  Description := Description
  source := Description.source
  target := Description.target

private theorem build {wires : List Sig}
    (description : Description wires) :
    Content.Ends.Local description.source description.target := by
  cases description with
  | spawn description => exact .spawn (.mk description)
  | absorb description => exact .absorb (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Content.Ends.Local before after) :
    ∃ description : Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | spawn step =>
      cases step with
      | mk description => exact ⟨.spawn description, rfl, rfl⟩
  | absorb step =>
      cases step with
      | mk description => exact ⟨.absorb description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

def endsSpawn (description : Content.Ends.Delete.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .direct (.spawn description) occurrence

def endsDelete (description : Content.Ends.Delete.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .reverse (.spawn description) occurrence

def endsAbsorb (description : Content.Ends.Delete.Description wires)
    (occurrence : Occurrence description.source source) :
    Option (ForwardIndex source) :=
  match Content.Ends.Absorb.Description.build description with
  | some ⟨absorb, deletionEq⟩ => by
      subst description
      exact some (.direct (.absorb absorb) occurrence)
  | none => none

def endsInsert (description : Content.Ends.Delete.Description wires)
    (occurrence : Occurrence description.target source) :
    Option (ForwardIndex source) :=
  match Content.Ends.Absorb.Description.build description with
  | some ⟨absorb, deletionEq⟩ => by
      subst description
      exact some (.reverse (.absorb absorb) occurrence)
  | none => none

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
      Rule.WirePrimitive.Ends source target := by
  exact Executable.ComputedDirected.forward_exact family Content.Ends.Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.Ends target source := by
  exact Executable.ComputedDirected.backward_exact family Content.Ends.Local
    build view source target

theorem respectsTargetIso
    (step : Rule.WirePrimitive.Ends source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.Ends source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.Ends.iso (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.Ends target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.Ends target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.Ends.iso targetIso step (OpenDiagramIso.refl source)

end Ends

end VisualProof.Rule.WirePrimitive
