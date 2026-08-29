import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.Lambda.Spawn

namespace VisualProof.Rule.Lambda.Spawn

open Diagram
open Theory

private def family : WirePrimitive.Executable.Family where
  Description := Description
  source := Description.source
  target := Description.target

private theorem build {context : List Sig} (description : Description context) :
    Local description.source description.target :=
  .spawn description

private theorem view {context : List Sig} {before after : Region context}
    (step : Local before after) :
    ∃ description : Description context,
      before = description.source ∧ after = description.target := by
  cases step with
  | spawn description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  ForwardIndex source

def spawn (description : Description context)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def remove (description : Description context)
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
      VisualProof.Rule.Lambda.Spawn source target := by
  simpa only [VisualProof.Rule.Lambda.Spawn] using
    (WirePrimitive.Executable.ComputedSymmetric.forward_exact family Local
      build view source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Spawn target source := by
  simpa only [VisualProof.Rule.Lambda.Spawn] using
    (WirePrimitive.Executable.ComputedSymmetric.backward_exact family Local
      build view source target)

end VisualProof.Rule.Lambda.Spawn
