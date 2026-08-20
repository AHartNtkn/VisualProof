import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Arity

namespace VisualProof.Rule.WirePrimitive.Arity

open Theory
open Diagram

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.ForwardIndex Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.BackwardIndex Local source

def arityShift (step : Shift before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .direct (.shift step) occurrence targetCanonical targetExternalTwoEnded

def arityUnshift (step : Shift after before)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .reverse (.shift step) occurrence targetCanonical targetExternalTwoEnded

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary :=
  Executable.Symmetric.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  Executable.Symmetric.runBackward source

def compileForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary := runForward source

def compileBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary := runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.WirePrimitive.Arity source target := by
  simpa only [Rule.WirePrimitive.Arity] using
    (Executable.Symmetric.forward_exact Local source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.Arity target source := by
  simpa only [Rule.WirePrimitive.Arity] using
    (Executable.Symmetric.backward_exact Local source target)

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
