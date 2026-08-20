import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Argument

namespace VisualProof.Rule.WirePrimitive.ArgumentDuplicate

open Theory
open Diagram

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.ForwardIndex Argument.Duplicate.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.BackwardIndex Argument.Duplicate.Local source

def argumentDuplicate (step : Argument.Duplicate.Duplicates before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .direct (.duplicate step) occurrence targetCanonical targetExternalTwoEnded

def argumentContract (step : Argument.Duplicate.Duplicates after before)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .reverse (.duplicate step) occurrence targetCanonical targetExternalTwoEnded

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
      Rule.WirePrimitive.ArgumentDuplicate source target := by
  simpa only [Rule.WirePrimitive.ArgumentDuplicate] using
    (Executable.Symmetric.forward_exact Argument.Duplicate.Local source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.ArgumentDuplicate target source := by
  simpa only [Rule.WirePrimitive.ArgumentDuplicate] using
    (Executable.Symmetric.backward_exact Argument.Duplicate.Local source target)

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
