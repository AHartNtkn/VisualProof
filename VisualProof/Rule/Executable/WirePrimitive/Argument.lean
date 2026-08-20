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

namespace VisualProof.Rule.WirePrimitive.ArgumentProjection

open Theory
open Diagram

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.ForwardIndex Argument.Projection.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.BackwardIndex Argument.Projection.Local source

def argumentExtend (step : Argument.Projection.Drops after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .positive (.extend step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def argumentDrop (step : Argument.Projection.Drops before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .negative (.extend step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def uniformArgumentDrop
    (step : Argument.Projection.UniformDrops before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source := by
  cases polarity : occurrence.context.polarity with
  | positive =>
      exact .positive (.uniformDrop step) occurrence polarity targetCanonical
        targetExternalTwoEnded
  | negative =>
      exact .negative (.uniformExtend step) occurrence polarity targetCanonical
        targetExternalTwoEnded

def uniformArgumentExtend
    (step : Argument.Projection.UniformDrops after before)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source := by
  cases polarity : occurrence.context.polarity with
  | positive =>
      exact .positive (.uniformExtend step) occurrence polarity targetCanonical
        targetExternalTwoEnded
  | negative =>
      exact .negative (.uniformDrop step) occurrence polarity targetCanonical
        targetExternalTwoEnded

def backwardArgumentDrop (step : Argument.Projection.Drops before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .positive (.extend step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardArgumentExtend (step : Argument.Projection.Drops after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .negative (.extend step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary :=
  Executable.Directed.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  Executable.Directed.runBackward source

def compileForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary := runForward source

def compileBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary := runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.WirePrimitive.ArgumentProjection source target := by
  exact Executable.Directed.forward_exact Argument.Projection.Local source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.ArgumentProjection target source := by
  exact Executable.Directed.backward_exact Argument.Projection.Local source target

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
