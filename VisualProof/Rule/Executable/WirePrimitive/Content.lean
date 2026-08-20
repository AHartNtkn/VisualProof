import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Content

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace CutShape

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.ForwardIndex Content.Cut.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.BackwardIndex Content.Cut.Local source

def cutWrap (step : Content.Cut.Wrap before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .direct (.wrap step) occurrence targetCanonical targetExternalTwoEnded

def cutAbsorb (step : Content.Cut.Wrap after before)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .reverse (.wrap step) occurrence targetCanonical targetExternalTwoEnded

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
      Rule.WirePrimitive.CutShape source target := by
  simpa only [Rule.WirePrimitive.CutShape] using
    (Executable.Symmetric.forward_exact Content.Cut.Local source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.CutShape target source := by
  simpa only [Rule.WirePrimitive.CutShape] using
    (Executable.Symmetric.backward_exact Content.Cut.Local source target)

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

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.ForwardIndex Content.Parallel.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.BackwardIndex Content.Parallel.Local source

def parallelSplit (step : Content.Parallel.Split before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .direct (.split step) occurrence targetCanonical targetExternalTwoEnded

def parallelFuse (step : Content.Parallel.Split after before)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .reverse (.split step) occurrence targetCanonical targetExternalTwoEnded

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
      Rule.WirePrimitive.ParallelShape source target := by
  simpa only [Rule.WirePrimitive.ParallelShape] using
    (Executable.Symmetric.forward_exact Content.Parallel.Local source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.ParallelShape target source := by
  simpa only [Rule.WirePrimitive.ParallelShape] using
    (Executable.Symmetric.backward_exact Content.Parallel.Local source target)

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

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.ForwardIndex Content.Ends.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.BackwardIndex Content.Ends.Local source

def endsSpawn (step : Content.Ends.Delete after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .positive (.spawn step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def endsDelete (step : Content.Ends.Delete before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .negative (.spawn step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardEndsDelete (step : Content.Ends.Delete before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .positive (.spawn step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardEndsSpawn (step : Content.Ends.Delete after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .negative (.spawn step) occurrence polarity targetCanonical
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
      Rule.WirePrimitive.Ends source target := by
  exact Executable.Directed.forward_exact Content.Ends.Local source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.Ends target source := by
  exact Executable.Directed.backward_exact Content.Ends.Local source target

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
