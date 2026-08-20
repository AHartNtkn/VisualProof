import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Permutation

namespace VisualProof.Rule.WirePrimitive.ArgumentPermutation

open Theory
open Diagram

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.ForwardIndex Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Symmetric.BackwardIndex Local source

/-- The sole parametric permutation executor. Applying it with the inverse
permutation supplies the inverse semantic operation. -/
def argumentPermute (step : Permutes before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .direct (.permute step) occurrence targetCanonical targetExternalTwoEnded

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
      Rule.WirePrimitive.ArgumentPermutation source target := by
  simpa only [Rule.WirePrimitive.ArgumentPermutation] using
    (Executable.Symmetric.forward_exact Local source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.ArgumentPermutation target source := by
  simpa only [Rule.WirePrimitive.ArgumentPermutation] using
    (Executable.Symmetric.backward_exact Local source target)

theorem respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentPermutation source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentPermutation source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentPermutation.iso
    (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.ArgumentPermutation target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.ArgumentPermutation target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.ArgumentPermutation.iso targetIso step
    (OpenDiagramIso.refl source)

end VisualProof.Rule.WirePrimitive.ArgumentPermutation
