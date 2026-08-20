import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Permutation

namespace VisualProof.Rule.WirePrimitive.ArgumentPermutation

open Theory
open Diagram

private def family : Executable.Family where
  Description := Permutes.Description
  source := Permutes.Description.source
  target := Permutes.Description.target

private theorem build {wires : List Sig}
    (description : Permutes.Description wires) :
    Local description.source description.target :=
  .permute (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Permutes.Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | permute step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedSymmetric.Index family source

/-- The sole parametric permutation executor. Applying it with the inverse
permutation supplies the inverse semantic operation. -/
def argumentPermute (description : Permutes.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

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
      Rule.WirePrimitive.ArgumentPermutation source target := by
  simpa only [Rule.WirePrimitive.ArgumentPermutation] using
    (Executable.ComputedSymmetric.forward_exact family Local build view
      source target)

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.ArgumentPermutation target source := by
  simpa only [Rule.WirePrimitive.ArgumentPermutation] using
    (Executable.ComputedSymmetric.backward_exact family Local build view
      source target)

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
