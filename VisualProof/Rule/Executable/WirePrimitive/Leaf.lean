import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Leaf

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace FormalApplication

private def family : Executable.Family where
  Description := Leaf.Formal.Applies.Description
  source := Leaf.Formal.Applies.Description.target
  target := Leaf.Formal.Applies.Description.source

private theorem build {wires : List Sig}
    (description : Leaf.Formal.Applies.Description wires) :
    Leaf.Formal.Local description.target description.source :=
  .abstractFormal (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Leaf.Formal.Local before after) :
    ∃ description : Leaf.Formal.Applies.Description wires,
      before = description.target ∧ after = description.source := by
  cases step with
  | abstractFormal step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

def abstractFormal (description : Leaf.Formal.Applies.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .direct description occurrence

def applyFormal (description : Leaf.Formal.Applies.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .reverse description occurrence

def backwardApplyFormal (description : Leaf.Formal.Applies.Description wires)
    (occurrence : Occurrence description.source source) :
    BackwardIndex source :=
  .reverse description occurrence

def backwardAbstractFormal
    (description : Leaf.Formal.Applies.Description wires)
    (occurrence : Occurrence description.target source) :
    BackwardIndex source :=
  .direct description occurrence

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
      Rule.WirePrimitive.FormalApplication source target := by
  exact Executable.ComputedDirected.forward_exact family Leaf.Formal.Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.FormalApplication target source := by
  exact Executable.ComputedDirected.backward_exact family Leaf.Formal.Local
    build view source target

theorem respectsTargetIso
    (step : Rule.WirePrimitive.FormalApplication source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.FormalApplication source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.FormalApplication.iso
    (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.FormalApplication target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.FormalApplication target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.FormalApplication.iso targetIso step
    (OpenDiagramIso.refl source)

end FormalApplication

namespace IdentityLeaf

private def family : Executable.Family where
  Description := Leaf.Identity.Leaves.Description
  source := Leaf.Identity.Leaves.Description.target
  target := Leaf.Identity.Leaves.Description.source

private theorem build {wires : List Sig}
    (description : Leaf.Identity.Leaves.Description wires) :
    Leaf.Identity.Local description.target description.source :=
  .abstractIdentity (.mk description)

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Leaf.Identity.Local before after) :
    ∃ description : Leaf.Identity.Leaves.Description wires,
      before = description.target ∧ after = description.source := by
  cases step with
  | abstractIdentity step =>
      cases step with
      | mk description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.ComputedDirected.Index family source

def identityAbstract (description : Leaf.Identity.Leaves.Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .direct description occurrence

def identityLeaf (description : Leaf.Identity.Leaves.Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .reverse description occurrence

def backwardIdentityLeaf (description : Leaf.Identity.Leaves.Description wires)
    (occurrence : Occurrence description.source source) :
    BackwardIndex source :=
  .reverse description occurrence

def backwardIdentityAbstract
    (description : Leaf.Identity.Leaves.Description wires)
    (occurrence : Occurrence description.target source) :
    BackwardIndex source :=
  .direct description occurrence

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
      Rule.WirePrimitive.IdentityLeaf source target := by
  exact Executable.ComputedDirected.forward_exact family Leaf.Identity.Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WirePrimitive.IdentityLeaf target source := by
  exact Executable.ComputedDirected.backward_exact family Leaf.Identity.Local
    build view source target

theorem respectsTargetIso
    (step : Rule.WirePrimitive.IdentityLeaf source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.IdentityLeaf source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.IdentityLeaf.iso
    (OpenDiagramIso.refl source) step targetIso

theorem backward_respectsTargetIso
    (step : Rule.WirePrimitive.IdentityLeaf target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Rule.WirePrimitive.IdentityLeaf target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Rule.WirePrimitive.IdentityLeaf.iso targetIso step
    (OpenDiagramIso.refl source)

end IdentityLeaf

end VisualProof.Rule.WirePrimitive
