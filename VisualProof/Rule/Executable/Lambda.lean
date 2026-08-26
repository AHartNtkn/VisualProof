import VisualProof.Rule.Executable.Lambda.Spawn
import VisualProof.Rule.Executable.Lambda.TermLeaf
import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.Lambda

namespace VisualProof.Rule.Lambda.Conversion

open Diagram
open Theory

private def family : WirePrimitive.Executable.Family where
  Description := Description
  source := Description.source
  target := Description.target

private theorem build {wires : List Sig}
    (description : Description wires) :
    Local description.source description.target :=
  .convert description

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : Description wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | convert description => exact ⟨description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

def convert (description : Description wires)
    (occurrence : Occurrence description.source source) :
    ForwardIndex source :=
  .direct description occurrence

def reverseConvert (description : Description wires)
    (occurrence : Occurrence description.target source) :
    ForwardIndex source :=
  .reverse description occurrence

def backwardConvert (description : Description wires)
    (occurrence : Occurrence description.target source) :
    BackwardIndex source :=
  .reverse description occurrence

def backwardReverseConvert (description : Description wires)
    (occurrence : Occurrence description.source source) :
    BackwardIndex source :=
  .direct description occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Conversion source target := by
  exact WirePrimitive.Executable.ComputedDirected.forward_exact family Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Conversion target source := by
  exact WirePrimitive.Executable.ComputedDirected.backward_exact family Local
    build view source target

end VisualProof.Rule.Lambda.Conversion

namespace VisualProof.Rule.Lambda.FreeVariableIdentity

open Diagram
open Theory

private inductive ExecutableDescription (wires : List Sig) where
  | toIdentity (description : Description wires)
  | toTerm (description : Description wires)

private def ExecutableDescription.source :
    ExecutableDescription wires → Region wires
  | .toIdentity description => description.term
  | .toTerm description => description.identity

private def ExecutableDescription.target :
    ExecutableDescription wires → Region wires
  | .toIdentity description => description.identity
  | .toTerm description => description.term

private def family : WirePrimitive.Executable.Family where
  Description := ExecutableDescription
  source := ExecutableDescription.source
  target := ExecutableDescription.target

private theorem build {wires : List Sig}
    (description : ExecutableDescription wires) :
    Local description.source description.target := by
  cases description with
  | toIdentity description => exact .toIdentity description
  | toTerm description => exact .toTerm description

private theorem view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : ExecutableDescription wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | toIdentity description => exact ⟨.toIdentity description, rfl, rfl⟩
  | toTerm description => exact ⟨.toTerm description, rfl, rfl⟩

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.Index family source

def toIdentity (description : Description wires)
    (occurrence : Occurrence description.term source) : ForwardIndex source :=
  .direct (.toIdentity description) occurrence

/-- The ordering in `description` selects which binary identity incidence
becomes the term output and which becomes free slot zero. -/
def toTerm (description : Description wires)
    (occurrence : Occurrence description.identity source) : ForwardIndex source :=
  .direct (.toTerm description) occurrence

def reverseToIdentity (description : Description wires)
    (occurrence : Occurrence description.identity source) : ForwardIndex source :=
  .reverse (.toIdentity description) occurrence

def reverseToTerm (description : Description wires)
    (occurrence : Occurrence description.term source) : ForwardIndex source :=
  .reverse (.toTerm description) occurrence

def backwardToIdentity (description : Description wires)
    (occurrence : Occurrence description.identity source) :
    BackwardIndex source :=
  .reverse (.toIdentity description) occurrence

def backwardToTerm (description : Description wires)
    (occurrence : Occurrence description.term source) : BackwardIndex source :=
  .reverse (.toTerm description) occurrence

def backwardReverseToIdentity (description : Description wires)
    (occurrence : Occurrence description.term source) : BackwardIndex source :=
  .direct (.toIdentity description) occurrence

def backwardReverseToTerm (description : Description wires)
    (occurrence : Occurrence description.identity source) :
    BackwardIndex source :=
  .direct (.toTerm description) occurrence

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runForward source

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  WirePrimitive.Executable.ComputedDirected.runBackward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.FreeVariableIdentity source target := by
  exact WirePrimitive.Executable.ComputedDirected.forward_exact family Local
    build view source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.FreeVariableIdentity target source := by
  exact WirePrimitive.Executable.ComputedDirected.backward_exact family Local
    build view source target

end VisualProof.Rule.Lambda.FreeVariableIdentity
