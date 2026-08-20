import VisualProof.Rule.Executable.WirePrimitive.Uniform
import VisualProof.Rule.WirePrimitive.Leaf

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace FormalApplication

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.ForwardIndex Leaf.Formal.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.BackwardIndex Leaf.Formal.Local source

def abstractFormal (step : Leaf.Formal.Applies after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .positive (.abstractFormal step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def applyFormal (step : Leaf.Formal.Applies before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .negative (.abstractFormal step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardApplyFormal (step : Leaf.Formal.Applies before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .positive (.abstractFormal step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardAbstractFormal (step : Leaf.Formal.Applies after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .negative (.abstractFormal step) occurrence polarity targetCanonical
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
      Rule.WirePrimitive.FormalApplication source target := by
  exact Executable.Directed.forward_exact Leaf.Formal.Local source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.FormalApplication target source := by
  exact Executable.Directed.backward_exact Leaf.Formal.Local source target

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

abbrev ForwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.ForwardIndex Leaf.Identity.Local source

abbrev BackwardIndex {boundary : List Sig} (source : OpenDiagram boundary) :=
  Executable.Directed.BackwardIndex Leaf.Identity.Local source

def identityAbstract (step : Leaf.Identity.Leaves after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .positive (.abstractIdentity step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def identityLeaf (step : Leaf.Identity.Leaves before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    ForwardIndex source :=
  .negative (.abstractIdentity step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardIdentityLeaf (step : Leaf.Identity.Leaves before after)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .positive)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .positive (.abstractIdentity step) occurrence polarity targetCanonical
    targetExternalTwoEnded

def backwardIdentityAbstract (step : Leaf.Identity.Leaves after before)
    (occurrence : Occurrence before source)
    (polarity : occurrence.context.polarity = .negative)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) :
    BackwardIndex source :=
  .negative (.abstractIdentity step) occurrence polarity targetCanonical
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
      Rule.WirePrimitive.IdentityLeaf source target := by
  exact Executable.Directed.forward_exact Leaf.Identity.Local source target

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.WirePrimitive.IdentityLeaf target source := by
  exact Executable.Directed.backward_exact Leaf.Identity.Local source target

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
