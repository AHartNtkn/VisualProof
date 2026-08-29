import VisualProof.Rule.Lambda.HeadStrip

namespace VisualProof.Rule.Lambda.HeadStrip

open Diagram
open Theory

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | strip (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | strip (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source

def replayStrip (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source :=
  .strip canonicalSource description sourceIso

def restore (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) :
    BackwardIndex source :=
  .strip canonicalSource description sourceIso

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .strip _ description _ => some description.target

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .strip canonicalSource _ _ => some canonicalSource

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.HeadStrip source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | strip canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .strip canonicalSource description sourceIso outputIso
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.strip canonicalSource description sourceIso,
      description.target, rfl, ⟨targetIso⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.HeadStrip target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | strip canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .strip canonicalSource description outputIso.symm sourceIso.symm
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.strip canonicalSource description targetIso.symm,
      canonicalSource, rfl, ⟨sourceIso.symm⟩⟩

end VisualProof.Rule.Lambda.HeadStrip
