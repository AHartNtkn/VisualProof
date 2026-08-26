import VisualProof.Rule.Lambda.Congruence

namespace VisualProof.Rule.Lambda.Congruence

open Diagram
open Theory

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | join (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | join (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source

def replayJoin (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source :=
  .join canonicalSource description sourceIso

def separate (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) :
    BackwardIndex source :=
  .join canonicalSource description sourceIso

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .join _ description _ => some description.target

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .join canonicalSource _ _ => some canonicalSource

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Congruence source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | join canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .join canonicalSource description sourceIso outputIso
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.join canonicalSource description sourceIso,
      description.target, rfl, ⟨targetIso⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Congruence target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | join canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .join canonicalSource description outputIso.symm sourceIso.symm
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.join canonicalSource description targetIso.symm,
      canonicalSource, rfl, ⟨sourceIso.symm⟩⟩

end VisualProof.Rule.Lambda.Congruence
