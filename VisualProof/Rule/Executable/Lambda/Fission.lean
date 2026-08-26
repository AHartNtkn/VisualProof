import VisualProof.Rule.Lambda.Fission

namespace VisualProof.Rule.Lambda.Fission

open Diagram
open Theory

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | split (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | split (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source

def replaySplit (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source :=
  .split canonicalSource description sourceIso

def fuse (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) : BackwardIndex source :=
  .split canonicalSource description sourceIso

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .split _ description _ => some description.target

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .split canonicalSource _ _ => some canonicalSource

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Fission source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | split canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .split canonicalSource description sourceIso outputIso
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.split canonicalSource description sourceIso,
      description.target, rfl, ⟨targetIso⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Fission target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | split canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .split canonicalSource description outputIso.symm sourceIso.symm
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.split canonicalSource description targetIso.symm,
      canonicalSource, rfl, ⟨sourceIso.symm⟩⟩

end VisualProof.Rule.Lambda.Fission

namespace VisualProof.Rule.Lambda.Fusion

open Diagram
open Theory

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | fuse (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | fuse (canonicalSource : OpenDiagram boundary)
      (description : OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source

def replayFuse (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) : ForwardIndex source :=
  .fuse canonicalSource description sourceIso

def split (description : OpenDescription canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) : BackwardIndex source :=
  .fuse canonicalSource description sourceIso

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .fuse _ description _ => some description.target

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .fuse canonicalSource _ _ => some canonicalSource

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Fusion source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | fuse canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .fuse canonicalSource description sourceIso outputIso
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.fuse canonicalSource description sourceIso,
      description.target, rfl, ⟨targetIso⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.Fusion target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | fuse canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .fuse canonicalSource description outputIso.symm sourceIso.symm
  · rintro ⟨canonicalSource, description, sourceIso, targetIso⟩
    exact ⟨.fuse canonicalSource description targetIso.symm,
      canonicalSource, rfl, ⟨sourceIso.symm⟩⟩

end VisualProof.Rule.Lambda.Fusion
