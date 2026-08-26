import VisualProof.Rule.Lambda.AnchoredWire

namespace VisualProof.Rule.Lambda.AnchoredWire

open Diagram
open Theory

/-- Exact forward replay data. Each description owns the selected nested
occurrence, endpoint partition, destination plan, and validated target. -/
inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | split (canonicalSource : OpenDiagram boundary)
      (description : Split.Description canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) :
      ForwardIndex source
  | contract (canonicalSource : OpenDiagram boundary)
      (description : Contract.Description canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource) :
      ForwardIndex source

/-- Exact backward replay data, indexed by the public target of the original
operation. -/
inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | split (canonicalSource : OpenDiagram boundary)
      (description : Split.Description canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source
  | contract (canonicalSource : OpenDiagram boundary)
      (description : Contract.Description canonicalSource)
      (sourceIso : OpenDiagramIso source description.target) :
      BackwardIndex source

def replaySplit (description : Split.Description canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) :
    ForwardIndex source :=
  .split canonicalSource description sourceIso

def replayContract (description : Contract.Description canonicalSource)
    (sourceIso : OpenDiagramIso source canonicalSource) :
    ForwardIndex source :=
  .contract canonicalSource description sourceIso

def reverseSplit (description : Split.Description canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) :
    BackwardIndex source :=
  .split canonicalSource description sourceIso

def reverseContract (description : Contract.Description canonicalSource)
    (sourceIso : OpenDiagramIso source description.target) :
    BackwardIndex source :=
  .contract canonicalSource description sourceIso

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .split _ description _ => some description.target
  | .contract _ description _ => some description.target

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .split canonicalSource _ _ => some canonicalSource
  | .contract canonicalSource _ _ => some canonicalSource

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.AnchoredWire source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | split canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .split canonicalSource description sourceIso outputIso
    | contract canonicalSource description sourceIso =>
        simp only [runForward, Option.some.injEq] at computed
        subst output
        exact .contract canonicalSource description sourceIso outputIso
  · intro step
    cases step with
    | split canonicalSource description sourceIso targetIso =>
        exact ⟨.split canonicalSource description sourceIso,
          description.target, rfl, ⟨targetIso⟩⟩
    | contract canonicalSource description sourceIso targetIso =>
        exact ⟨.contract canonicalSource description sourceIso,
          description.target, rfl, ⟨targetIso⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Lambda.AnchoredWire target source := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | split canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .split canonicalSource description outputIso.symm sourceIso.symm
    | contract canonicalSource description sourceIso =>
        simp only [runBackward, Option.some.injEq] at computed
        subst output
        exact .contract canonicalSource description outputIso.symm sourceIso.symm
  · intro step
    cases step with
    | split canonicalSource description sourceIso targetIso =>
        exact ⟨.split canonicalSource description targetIso.symm,
          canonicalSource, rfl, ⟨sourceIso.symm⟩⟩
    | contract canonicalSource description sourceIso targetIso =>
        exact ⟨.contract canonicalSource description targetIso.symm,
          canonicalSource, rfl, ⟨sourceIso.symm⟩⟩

end VisualProof.Rule.Lambda.AnchoredWire
