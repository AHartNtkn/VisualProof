import VisualProof.Diagram.Concrete.Subgraph.SelectionFixtures
import VisualProof.Diagram.Concrete.Subgraph.OccurrenceFixtures
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction

namespace VisualProof
namespace ConcreteSpliceExamples

open SelectionFixtures

def accepted {error value : Type} (result : Except error value) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

/-! The three durable partial-selection forms all enter through `checkSelection`. -/

example : accepted (checkSelection directInput) = true := by
  native_decide

example : accepted (checkSelection subtreeInput) = true := by
  native_decide

example : accepted (checkSelection explicitWireInput) = true := by
  native_decide

example :
    anchorNode ∈ direct.allNodes ∧ leftNode ∉ direct.allNodes := by
  native_decide

example :
    leftRegion ∈ subtree.allRegions ∧ rightRegion ∉ subtree.allRegions := by
  native_decide

example :
    anchorWire ∈ explicitWire.internalWires ∧
      anchorWire ∉ explicitWire.touchingWires := by
  native_decide

/-!
One boundary class represents the canonical one-stub extraction of the
touching wire. The wire may have several selected endpoints; the ordered seam
still names it exactly once.
-/

def oneStubRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .identity 0 .iota 2
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] } }
  boundary := [0]

theorem oneStubRaw_wellFormed : oneStubRaw.WellFormed [] := by
  constructor <;> native_decide

def oneStub : CheckedOpenDiagram [] :=
  ⟨oneStubRaw, oneStubRaw_wellFormed⟩

def oneStubInput : OccurrenceInput oneStub host where
  region := anchor
  regionMap := fun _ => anchor
  nodeMap := fun _ => anchorNode
  wireMap := fun _ => anchorWire

example : accepted (checkOccurrence oneStubInput) = true := by
  native_decide

def oneStubOccurrence : Occurrence oneStub host :=
  (checkOccurrence oneStubInput).toOption.get (by native_decide)

example :
    oneStubOccurrence.boundaryAttachments =
      oneStubOccurrence.toSelection.touchingWires := by
  native_decide

example :
    accepted
      (checkExtraction oneStubOccurrence.toSelection oneStubOccurrence) =
      true := by
  native_decide

/-! Exact occurrence matching preserves repeated ordered boundary aliases. -/

example :
    OccurrenceFixtures.mainOccurrence.boundaryAttachments =
      [OccurrenceFixtures.mainBoundaryWire,
        OccurrenceFixtures.mainBoundaryWire] := by
  native_decide

/-! Generic splice is exercised through both public checkers. -/

def oneStubAttachment? :
    Option (ConcreteSpliceAttachment host anchor oneStub) :=
  checkConcreteSpliceAttachment host anchor oneStub (fun _ => anchorWire)

example : oneStubAttachment?.isSome = true := by
  native_decide

def oneStubAttachment : ConcreteSpliceAttachment host anchor oneStub :=
  oneStubAttachment?.get (by native_decide)

example : accepted (splice oneStubAttachment) = true := by
  native_decide

/-!
Occurrence reconstruction uses only `remove`, the reconstruction attachment
checker, and its acceptance equation. No reconstruction premise or raw receipt
is supplied by the caller.
-/

def mainRemoved :
    RemovalResult OccurrenceFixtures.mainOccurrence :=
  (remove OccurrenceFixtures.mainOccurrence).toOption.get (by native_decide)

def mainReconstruction? :
    Option
      (ConcreteSpliceAttachment mainRemoved.complement mainRemoved.site
        OccurrenceFixtures.mainPattern) :=
  reconstructionAttachment? OccurrenceFixtures.mainOccurrence mainRemoved

example : mainReconstruction?.isSome = true := by
  native_decide

def mainReconstruction :
    ConcreteSpliceAttachment mainRemoved.complement mainRemoved.site
      OccurrenceFixtures.mainPattern :=
  mainReconstruction?.get (by native_decide)

theorem mainReconstruction_accepted :
    reconstructionAttachment? OccurrenceFixtures.mainOccurrence mainRemoved =
      some mainReconstruction := by
  exact Option.some_get (by native_decide) |>.symm

def mainReconstructionIso? :
    Option (ConcreteIso mainReconstruction.diagram
      OccurrenceFixtures.mainHost.val) :=
  Reconstruction.extract_splice_iso? OccurrenceFixtures.mainOccurrence
    mainRemoved mainReconstruction mainReconstruction_accepted

example : mainReconstructionIso?.isSome = true := by
  native_decide

def mainReconstructionIso :
    ConcreteIso mainReconstruction.diagram
      OccurrenceFixtures.mainHost.val :=
  mainReconstructionIso?.get (by native_decide)

end ConcreteSpliceExamples
end VisualProof
