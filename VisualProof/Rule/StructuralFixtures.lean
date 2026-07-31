import VisualProof.Rule.Structural
import VisualProof.Diagram.Concrete.Subgraph.SpliceExamples
import VisualProof.Rule.IdentityFixtures

namespace VisualProof
namespace StructuralFixtures

open ConcreteSpliceExamples SelectionFixtures StructuralCore

private def structuralError? {value : Type}
    (result : Except StructuralError value) : Option StructuralError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def insertionInput :
    StructuralInsertionInput host oneStub where
  orientation := .forward
  site := leftRegion
  target := fun _ => anchorWire

private def backwardPositiveInput :
    StructuralInsertionInput host oneStub where
  orientation := .backward
  site := anchor
  target := fun _ => anchorWire

private def forwardPositiveInput :
    StructuralInsertionInput host oneStub where
  orientation := .forward
  site := anchor
  target := fun _ => anchorWire

private def backwardNegativeInput :
    StructuralInsertionInput host oneStub where
  orientation := .backward
  site := leftRegion
  target := fun _ => anchorWire

private def erasureInput (orientation : Orientation) :
    StructuralErasureInput host oneStub where
  orientation := orientation
  site := anchor
  target := fun _ => anchorWire

private def negativeErasureInput :
    StructuralErasureInput host oneStub where
  orientation := .forward
  site := leftRegion
  target := fun _ => anchorWire

private def backwardNegativeErasureInput :
    StructuralErasureInput host oneStub where
  orientation := .backward
  site := leftRegion
  target := fun _ => anchorWire

/-- The public rule surface is concrete and checker-owned. -/
example :
    (checkStructuralInsertion insertionInput).toOption.isSome = true := by
  native_decide

example :
    (checkStructuralInsertion backwardPositiveInput).toOption.isSome = true := by
  native_decide

example :
    structuralError? (checkStructuralInsertion forwardPositiveInput) =
      some .forwardInsertionRequiresNegative := by
  native_decide

example :
    structuralError? (checkStructuralInsertion backwardNegativeInput) =
      some .backwardInsertionRequiresPositive := by
  native_decide

example :
    (checkStructuralErasure (erasureInput .forward)).toOption.isSome =
      true := by
  native_decide

example :
    (checkStructuralErasure backwardNegativeErasureInput).toOption.isSome =
      true := by
  native_decide

example :
    structuralError? (checkStructuralErasure (erasureInput .backward)) =
      some .backwardErasureRequiresNegative := by
  native_decide

example :
    structuralError? (checkStructuralErasure negativeErasureInput) =
      some .forwardErasureRequiresPositive := by
  native_decide

/-- Soundness is stated directly between checked concrete diagrams. -/
example (checked : StructuralInsertionReceipt insertionInput)
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) :=
  checked.sound pre definitionEnv

/-- Backward erasure in a negative region has the flipped semantic direction. -/
example (checked : StructuralErasureReceipt backwardNegativeErasureInput)
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    Directed .backward
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) :=
  checked.sound pre definitionEnv

private def doubledRaw : ConcreteDiagram 0 where
  regionCount := 5
  nodeCount := 3
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 4
    | ⟨2, _⟩ => .cut 4
    | ⟨3, _⟩ => .cut 0
    | ⟨4, _⟩ => .cut 3
  nodes
    | ⟨0, _⟩ => .identity 4 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }

private theorem doubledRaw_wellFormed : doubledRaw.WellFormed [] := by
  native_decide

private def doubled : CheckedDiagram [] :=
  ⟨doubledRaw, doubledRaw_wellFormed⟩

private def doubleCutInput : DoubleCutInput host doubled where
  site := anchor

theorem double_cut_receipt :
    (checkDoubleCut doubleCutInput).toOption.isSome = true := by
  native_decide

private def vacuousRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 3
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }

private theorem vacuousRaw_wellFormed : vacuousRaw.WellFormed [] := by
  native_decide

private def vacuous : CheckedDiagram [] :=
  ⟨vacuousRaw, vacuousRaw_wellFormed⟩

private def vacuousInput : VacuousInput host vacuous where
  site := anchor
  sig := .rel [.iota]

theorem vacuous_wire_receipt :
    (checkVacuous vacuousInput).toOption.isSome = true := by
  native_decide

private def descendantIteration :
    OrdinaryIterationInput oneStubOccurrence.toSelection oneStubOccurrence where
  destination := rightRegion

theorem ordinary_descendant_iteration_receipt :
    (checkOrdinaryIteration descendantIteration).toOption.isSome = true := by
  native_decide

private def sameSiteIteration :
    OrdinaryIterationInput oneStubOccurrence.toSelection oneStubOccurrence where
  destination := anchor

theorem ordinary_same_site_iteration_receipt :
    (checkOrdinaryIteration sameSiteIteration).toOption.isSome = true := by
  native_decide

/-!
Deiteration starts from a source that already contains an ancestor copy and a
strictly inner copy.  A second root copy with another boundary wire supplies the
ordered-attachment refusal, while the sibling copy supplies the ancestry refusal.
-/

private def copyPatternRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .identity 0 .iota 2
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 1⟩] } }
  boundary := [0, 1]

private theorem copyPatternRaw_wellFormed :
    copyPatternRaw.WellFormed [] := by
  constructor <;> native_decide

private def copyPattern : CheckedOpenDiagram [] :=
  ⟨copyPatternRaw, copyPatternRaw_wellFormed⟩

private def deiterationSourceRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 4
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 0 .iota 2
    | ⟨3, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 0⟩, ⟨1, .identity 0⟩,
              ⟨3, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 1⟩, ⟨1, .identity 1⟩,
              ⟨3, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨2, .identity 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨2, .identity 1⟩] }

private theorem deiterationSourceRaw_wellFormed :
    deiterationSourceRaw.WellFormed [] := by
  native_decide

private def deiterationSource : CheckedDiagram [] :=
  ⟨deiterationSourceRaw, deiterationSourceRaw_wellFormed⟩

private def deiterationRoot : deiterationSource.val.RegionId := ⟨0, by decide⟩
private def deiterationInnerRegion : deiterationSource.val.RegionId :=
  ⟨1, by decide⟩
private def deiterationSiblingRegion : deiterationSource.val.RegionId :=
  ⟨2, by decide⟩
private def deiterationAncestorNode : deiterationSource.val.NodeId :=
  ⟨0, by decide⟩
private def deiterationInnerNode : deiterationSource.val.NodeId :=
  ⟨1, by decide⟩
private def deiterationMismatchNode : deiterationSource.val.NodeId :=
  ⟨2, by decide⟩
private def deiterationSiblingNode : deiterationSource.val.NodeId :=
  ⟨3, by decide⟩
private def deiterationSharedWire0 : deiterationSource.val.WireId :=
  ⟨0, by decide⟩
private def deiterationSharedWire1 : deiterationSource.val.WireId :=
  ⟨1, by decide⟩
private def deiterationMismatchWire0 : deiterationSource.val.WireId :=
  ⟨2, by decide⟩
private def deiterationMismatchWire1 : deiterationSource.val.WireId :=
  ⟨3, by decide⟩

private def copyOccurrenceInput
    (region : deiterationSource.val.RegionId)
    (node : deiterationSource.val.NodeId)
    (wire0 wire1 : deiterationSource.val.WireId) :
    OccurrenceInput copyPattern deiterationSource where
  region := region
  regionMap := fun _ => region
  nodeMap := fun _ => node
  wireMap
    | ⟨0, _⟩ => wire0
    | ⟨1, _⟩ => wire1

private def innerOccurrence : Occurrence copyPattern deiterationSource :=
  (checkOccurrence
    (copyOccurrenceInput deiterationInnerRegion deiterationInnerNode
      deiterationSharedWire0 deiterationSharedWire1)).toOption.get
      (by native_decide)

private def ancestorOccurrence : Occurrence copyPattern deiterationSource :=
  (checkOccurrence
    (copyOccurrenceInput deiterationRoot deiterationAncestorNode
      deiterationSharedWire0 deiterationSharedWire1)).toOption.get
      (by native_decide)

private def mismatchedAncestorOccurrence :
    Occurrence copyPattern deiterationSource :=
  (checkOccurrence
    (copyOccurrenceInput deiterationRoot deiterationMismatchNode
      deiterationMismatchWire0 deiterationMismatchWire1)).toOption.get
      (by native_decide)

private def siblingOccurrence : Occurrence copyPattern deiterationSource :=
  (checkOccurrence
    (copyOccurrenceInput deiterationSiblingRegion deiterationSiblingNode
      deiterationSharedWire0 deiterationSharedWire1)).toOption.get
      (by native_decide)

private def descendantDeiteration :
    OrdinaryDeiterationInput innerOccurrence.toSelection innerOccurrence
      ancestorOccurrence.toSelection ancestorOccurrence where

private def mismatchedDeiteration :
    OrdinaryDeiterationInput innerOccurrence.toSelection innerOccurrence
      mismatchedAncestorOccurrence.toSelection
      mismatchedAncestorOccurrence where

private def nonAncestorDeiteration :
    OrdinaryDeiterationInput innerOccurrence.toSelection innerOccurrence
      siblingOccurrence.toSelection siblingOccurrence where

theorem ordinary_deiteration_receipt :
    (checkOrdinaryDeiteration descendantDeiteration).toOption.isSome = true := by
  native_decide

example :
    (checkOrdinaryDeiteration descendantDeiteration).toOption.map
      (fun checked =>
        decide
          (checked.target.val.nodeCount + 1 =
            checked.source.val.nodeCount)) =
      some true := by
  native_decide

example :
    (checkOrdinaryDeiteration descendantDeiteration).toOption.map
      (fun checked =>
        decide
          (checked.survivingJustifier.boundaryAttachments.length = 2)) =
      some true := by
  native_decide

example
    (checked : CheckedOrdinaryDeiteration descendantDeiteration)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) :=
  checked.sound pre definitionEnv

example :
    structuralError? (checkOrdinaryDeiteration mismatchedDeiteration) =
      some .copyBoundaryMismatch := by
  native_decide

example :
    structuralError? (checkOrdinaryDeiteration nonAncestorDeiteration) =
      some .illegalDeiterationJustifier := by
  native_decide

private def retargetedIteration :
    IdentityRetargetedCopyInput IdentityFixtures.retargetHost
      ConcreteExamples.repeatedBoundaryAlias_checked where
  direction := .iteration
  site := IdentityFixtures.nestedSite
  sourceTarget := IdentityFixtures.sourceTarget
  retargets :=
    [IdentityFixtures.retargetInput 1, IdentityFixtures.retargetInput 0]

example :
    (checkIdentityRetargetedCopy retargetedIteration).toOption.isSome =
      true := by
  native_decide

end StructuralFixtures
end VisualProof
