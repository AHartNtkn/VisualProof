import VisualProof.Rule.Structural
import VisualProof.Diagram.Concrete.Subgraph.SpliceExamples

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

/-- An accepted insertion owns an injective raw host-wire carrier. -/
example (checked : StructuralInsertionReceipt insertionInput) :
    Function.Injective checked.rawHostWire :=
  checked.rawHostWire_injective

/-- An accepted insertion preserves signatures along its raw host-wire carrier. -/
example (checked : StructuralInsertionReceipt insertionInput)
    (wire : host.val.WireId) :
    (checked.target.val.wires (checked.rawHostWire wire)).sig =
      (host.val.wires wire).sig :=
  checked.rawHostWire_signature wire

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

private def doubleCutChecked : CheckedDoubleCut doubleCutInput :=
  (checkDoubleCut doubleCutInput).toOption.get (by native_decide)

/-- The canonical receipt owns a total, injective positional wire carrier. -/
example : Function.Injective doubleCutChecked.wireEquiv :=
  doubleCutChecked.wireEquiv_injective

/-- Every canonical wire retains its signature under the checked carrier. -/
example (wire : host.val.WireId) :
    (doubled.val.wires (doubleCutChecked.wireEquiv wire)).sig =
      (host.val.wires wire).sig :=
  doubleCutChecked.wireEquiv_signature wire

/-!
An intrinsically identical endpoint obtained by renaming two concrete wires is
not a valid stable-ID double-cut target when those positions have different
signatures.  Intrinsic equality alone therefore cannot admit it.
-/

private def mixedPlainRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 3
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 (.rel []) 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
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

private theorem mixedPlainRaw_wellFormed : mixedPlainRaw.WellFormed [] := by
  native_decide

private def mixedPlain : CheckedDiagram [] :=
  ⟨mixedPlainRaw, mixedPlainRaw_wellFormed⟩

private def mixedDoubledRaw : ConcreteDiagram 0 where
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
    | ⟨0, _⟩ => .identity 4 (.rel []) 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
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

private theorem mixedDoubledRaw_wellFormed :
    mixedDoubledRaw.WellFormed [] := by
  native_decide

private def mixedDoubled : CheckedDiagram [] :=
  ⟨mixedDoubledRaw, mixedDoubledRaw_wellFormed⟩

private def renamedMixedDoubledRaw : ConcreteDiagram 0 where
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
    | ⟨0, _⟩ => .identity 4 (.rel []) 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }

private theorem renamedMixedDoubledRaw_wellFormed :
    renamedMixedDoubledRaw.WellFormed [] := by
  native_decide

private def renamedMixedDoubled : CheckedDiagram [] :=
  ⟨renamedMixedDoubledRaw, renamedMixedDoubledRaw_wellFormed⟩

private def mixedDoubleCutInput : DoubleCutInput mixedPlain mixedDoubled where
  site := ⟨0, by decide⟩

private def renamedMixedDoubleCutInput :
    DoubleCutInput mixedPlain renamedMixedDoubled where
  site := ⟨0, by decide⟩

example :
    (checkDoubleCut mixedDoubleCutInput).toOption.isSome = true := by
  native_decide

example :
    intrinsicRegionsEqual (elaborate renamedMixedDoubled)
      (elaborate mixedDoubled) = true := by
  native_decide

example :
    structuralError? (checkDoubleCut renamedMixedDoubleCutInput) =
      some .targetMismatch := by
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

private def descendantIterationChecked :
    CheckedOrdinaryIteration descendantIteration :=
  (checkOrdinaryIteration descendantIteration).toOption.get (by native_decide)

/-- Ordinary iteration exposes the accepted destination host-wire image exactly. -/
example :
    descendantIterationChecked.rawHostWire anchorWire =
      (⟨0, by decide⟩ : descendantIterationChecked.target.val.WireId) := by
  native_decide

/-- The accepted ordinary-iteration carrier is injective. -/
example : Function.Injective descendantIterationChecked.rawHostWire :=
  descendantIterationChecked.rawHostWire_injective

/-- The accepted ordinary-iteration carrier preserves every host signature. -/
example (wire : host.val.WireId) :
    (descendantIterationChecked.target.val.wires
      (descendantIterationChecked.rawHostWire wire)).sig =
        (host.val.wires wire).sig :=
  descendantIterationChecked.rawHostWire_signature wire

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

private def carrierErasureChecked :
    StructuralErasureReceipt (erasureInput .forward) :=
  (checkStructuralErasure (erasureInput .forward)).toOption.get
    (by native_decide)

/-- Erasure maps an accepted insertion host wire exactly back to the base. -/
example :
    carrierErasureChecked.rawWireImage?
        (⟨0, by decide⟩ : carrierErasureChecked.source.val.WireId) =
      some anchorWire := by
  native_decide

/-- Accepted structural fragments have no internal wire, so every raw source
wire lies in the insertion host carrier and receives an exact base image. -/
example :
    ∀ wire : carrierErasureChecked.source.val.WireId,
      ∃ mapped, carrierErasureChecked.rawWireImage? wire = some mapped := by
  native_decide

/-- The accepted erasure carrier is injective on mapped identities. -/
example {left right : carrierErasureChecked.source.val.WireId}
    {mapped : carrierErasureChecked.target.val.WireId}
    (leftMapped : carrierErasureChecked.rawWireImage? left = some mapped)
    (rightMapped : carrierErasureChecked.rawWireImage? right = some mapped) :
    left = right :=
  carrierErasureChecked.rawWireImage_injective leftMapped rightMapped

/-- The accepted erasure carrier preserves every mapped signature. -/
example {wire : carrierErasureChecked.source.val.WireId}
    {mapped : carrierErasureChecked.target.val.WireId}
    (mappedExact : carrierErasureChecked.rawWireImage? wire = some mapped) :
    (carrierErasureChecked.target.val.wires mapped).sig =
      (carrierErasureChecked.source.val.wires wire).sig :=
  carrierErasureChecked.rawWireImage_signature mappedExact

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

private def descendantDeiterationChecked :
    CheckedOrdinaryDeiteration descendantDeiteration :=
  (checkOrdinaryDeiteration descendantDeiteration).toOption.get
    (by native_decide)

/-- A surviving source wire maps to its exact dense removal position. -/
example :
    descendantDeiterationChecked.rawWireImage? deiterationSharedWire0 =
      some (⟨0, by decide⟩ : descendantDeiterationChecked.target.val.WireId) := by
  native_decide

/-- For this accepted receipt, any wire excluded by the retained removal list
has exactly no target image. -/
example (wire : descendantDeiterationChecked.source.val.WireId)
    (removed : wire ∉ Removal.wires innerOccurrence) :
    descendantDeiterationChecked.rawWireImage? wire = none :=
  descendantDeiterationChecked.rawWireImage_eq_none_of_not_mem wire removed

/-- The accepted deiteration carrier is injective on surviving identities. -/
example {left right : descendantDeiterationChecked.source.val.WireId}
    {mapped : descendantDeiterationChecked.target.val.WireId}
    (leftMapped : descendantDeiterationChecked.rawWireImage? left = some mapped)
    (rightMapped : descendantDeiterationChecked.rawWireImage? right = some mapped) :
    left = right :=
  descendantDeiterationChecked.rawWireImage_injective leftMapped rightMapped

/-- The accepted deiteration carrier preserves every surviving signature. -/
example {wire : descendantDeiterationChecked.source.val.WireId}
    {mapped : descendantDeiterationChecked.target.val.WireId}
    (mappedExact : descendantDeiterationChecked.rawWireImage? wire = some mapped) :
    (descendantDeiterationChecked.target.val.wires mapped).sig =
      (descendantDeiterationChecked.source.val.wires wire).sig :=
  descendantDeiterationChecked.rawWireImage_signature mappedExact

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

end StructuralFixtures
end VisualProof
