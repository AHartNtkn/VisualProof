import VisualProof.Rule.WireQuantifier
import VisualProof.Diagram.Concrete.Examples

namespace VisualProof

namespace WireQuantifierFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def iotaSeverRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }

private theorem iotaSeverRaw_wellFormed :
    iotaSeverRaw.WellFormed [] := by
  native_decide

private def iotaSeverSource : CheckedDiagram [] :=
  ⟨iotaSeverRaw, iotaSeverRaw_wellFormed⟩

private def iotaSeverInput : WireSeverInput iotaSeverSource :=
  .iota .forward (idx 0) [⟨idx 0, .identity 0⟩]

example :
    (applyWireSever iotaSeverSource iotaSeverInput).toOption.map
      (fun applied => applied.target.val.wireCount) =
      some 2 := by
  native_decide

example
    (applied : AppliedWireSever iotaSeverSource iotaSeverInput)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv iotaSeverSource)
      (denoteChecked pre definitionEnv applied.target) := by
  exact
    iota_sever_sound .forward (idx 0) [⟨idx 0, .identity 0⟩]
      applied pre definitionEnv

private def iotaJoinRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .identity 1⟩] }

private theorem iotaJoinRaw_wellFormed :
    iotaJoinRaw.WellFormed [] := by
  native_decide

private def iotaJoinSource : CheckedDiagram [] :=
  ⟨iotaJoinRaw, iotaJoinRaw_wellFormed⟩

private def iotaJoinInput : WireJoinInput iotaJoinSource :=
  .iota .forward (idx 0) (idx 1)

example :
    (applyWireJoin iotaJoinSource iotaJoinInput).toOption.map
      (fun applied => applied.target.val.wireCount) =
      some 1 := by
  native_decide

example
    (applied : AppliedWireJoin iotaJoinSource iotaJoinInput)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv iotaJoinSource)
      (denoteChecked pre definitionEnv applied.target) := by
  exact
    iota_join_sound .forward (idx 0) (idx 1)
      applied pre definitionEnv

/-! Mixed-parity exact-copy relation sever. -/

private def unaryEqualityPatternRaw : OpenConcreteDiagram 0 where
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

private theorem unaryEqualityPatternRaw_wellFormed :
    unaryEqualityPatternRaw.WellFormed [] := by
  constructor <;> native_decide

private def unaryEqualityPattern : CheckedOpenDiagram [] :=
  ⟨unaryEqualityPatternRaw, unaryEqualityPatternRaw_wellFormed⟩

private def mixedParityRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩, ⟨1, .identity 1⟩] }

private theorem mixedParityRaw_wellFormed :
    mixedParityRaw.WellFormed [] := by
  native_decide

private def mixedParitySource : CheckedDiagram [] :=
  ⟨mixedParityRaw, mixedParityRaw_wellFormed⟩

private def mixedOccurrenceInput
    (region : mixedParitySource.val.RegionId)
    (node : mixedParitySource.val.NodeId)
    (formal : mixedParitySource.val.WireId) :
    OccurrenceInput unaryEqualityPattern mixedParitySource where
  region := region
  regionMap := fun _ => region
  nodeMap := fun _ => node
  wireMap
    | ⟨0, _⟩ => formal
    | ⟨1, _⟩ => idx 2

private def firstMixedOccurrence :
    Occurrence unaryEqualityPattern mixedParitySource :=
  (checkOccurrence (mixedOccurrenceInput (idx 0) (idx 0) (idx 0))).toOption.get
    (by native_decide)

private def secondMixedOccurrence :
    Occurrence unaryEqualityPattern mixedParitySource :=
  (checkOccurrence (mixedOccurrenceInput (idx 1) (idx 1) (idx 1))).toOption.get
    (by native_decide)

private def firstMixedContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := firstMixedOccurrence.toSelection
  occurrence := firstMixedOccurrence
  formals := [idx 0]

private def secondMixedContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := secondMixedOccurrence.toSelection
  occurrence := secondMixedOccurrence
  formals := [idx 1]

private def mixedParitySever : WireSeverInput mixedParitySource :=
  .relation .forward (idx 0) unaryEqualityPattern
    [firstMixedContent, secondMixedContent]

example :
    (applyWireSever mixedParitySource mixedParitySever).toOption.map
      (fun applied =>
        (applied.target.val.nodeCount, applied.target.val.wireCount)) =
      some (2, 4) := by
  native_decide

private def reorderedSecondContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := secondMixedOccurrence.toSelection
  occurrence := secondMixedOccurrence
  formals := [idx 2, idx 1]

private def reorderedFirstContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := firstMixedOccurrence.toSelection
  occurrence := firstMixedOccurrence
  formals := [idx 0, idx 2]

private def reorderedSever : WireSeverInput mixedParitySource :=
  .relation .forward (idx 0) unaryEqualityPattern
    [reorderedFirstContent, reorderedSecondContent]

private def error?
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source} :
    Except WireQuantifierError (AppliedWireSever source input) →
      Option WireQuantifierError
  | .error error => some error
  | .ok _ => none

example :
    error? (applyWireSever mixedParitySource reorderedSever) =
      some .contentMismatch := by
  native_decide

/-! Relation grounding consumes every applied-head endpoint. -/

private def unaryAtomContentRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 [.iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota]
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem unaryAtomContentRaw_wellFormed :
    unaryAtomContentRaw.WellFormed [] := by
  constructor <;> native_decide

private def unaryAtomContent : CheckedOpenDiagram [] :=
  ⟨unaryAtomContentRaw, unaryAtomContentRaw_wellFormed⟩

/-!
The relation-sever boundary is canonical content order: ordered formals first,
then ambient parameters. Distinct signatures make a reversed order observable.
-/

private def asymmetricBoundarySourceRaw : ConcreteDiagram 0 :=
  unaryAtomContentRaw.diagram

private theorem asymmetricBoundarySourceRaw_wellFormed :
    asymmetricBoundarySourceRaw.WellFormed [] :=
  unaryAtomContentRaw_wellFormed.1

private def asymmetricBoundarySource : CheckedDiagram [] :=
  ⟨asymmetricBoundarySourceRaw, asymmetricBoundarySourceRaw_wellFormed⟩

private def asymmetricBoundaryOccurrenceInput :
    OccurrenceInput unaryAtomContent asymmetricBoundarySource where
  region := idx 0
  regionMap := fun _ => idx 0
  nodeMap := fun _ => idx 0
  wireMap := fun wire => wire

private def asymmetricBoundaryOccurrence :
    Occurrence unaryAtomContent asymmetricBoundarySource :=
  (checkOccurrence asymmetricBoundaryOccurrenceInput).toOption.get
    (by native_decide)

private def parameterThenFormalContent :
    ContentOccurrence asymmetricBoundarySource unaryAtomContent where
  selection := asymmetricBoundaryOccurrence.toSelection
  occurrence := asymmetricBoundaryOccurrence
  formals := [idx 1]

private def parameterThenFormalSever :
    WireSeverInput asymmetricBoundarySource :=
  .relation .forward (idx 0) unaryAtomContent [parameterThenFormalContent]

example :
    error? (applyWireSever asymmetricBoundarySource parameterThenFormalSever) =
      some .contentMismatch := by
  native_decide

private def relationJoinRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes
    | ⟨0, _⟩ => .atom 1 [.iota]
    | ⟨1, _⟩ => .atom 2 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .arg 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }

private theorem relationJoinRaw_wellFormed :
    relationJoinRaw.WellFormed [] := by
  native_decide

private def relationJoinSource : CheckedDiagram [] :=
  ⟨relationJoinRaw, relationJoinRaw_wellFormed⟩

private def relationJoinInput : WireJoinInput relationJoinSource :=
  .relation .forward (idx 0) unaryAtomContent [idx 3]

example :
    (applyWireJoin relationJoinSource relationJoinInput).toOption.map
      (fun applied =>
        (applied.applications.length, applied.target.val.nodeCount,
          applied.target.val.wireCount)) =
      some (2, 2, 3) := by
  native_decide

/-! Nullary content and exact refusal gates. -/

private def blankPatternRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 0
      wireCount := 0
      root := 0
      regions := fun _ => .sheet
      nodes := fun node => Fin.elim0 node
      wires := fun wire => Fin.elim0 wire }
  boundary := []

private theorem blankPatternRaw_wellFormed :
    blankPatternRaw.WellFormed [] := by
  constructor <;> native_decide

private def blankPattern : CheckedOpenDiagram [] :=
  ⟨blankPatternRaw, blankPatternRaw_wellFormed⟩

private def nullarySourceRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 0
  wireCount := 0
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes := fun node => Fin.elim0 node
  wires := fun wire => Fin.elim0 wire

private theorem nullarySourceRaw_wellFormed :
    nullarySourceRaw.WellFormed [] := by
  native_decide

private def nullarySource : CheckedDiagram [] :=
  ⟨nullarySourceRaw, nullarySourceRaw_wellFormed⟩

private def blankOccurrenceInput
    (region : nullarySource.val.RegionId) :
    OccurrenceInput blankPattern nullarySource where
  region := region
  regionMap := fun _ => region
  nodeMap := fun node => Fin.elim0 node
  wireMap := fun wire => Fin.elim0 wire

private def firstBlankOccurrence : Occurrence blankPattern nullarySource :=
  (checkOccurrence (blankOccurrenceInput (idx 1))).toOption.get
    (by native_decide)

private def secondBlankOccurrence : Occurrence blankPattern nullarySource :=
  (checkOccurrence (blankOccurrenceInput (idx 2))).toOption.get
    (by native_decide)

private def firstBlankContent :
    ContentOccurrence nullarySource blankPattern where
  selection := firstBlankOccurrence.toSelection
  occurrence := firstBlankOccurrence
  formals := []

private def secondBlankContent :
    ContentOccurrence nullarySource blankPattern where
  selection := secondBlankOccurrence.toSelection
  occurrence := secondBlankOccurrence
  formals := []

private def nullarySever : WireSeverInput nullarySource :=
  .relation .forward (idx 0) blankPattern
    [firstBlankContent, secondBlankContent]

example :
    (applyWireSever nullarySource nullarySever).toOption.map
      (fun applied =>
        (applied.target.val.wiresList.head?.map fun wire =>
            (applied.target.val.wires wire).sig,
          applied.target.val.nodeCount)) =
      some (some (.rel []), 2) := by
  native_decide

private def mismatchedSecondContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := firstMixedOccurrence.toSelection
  occurrence := secondMixedOccurrence
  formals := [idx 1]

private def mismatchedCopySever : WireSeverInput mixedParitySource :=
  .relation .forward (idx 0) unaryEqualityPattern
    [firstMixedContent, mismatchedSecondContent]

example :
    error? (applyWireSever mixedParitySource mismatchedCopySever) =
      some (.extractionRejected .selectionMismatch) := by
  native_decide

private def outsideScopeSever : WireSeverInput mixedParitySource :=
  .relation .backward (idx 1) unaryEqualityPattern
    [firstMixedContent, secondMixedContent]

example :
    error? (applyWireSever mixedParitySource outsideScopeSever) =
      some .occurrenceOutsideScope := by
  native_decide

private def splitParameterRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 1⟩] }

private theorem splitParameterRaw_wellFormed :
    splitParameterRaw.WellFormed [] := by
  native_decide

private def splitParameterSource : CheckedDiagram [] :=
  ⟨splitParameterRaw, splitParameterRaw_wellFormed⟩

private def splitParameterOccurrenceInput
    (region : splitParameterSource.val.RegionId)
    (node : splitParameterSource.val.NodeId)
    (formal parameter : splitParameterSource.val.WireId) :
    OccurrenceInput unaryEqualityPattern splitParameterSource where
  region := region
  regionMap := fun _ => region
  nodeMap := fun _ => node
  wireMap
    | ⟨0, _⟩ => formal
    | ⟨1, _⟩ => parameter

private def firstSplitParameterOccurrence :
    Occurrence unaryEqualityPattern splitParameterSource :=
  (checkOccurrence
    (splitParameterOccurrenceInput
      (idx 0) (idx 0) (idx 0) (idx 2))).toOption.get
    (by native_decide)

private def secondSplitParameterOccurrence :
    Occurrence unaryEqualityPattern splitParameterSource :=
  (checkOccurrence
    (splitParameterOccurrenceInput
      (idx 1) (idx 1) (idx 1) (idx 3))).toOption.get
    (by native_decide)

private def firstSplitParameterContent :
    ContentOccurrence splitParameterSource unaryEqualityPattern where
  selection := firstSplitParameterOccurrence.toSelection
  occurrence := firstSplitParameterOccurrence
  formals := [idx 0]

private def secondSplitParameterContent :
    ContentOccurrence splitParameterSource unaryEqualityPattern where
  selection := secondSplitParameterOccurrence.toSelection
  occurrence := secondSplitParameterOccurrence
  formals := [idx 1]

private def mismatchedParameterSever :
    WireSeverInput splitParameterSource :=
  .relation .forward (idx 0) unaryEqualityPattern
    [firstSplitParameterContent, secondSplitParameterContent]

example :
    error? (applyWireSever splitParameterSource mismatchedParameterSever) =
      some .parameterMismatch := by
  native_decide

private def innerScopedParameterRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes
    | ⟨0, _⟩ => .identity 1 .iota 2
    | ⟨1, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .identity 1⟩, ⟨1, .identity 1⟩] }

private theorem innerScopedParameterRaw_wellFormed :
    innerScopedParameterRaw.WellFormed [] := by
  native_decide

private def innerScopedParameterSource : CheckedDiagram [] :=
  ⟨innerScopedParameterRaw, innerScopedParameterRaw_wellFormed⟩

private def innerScopedOccurrenceInput
    (region : innerScopedParameterSource.val.RegionId)
    (node : innerScopedParameterSource.val.NodeId)
    (formal : innerScopedParameterSource.val.WireId) :
    OccurrenceInput unaryEqualityPattern innerScopedParameterSource where
  region := region
  regionMap := fun _ => region
  nodeMap := fun _ => node
  wireMap
    | ⟨0, _⟩ => formal
    | ⟨1, _⟩ => idx 2

private def firstInnerScopedOccurrence :
    Occurrence unaryEqualityPattern innerScopedParameterSource :=
  (checkOccurrence
    (innerScopedOccurrenceInput (idx 1) (idx 0) (idx 0))).toOption.get
    (by native_decide)

private def secondInnerScopedOccurrence :
    Occurrence unaryEqualityPattern innerScopedParameterSource :=
  (checkOccurrence
    (innerScopedOccurrenceInput (idx 2) (idx 1) (idx 1))).toOption.get
    (by native_decide)

private def firstInnerScopedContent :
    ContentOccurrence innerScopedParameterSource unaryEqualityPattern where
  selection := firstInnerScopedOccurrence.toSelection
  occurrence := firstInnerScopedOccurrence
  formals := [idx 0]

private def secondInnerScopedContent :
    ContentOccurrence innerScopedParameterSource unaryEqualityPattern where
  selection := secondInnerScopedOccurrence.toSelection
  occurrence := secondInnerScopedOccurrence
  formals := [idx 1]

private def parameterScopeSever :
    WireSeverInput innerScopedParameterSource :=
  .relation .forward (idx 0) unaryEqualityPattern
    [firstInnerScopedContent, secondInnerScopedContent]

example :
    error?
      (applyWireSever innerScopedParameterSource parameterScopeSever) =
      some .parameterOutsideScope := by
  native_decide

private def joinError?
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source} :
    Except WireQuantifierError (AppliedWireJoin source input) →
      Option WireQuantifierError
  | .error error => some error
  | .ok _ => none

private def nonAppliedJoin :
    WireJoinInput ConcreteExamples.higherOrderArgumentAtom_checked :=
  .relation .backward (idx 1) blankPattern []

example :
    joinError?
      (applyWireJoin ConcreteExamples.higherOrderArgumentAtom_checked
        nonAppliedJoin) =
      some .nonAppliedEndpoint := by
  native_decide

private def missingParameterJoin : WireJoinInput relationJoinSource :=
  .relation .forward (idx 0) unaryAtomContent []

example :
    joinError? (applyWireJoin relationJoinSource missingParameterJoin) =
      some .parameterMismatch := by
  native_decide

end WireQuantifierFixtures

end VisualProof
