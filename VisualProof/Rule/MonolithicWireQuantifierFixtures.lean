import VisualProof.Rule.MonolithicWireQuantifier
import VisualProof.Diagram.Concrete.Examples

namespace VisualProof

namespace MonolithicWireQuantifierFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

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

private def mixedParitySever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [firstMixedContent, secondMixedContent]

example :
    (applyMonolithicRelationSever mixedParitySource mixedParitySever).toOption.map
        (fun applied =>
          (applied.target.val.nodeCount, applied.target.val.wireCount)) =
      some (2, 4) := by
  native_decide

private def mixedParitySeverApplied :
    AppliedMonolithicRelationSever mixedParitySource mixedParitySever :=
  (applyMonolithicRelationSever mixedParitySource mixedParitySever)
    |>.toOption.get
    (by native_decide)

example :
    (mixedParitySeverApplied.target.val.wiresList.getLast?
      |>.map fun wire =>
        ((mixedParitySeverApplied.target.val.wires wire).sig,
          (mixedParitySeverApplied.target.val.wires wire).scope.val)) =
      some (.rel [.iota], 0) := by
  native_decide

example
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel []) :
    Directed .forward
      (denoteChecked model.toPreModel definitionEnv mixedParitySource)
      (denoteChecked model.toPreModel definitionEnv
        mixedParitySeverApplied.target) := by
  exact
    relation_sever_sound .forward (idx 0) unaryEqualityPattern
      [firstMixedContent, secondMixedContent]
      mixedParitySeverApplied model definitionEnv

private def backwardNegativeSever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .backward
  scope := idx 1
  pattern := unaryEqualityPattern
  occurrences := [secondMixedContent]

private def backwardNegativeSeverApplied :
    AppliedMonolithicRelationSever mixedParitySource backwardNegativeSever :=
  (applyMonolithicRelationSever mixedParitySource backwardNegativeSever)
    |>.toOption.get
    (by native_decide)

example
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel []) :
    Directed .backward
      (denoteChecked model.toPreModel definitionEnv mixedParitySource)
      (denoteChecked model.toPreModel definitionEnv
        backwardNegativeSeverApplied.target) := by
  exact
    relation_sever_sound .backward (idx 1) unaryEqualityPattern
      [secondMixedContent] backwardNegativeSeverApplied model definitionEnv

private def overlappingSever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [firstMixedContent, firstMixedContent]

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

private def reorderedSever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [reorderedFirstContent, reorderedSecondContent]

private def error?
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source} :
    Except MonolithicWireQuantifierError
        (AppliedMonolithicRelationSever source input) →
      Option MonolithicWireQuantifierError
  | .error error => some error
  | .ok _ => none

example :
    error?
      (applyMonolithicRelationSever mixedParitySource reorderedSever) =
      some .contentMismatch := by
  native_decide

example :
    error?
      (applyMonolithicRelationSever mixedParitySource overlappingSever) =
      some .occurrencesOverlap := by
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
    MonolithicRelationSeverInput asymmetricBoundarySource where
  orientation := .forward
  scope := idx 0
  pattern := unaryAtomContent
  occurrences := [parameterThenFormalContent]

example :
    error?
      (applyMonolithicRelationSever
        asymmetricBoundarySource parameterThenFormalSever) =
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

private def relationJoinInput :
    MonolithicRelationJoinInput relationJoinSource where
  orientation := .forward
  wire := idx 0
  content := unaryAtomContent
  parameters := [idx 3]

example :
    (applyMonolithicRelationJoin relationJoinSource relationJoinInput).toOption.map
        (fun applied =>
          (applied.applications.length, applied.target.val.nodeCount,
            applied.target.val.wireCount)) =
      some (2, 2, 3) := by
  native_decide

private def relationJoinApplied :
    AppliedMonolithicRelationJoin relationJoinSource relationJoinInput :=
  (applyMonolithicRelationJoin relationJoinSource relationJoinInput)
    |>.toOption.get
    (by native_decide)

/-!
A repeated content boundary attached to two distinct same-signature source
wires generates one equality node.  The executor-owned raw atlas retains that
generated origin explicitly rather than collapsing it into either attachment.
-/

private def repeatedBoundaryJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota, .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 1⟩] }

private theorem repeatedBoundaryJoinSourceRaw_wellFormed :
    repeatedBoundaryJoinSourceRaw.WellFormed [] := by
  native_decide

private def repeatedBoundaryJoinSource : CheckedDiagram [] :=
  ⟨repeatedBoundaryJoinSourceRaw,
    repeatedBoundaryJoinSourceRaw_wellFormed⟩

private def repeatedBoundaryJoinInput :
    MonolithicRelationJoinInput repeatedBoundaryJoinSource where
  orientation := .forward
  wire := idx 0
  content := ConcreteExamples.repeatedBoundaryAlias_checked
  parameters := []

private def repeatedBoundaryJoinApplied :
    AppliedMonolithicRelationJoin repeatedBoundaryJoinSource
      repeatedBoundaryJoinInput :=
  (applyMonolithicRelationJoin repeatedBoundaryJoinSource
      repeatedBoundaryJoinInput).toOption.get
    (by native_decide)

example :
    repeatedBoundaryJoinApplied.concreteResult.steps.map
        (fun step =>
          (step.sourceAttachments,
            step.attachment.identityRequests.length)) =
      [([idx 1, idx 2], 1)] := by
  native_decide

example :
    (match
      (repeatedBoundaryJoinApplied.concreteResult.finalNodeOriginEquiv
        (idx 0)).1 with
    | .inr ⟨occurrence, .inr request⟩ =>
        occurrence.val = 0 && request.val = 0
    | _ => false) = true := by
  native_decide

private def repeatedBoundaryRepresentativeSnapshot :
    Nat × Nat × Nat :=
  let step := repeatedBoundaryJoinApplied.concreteResult.steps.get (idx 0)
  let source := ConcreteExamples.repeatedBoundaryAlias_checked.val.boundary.get
    (idx 0)
  let sourceMember :
      source ∈ ConcreteExamples.repeatedBoundaryAlias_checked.val.boundary := by
    native_decide
  ((step.attachment.representativePosition source sourceMember).val,
    (step.attachment.representativeTarget source sourceMember).val,
    (step.attachment.target (idx 1)).val)

example :
    repeatedBoundaryRepresentativeSnapshot = (0, 1, 2) := by
  native_decide

example :
    (match relationJoinApplied.concreteResult.finalRegionOriginEquiv (idx 0) with
    | .inl region => region.val = 0
    | _ => false) = true := by
  native_decide

example :
    (match (relationJoinApplied.concreteResult.finalNodeOriginEquiv (idx 0)).1 with
    | .inr ⟨occurrence, .inl node⟩ =>
        occurrence.val = 0 && node.val = 0
    | _ => false) = true := by
  native_decide

example
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel []) :
    Directed .forward
      (denoteChecked model.toPreModel definitionEnv relationJoinSource)
      (denoteChecked model.toPreModel definitionEnv relationJoinApplied.target) := by
  exact
    relation_join_sound .forward (idx 0) unaryAtomContent [idx 3]
      relationJoinApplied model definitionEnv

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

private def nullarySever :
    MonolithicRelationSeverInput nullarySource where
  orientation := .forward
  scope := idx 0
  pattern := blankPattern
  occurrences := [firstBlankContent, secondBlankContent]

example :
    (applyMonolithicRelationSever nullarySource nullarySever).toOption.map
        (fun applied =>
          (applied.target.val.wiresList.head?.map fun wire =>
              (applied.target.val.wires wire).sig,
            applied.target.val.nodeCount)) =
      some (some (.rel []), 2) := by
  native_decide

/-! Repeated ordered formals remain distinct relation argument positions. -/

private def repeatedFormalPatternRaw : OpenConcreteDiagram 0 where
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
  boundary := [0, 0]

private theorem repeatedFormalPatternRaw_wellFormed :
    repeatedFormalPatternRaw.WellFormed [] := by
  constructor <;> native_decide

private def repeatedFormalPattern : CheckedOpenDiagram [] :=
  ⟨repeatedFormalPatternRaw, repeatedFormalPatternRaw_wellFormed⟩

private def repeatedFormalSourceRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints :=
        [⟨0, .identity 0⟩, ⟨0, .identity 1⟩,
          ⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

private theorem repeatedFormalSourceRaw_wellFormed :
    repeatedFormalSourceRaw.WellFormed [] := by
  native_decide

private def repeatedFormalSource : CheckedDiagram [] :=
  ⟨repeatedFormalSourceRaw, repeatedFormalSourceRaw_wellFormed⟩

private def repeatedFormalOccurrenceInput :
    OccurrenceInput repeatedFormalPattern repeatedFormalSource where
  region := idx 0
  regionMap := fun _ => idx 0
  nodeMap := fun _ => idx 0
  wireMap := fun _ => idx 0

private def repeatedFormalOccurrence :
    Occurrence repeatedFormalPattern repeatedFormalSource :=
  (checkOccurrence repeatedFormalOccurrenceInput).toOption.get
    (by native_decide)

private def repeatedFormalContent :
    ContentOccurrence repeatedFormalSource repeatedFormalPattern where
  selection := repeatedFormalOccurrence.toSelection
  occurrence := repeatedFormalOccurrence
  formals := [idx 0, idx 0]

private def repeatedFormalSever :
    MonolithicRelationSeverInput repeatedFormalSource where
  orientation := .forward
  scope := idx 0
  pattern := repeatedFormalPattern
  occurrences := [repeatedFormalContent]

private def repeatedFormalSeverApplied :
    AppliedMonolithicRelationSever repeatedFormalSource repeatedFormalSever :=
  (applyMonolithicRelationSever repeatedFormalSource repeatedFormalSever)
    |>.toOption.get
    (by native_decide)

example :
    repeatedFormalSeverApplied.target.val.wiresList.getLast?.map
        (fun wire =>
          (repeatedFormalSeverApplied.target.val.wires wire).sig) =
      some (.rel [.iota, .iota]) := by
  native_decide

example
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel []) :
    Directed .forward
      (denoteChecked model.toPreModel definitionEnv repeatedFormalSource)
      (denoteChecked model.toPreModel definitionEnv
        repeatedFormalSeverApplied.target) := by
  exact
    relation_sever_sound .forward (idx 0) repeatedFormalPattern
      [repeatedFormalContent] repeatedFormalSeverApplied model definitionEnv

private def mismatchedSecondContent :
    ContentOccurrence mixedParitySource unaryEqualityPattern where
  selection := firstMixedOccurrence.toSelection
  occurrence := secondMixedOccurrence
  formals := [idx 1]

private def mismatchedCopySever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [firstMixedContent, mismatchedSecondContent]

example :
    error?
      (applyMonolithicRelationSever mixedParitySource mismatchedCopySever) =
      some (.extractionRejected .selectionMismatch) := by
  native_decide

private def outsideScopeSever :
    MonolithicRelationSeverInput mixedParitySource where
  orientation := .backward
  scope := idx 1
  pattern := unaryEqualityPattern
  occurrences := [firstMixedContent, secondMixedContent]

example :
    error?
      (applyMonolithicRelationSever mixedParitySource outsideScopeSever) =
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
    MonolithicRelationSeverInput splitParameterSource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [firstSplitParameterContent, secondSplitParameterContent]

example :
    error?
      (applyMonolithicRelationSever
        splitParameterSource mismatchedParameterSever) =
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
    MonolithicRelationSeverInput innerScopedParameterSource where
  orientation := .forward
  scope := idx 0
  pattern := unaryEqualityPattern
  occurrences := [firstInnerScopedContent, secondInnerScopedContent]

example :
    error?
      (applyMonolithicRelationSever
        innerScopedParameterSource parameterScopeSever) =
      some .parameterOutsideScope := by
  native_decide

private def joinError?
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source} :
    Except MonolithicWireQuantifierError
        (AppliedMonolithicRelationJoin source input) →
      Option MonolithicWireQuantifierError
  | .error error => some error
  | .ok _ => none

private def nonAppliedJoin :
    MonolithicRelationJoinInput
      ConcreteExamples.higherOrderArgumentAtom_checked where
  orientation := .backward
  wire := idx 1
  content := blankPattern
  parameters := []

example :
    joinError?
      (applyMonolithicRelationJoin
        ConcreteExamples.higherOrderArgumentAtom_checked
        nonAppliedJoin) =
      some .nonAppliedEndpoint := by
  native_decide

private def missingParameterJoin :
    MonolithicRelationJoinInput relationJoinSource where
  orientation := .forward
  wire := idx 0
  content := unaryAtomContent
  parameters := []

example :
    joinError?
      (applyMonolithicRelationJoin relationJoinSource missingParameterJoin) =
      some .parameterMismatch := by
  native_decide

end MonolithicWireQuantifierFixtures

end VisualProof
