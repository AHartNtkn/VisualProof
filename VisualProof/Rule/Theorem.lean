import VisualProof.Diagram.Concrete.Subgraph.FactorizationInsertion
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction
import VisualProof.Diagram.Concrete.Subgraph.RemovalSpliceWireImage
import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw
import VisualProof.Rule.Orientation
import VisualProof.Rule.Tag
import VisualProof.Theory.Semantics

namespace VisualProof

universe u

/-- One already checked theorem statement with an exact ordered signature
interface.  Proof replay supplies validity in the chronological theorem layer;
rule application only consumes this statement and its exact occurrence. -/
structure RuleTheorem (definitions : Definitions) where
  arguments : List Sig
  left : CheckedOpenDiagram definitions.signatures
  right : CheckedOpenDiagram definitions.signatures
  leftBoundary : checkedBoundarySigs left = arguments
  rightBoundary : checkedBoundarySigs right = arguments
  leftCompilation : OpenCompilation left
  leftCompilationAccepted : compileOpen left = some leftCompilation
  rightCompilation : OpenCompilation right
  rightCompilationAccepted : compileOpen right = some rightCompilation
  valid : ∀ (model : Model.{u})
      (definitionEnv : DefinitionEnv model.toPreModel definitions.signatures)
      (lawful : DefinitionLawful model.toPreModel definitions definitionEnv)
      (values : BoundaryEnv model.toPreModel arguments),
    denoteOpen model.toPreModel definitionEnv
        (leftBoundary ▸ leftCompilation.openDiagram) values →
      denoteOpen model.toPreModel definitionEnv
        (rightBoundary ▸ rightCompilation.openDiagram) values

inductive TheoremDirection
  | forward
  | reverse
  deriving Repr, DecidableEq

/-- A theorem citation pins the exact source-side occurrence. -/
inductive TheoremApplication
    (definitions : Definitions)
    (source : CheckedDiagram definitions.signatures) : Type
  | forward
      (statement : RuleTheorem.{u} definitions)
      (orientation : Orientation)
      (occurrence : Occurrence statement.left source) :
      TheoremApplication definitions source
  | reverse
      (statement : RuleTheorem.{u} definitions)
      (orientation : Orientation)
      (occurrence : Occurrence statement.right source) :
      TheoremApplication definitions source

namespace TheoremApplication

def statement {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    TheoremApplication (definitions := definitions) source →
      RuleTheorem.{u} definitions
  | .forward statement _ _ => statement
  | .reverse statement _ _ => statement

def orientation {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    TheoremApplication (definitions := definitions) source → Orientation
  | .forward _ orientation _ => orientation
  | .reverse _ orientation _ => orientation

def direction {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    TheoremApplication (definitions := definitions) source → TheoremDirection
  | .forward .. => .forward
  | .reverse .. => .reverse

def sourceFragment
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    TheoremApplication (definitions := definitions) source →
      CheckedOpenDiagram definitions.signatures
  | .forward statement _ _ => statement.left
  | .reverse statement _ _ => statement.right

def targetFragment
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    TheoremApplication (definitions := definitions) source →
      CheckedOpenDiagram definitions.signatures
  | .forward statement _ _ => statement.right
  | .reverse statement _ _ => statement.left

def occurrence
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    (input : TheoremApplication (definitions := definitions) source) →
      Occurrence input.sourceFragment source
  | .forward _ _ occurrence => occurrence
  | .reverse _ _ occurrence => occurrence

def sourceBoundary
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    (input : TheoremApplication (definitions := definitions) source) →
      checkedBoundarySigs input.sourceFragment = input.statement.arguments
  | .forward statement _ _ => statement.leftBoundary
  | .reverse statement _ _ => statement.rightBoundary

def targetBoundary
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures} :
    (input : TheoremApplication (definitions := definitions) source) →
      checkedBoundarySigs input.targetFragment = input.statement.arguments
  | .forward statement _ _ => statement.rightBoundary
  | .reverse statement _ _ => statement.leftBoundary

theorem boundaryLength
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures}
    (input : TheoremApplication (definitions := definitions) source) :
    input.targetFragment.val.boundary.length =
      input.sourceFragment.val.boundary.length := by
  have signatures := input.targetBoundary.trans input.sourceBoundary.symm
  have lengths := congrArg List.length signatures
  simpa [checkedBoundarySigs] using lengths

def site {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures}
    (input : TheoremApplication (definitions := definitions) source) :
    source.val.RegionId :=
  input.occurrence.regionMap input.sourceFragment.val.diagram.root

end TheoremApplication

private def theoremPolarityLegal
    (orientation : Orientation) (direction : TheoremDirection)
    (depth : Nat) : Bool :=
  match orientation, direction with
  | .forward, .forward | .backward, .reverse => decide (depth % 2 = 0)
  | .forward, .reverse | .backward, .forward => decide (depth % 2 = 1)

inductive TheoremRuleError
  | sourceCompilationRejected
  | targetCompilationRejected
  | illegalPolarity
  | removalRejected (error : WFError)
  | reconstructionRejected
  | reconstructionIsoRejected
  | reconstructionCompilationRejected
  | targetAttachmentRejected
  | targetInsertionCompilationRejected
  | targetSpliceRejected (error : WFError)
  deriving Repr, DecidableEq

/-- Opaque receipt for one exact, polarity-checked theorem-side replacement. -/
structure AppliedTheorem
    (definitions : Definitions)
    (source : CheckedDiagram definitions.signatures)
    (input : TheoremApplication (definitions := definitions) source) where
  private mk ::
  private sourceCompilation : OpenCompilation input.sourceFragment
  private sourceCompilationAccepted :
    compileOpen input.sourceFragment = some sourceCompilation
  private targetCompilation : OpenCompilation input.targetFragment
  private targetCompilationAccepted :
    compileOpen input.targetFragment = some targetCompilation
  private removed : RemovalResult input.occurrence
  private removedAccepted : remove input.occurrence = .ok removed
  private reconstruction : ConcreteSpliceAttachment removed.complement
    removed.site input.sourceFragment
  private reconstructionAccepted :
    reconstructionAttachment? input.occurrence removed = some reconstruction
  private reconstructionIso : ConcreteIso reconstruction.diagram source.val
  private reconstructionIsoAccepted :
    Reconstruction.extract_splice_iso? input.occurrence removed reconstruction
        reconstructionAccepted =
      some reconstructionIso
  private reconstructionCompilation :
    InsertionCompilation sourceCompilation reconstruction
  private reconstructionCompilationAccepted :
    compileInsertion? sourceCompilation reconstruction =
      some reconstructionCompilation
  private legal : theoremPolarityLegal input.orientation input.direction
    reconstructionCompilation.site.frame.context.cutDepth = true
  private attachment : ConcreteSpliceAttachment removed.complement
    removed.site input.targetFragment
  private boundaryTargets :
    ∀ position : Fin input.targetFragment.val.boundary.length,
      attachment.target position =
        reconstruction.target (Fin.cast input.boundaryLength position)
  private insertion : InsertionCompilation targetCompilation attachment
  private insertionAccepted :
    compileInsertion? targetCompilation attachment = some insertion
  private result : RawConcreteSpliceResult attachment
  private resultAccepted : spliceRaw attachment = .ok result

namespace AppliedTheorem

/-- Cut depth of the exact checked replacement site. -/
def siteDepth
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
  (applied : AppliedTheorem definitions source input) : Nat :=
  applied.reconstructionCompilation.site.frame.context.cutDepth

/-- The checked citation gate exposes exactly the parity required by theorem
direction and replay orientation. -/
theorem siteDepth_parity
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input) :
    match input.orientation, input.direction with
    | .forward, .forward | .backward, .reverse =>
        applied.siteDepth % 2 = 0
    | .forward, .reverse | .backward, .forward =>
        applied.siteDepth % 2 = 1 := by
  induction applied using AppliedTheorem.rec
  rename_i sourceCompilation sourceCompilationAccepted targetCompilation
    targetCompilationAccepted
    removed removedAccepted reconstruction reconstructionAccepted
    reconstructionIso reconstructionIsoAccepted reconstructionCompilation
    reconstructionCompilationAccepted legal attachment boundaryTargets
    insertion insertionAccepted result resultAccepted
  cases input with
  | forward statement orientation occurrence =>
      cases orientation <;>
        simpa [siteDepth, theoremPolarityLegal] using of_decide_eq_true legal
  | reverse statement orientation occurrence =>
      cases orientation <;>
        simpa [siteDepth, theoremPolarityLegal] using of_decide_eq_true legal

def source
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (_applied : AppliedTheorem definitions source input) :
    CheckedDiagram definitions.signatures :=
  source

def target
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input) :
    CheckedDiagram definitions.signatures :=
  applied.result.checked

/-- Whether the theorem owner retained one source identity through occurrence
removal.  This classification does not expose either private receipt. -/
def rawWireRetained
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (_applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId) : Prop :=
  wire ∈ Removal.wires input.occurrence

instance rawWireRetainedDecidable
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId) :
    Decidable (applied.rawWireRetained wire) := by
  unfold rawWireRetained
  infer_instance

/-- Exact raw target identity of one retained source wire.  The owner composes
its private occurrence-removal index with its private accepted replacement
attachment; neither receipt is exposed. -/
def rawRetainedWire
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId)
    (retained : applied.rawWireRetained wire) :
    applied.target.val.WireId :=
  applied.attachment.hostWire
    (Removal.wireIndex input.occurrence wire retained)

/-- Partial raw source-wire image through the accepted theorem replacement. -/
def rawWireImage?
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId) : Option applied.target.val.WireId :=
  Reconstruction.removalSpliceWireImage?
    input.occurrence applied.removed applied.attachment wire

/-- Every retained theorem-source wire has its exact owner-derived image. -/
theorem rawWireImage_of_mem
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId)
    (retained : applied.rawWireRetained wire) :
    applied.rawWireImage? wire =
      some (applied.rawRetainedWire wire retained) := by
  exact Reconstruction.removalSpliceWireImage_of_mem
    input.occurrence applied.removed applied.attachment wire retained

/-- A wire removed with the cited theorem occurrence has no target identity. -/
theorem rawWireImage_eq_none_of_not_mem
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    (wire : source.val.WireId)
    (removed : ¬ applied.rawWireRetained wire) :
    applied.rawWireImage? wire = none := by
  exact Reconstruction.removalSpliceWireImage_eq_none_of_not_mem
    input.occurrence applied.removed applied.attachment wire removed

/-- The theorem replacement never identifies two surviving source wires. -/
theorem rawWireImage_injective
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    {left right : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (leftMapped : applied.rawWireImage? left = some mapped)
    (rightMapped : applied.rawWireImage? right = some mapped) :
    left = right := by
  exact Reconstruction.removalSpliceWireImage_injective
    input.occurrence applied.removed applied.attachment
      leftMapped rightMapped

/-- Every surviving theorem-source wire retains its exact signature. -/
theorem rawWireImage_signature
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem definitions source input)
    {wire : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (mappedExact : applied.rawWireImage? wire = some mapped) :
    (applied.target.val.wires mapped).sig =
      (source.val.wires wire).sig := by
  exact Reconstruction.removalSpliceWireImage_signature
    input.occurrence applied.removed applied.attachment mappedExact

def tag
    {source : CheckedDiagram definitions.signatures}
    {input : TheoremApplication (definitions := definitions) source}
    (_applied : AppliedTheorem definitions source input) : StepTag :=
  .theorem

end AppliedTheorem

/-- Check one prior-theorem citation without graph search.  The exact source
occurrence owns removal; its reconstruction attachment supplies the ordered
argument tuple for the opposite theorem side. -/
def applyTheorem
    (definitions : Definitions)
    (source : CheckedDiagram definitions.signatures)
    (input : TheoremApplication (definitions := definitions) source) :
    Except TheoremRuleError (AppliedTheorem definitions source input) := by
  match sourceCompilationAccepted : compileOpen input.sourceFragment with
      | none => exact .error .sourceCompilationRejected
      | some sourceCompilation =>
          match targetCompilationAccepted : compileOpen input.targetFragment with
          | none => exact .error .targetCompilationRejected
          | some targetCompilation =>
              match removedAccepted : remove input.occurrence with
              | .error error => exact .error (.removalRejected error)
              | .ok removed =>
                  match reconstructionAccepted :
                      reconstructionAttachment? input.occurrence removed with
                  | none => exact .error .reconstructionRejected
                  | some reconstruction =>
                      match reconstructionIsoAccepted :
                          Reconstruction.extract_splice_iso? input.occurrence
                            removed reconstruction reconstructionAccepted with
                      | none => exact .error .reconstructionIsoRejected
                      | some reconstructionIso =>
                          match reconstructionCompilationAccepted :
                              compileInsertion? sourceCompilation
                                reconstruction with
                          | none =>
                              exact .error .reconstructionCompilationRejected
                          | some reconstructionCompilation =>
                              if legal : theoremPolarityLegal input.orientation
                                  input.direction
                                  reconstructionCompilation.site.frame.context.cutDepth then
                                let target
                                    (position : Fin
                                      input.targetFragment.val.boundary.length) :
                                    removed.complement.val.WireId :=
                                  reconstruction.target
                                    (Fin.cast input.boundaryLength position)
                                match attachmentAccepted :
                                    checkConcreteSpliceAttachment
                                      removed.complement removed.site
                                      input.targetFragment target with
                                | none =>
                                    exact .error .targetAttachmentRejected
                                | some attachment =>
                                    match insertionAccepted :
                                        compileInsertion? targetCompilation
                                          attachment with
                                    | none =>
                                        exact .error
                                          .targetInsertionCompilationRejected
                                    | some insertion =>
                                        match resultAccepted : spliceRaw attachment with
                                        | .error error =>
                                            exact .error
                                              (.targetSpliceRejected error)
                                        | .ok result =>
                                            exact .ok
                                              (AppliedTheorem.mk sourceCompilation
                                                sourceCompilationAccepted
                                                targetCompilation
                                                targetCompilationAccepted removed
                                                removedAccepted reconstruction
                                                reconstructionAccepted
                                                reconstructionIso
                                                reconstructionIsoAccepted
                                                reconstructionCompilation
                                                reconstructionCompilationAccepted
                                                legal attachment
                                                (by
                                                  intro position
                                                  have exactTarget := congrFun
                                                    (checkConcreteSpliceAttachment_target
                                                      removed.complement
                                                      removed.site
                                                      input.targetFragment target
                                                      attachment
                                                      attachmentAccepted)
                                                    position
                                                  simpa [target] using exactTarget)
                                                insertion insertionAccepted
                                                result resultAccepted)
                              else
                                exact .error .illegalPolarity

end VisualProof
