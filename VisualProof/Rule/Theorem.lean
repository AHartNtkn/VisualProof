import VisualProof.Diagram.Concrete.Subgraph.FactorizationInsertion
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction
import VisualProof.Diagram.Concrete.Subgraph.Splice
import VisualProof.Rule.Orientation
import VisualProof.Rule.Tag
import VisualProof.Theory.Semantics

namespace VisualProof

universe u

/-- One already checked theorem statement with an exact ordered signature
interface.  Proof replay supplies validity in the chronological theorem layer;
rule application only consumes this statement and its exact occurrence. -/
structure RuleTheorem (definitions : List (List Sig)) where
  arguments : List Sig
  left : CheckedOpenDiagram definitions
  right : CheckedOpenDiagram definitions
  leftBoundary : checkedBoundarySigs left = arguments
  rightBoundary : checkedBoundarySigs right = arguments
  leftCompilation : OpenCompilation left
  leftCompilationAccepted : compileOpen left = some leftCompilation
  rightCompilation : OpenCompilation right
  rightCompilationAccepted : compileOpen right = some rightCompilation
  valid : ∀ (model : Model.{u})
      (definitionEnv : DefinitionEnv model.toPreModel definitions)
      (values : BoundaryEnv model.toPreModel arguments),
    denoteOpen model.toPreModel definitionEnv
        (leftBoundary ▸ leftCompilation.openDiagram) values ↔
      denoteOpen model.toPreModel definitionEnv
        (rightBoundary ▸ rightCompilation.openDiagram) values

inductive TheoremDirection
  | forward
  | reverse
  deriving Repr, DecidableEq

/-- A theorem citation pins the exact source-side occurrence. -/
inductive TheoremApplication
    (source : CheckedDiagram definitions) : Type
  | forward
      (statement : RuleTheorem.{u} definitions)
      (orientation : Orientation)
      (occurrence : Occurrence statement.left source) :
      TheoremApplication (definitions := definitions) source
  | reverse
      (statement : RuleTheorem.{u} definitions)
      (orientation : Orientation)
      (occurrence : Occurrence statement.right source) :
      TheoremApplication (definitions := definitions) source

namespace TheoremApplication

def statement {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    TheoremApplication (definitions := definitions) source →
      RuleTheorem.{u} definitions
  | .forward statement _ _ => statement
  | .reverse statement _ _ => statement

def orientation {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    TheoremApplication (definitions := definitions) source → Orientation
  | .forward _ orientation _ => orientation
  | .reverse _ orientation _ => orientation

def direction {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    TheoremApplication (definitions := definitions) source → TheoremDirection
  | .forward .. => .forward
  | .reverse .. => .reverse

def sourceFragment
    {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    TheoremApplication (definitions := definitions) source →
      CheckedOpenDiagram definitions
  | .forward statement _ _ => statement.left
  | .reverse statement _ _ => statement.right

def targetFragment
    {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    TheoremApplication (definitions := definitions) source →
      CheckedOpenDiagram definitions
  | .forward statement _ _ => statement.right
  | .reverse statement _ _ => statement.left

def occurrence
    {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    (input : TheoremApplication (definitions := definitions) source) →
      Occurrence input.sourceFragment source
  | .forward _ _ occurrence => occurrence
  | .reverse _ _ occurrence => occurrence

def sourceBoundary
    {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    (input : TheoremApplication (definitions := definitions) source) →
      checkedBoundarySigs input.sourceFragment = input.statement.arguments
  | .forward statement _ _ => statement.leftBoundary
  | .reverse statement _ _ => statement.rightBoundary

def targetBoundary
    {definitions : List (List Sig)} {source : CheckedDiagram definitions} :
    (input : TheoremApplication (definitions := definitions) source) →
      checkedBoundarySigs input.targetFragment = input.statement.arguments
  | .forward statement _ _ => statement.rightBoundary
  | .reverse statement _ _ => statement.leftBoundary

theorem boundaryLength
    {definitions : List (List Sig)} {source : CheckedDiagram definitions}
    (input : TheoremApplication (definitions := definitions) source) :
    input.targetFragment.val.boundary.length =
      input.sourceFragment.val.boundary.length := by
  have signatures := input.targetBoundary.trans input.sourceBoundary.symm
  have lengths := congrArg List.length signatures
  simpa [checkedBoundarySigs] using lengths

def site {definitions : List (List Sig)} {source : CheckedDiagram definitions}
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
  | siteCompilationRejected
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
    (source : CheckedDiagram definitions)
    (input : TheoremApplication (definitions := definitions) source) where
  private mk ::
  private siteCompilation : SiteCompilation source input.site
  private legal : theoremPolarityLegal input.orientation input.direction
    siteCompilation.frame.context.cutDepth = true
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
  private attachment : ConcreteSpliceAttachment removed.complement
    removed.site input.targetFragment
  private boundaryTargets :
    ∀ position : Fin input.targetFragment.val.boundary.length,
      attachment.target position =
        reconstruction.target (Fin.cast input.boundaryLength position)
  private insertion : InsertionCompilation targetCompilation attachment
  private insertionAccepted :
    compileInsertion? targetCompilation attachment = some insertion
  private result : ConcreteSpliceResult attachment
  private resultAccepted : splice attachment = .ok result

namespace AppliedTheorem

def source
    {source : CheckedDiagram definitions}
    {input : TheoremApplication (definitions := definitions) source}
    (_applied : AppliedTheorem source input) : CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {input : TheoremApplication (definitions := definitions) source}
    (applied : AppliedTheorem source input) : CheckedDiagram definitions :=
  applied.result.checked

def tag
    {source : CheckedDiagram definitions}
    {input : TheoremApplication (definitions := definitions) source}
    (_applied : AppliedTheorem source input) : StepTag :=
  .theorem

end AppliedTheorem

/-- Check one prior-theorem citation without graph search.  The exact source
occurrence owns removal; its reconstruction attachment supplies the ordered
argument tuple for the opposite theorem side. -/
def applyTheorem
    (source : CheckedDiagram definitions)
    (input : TheoremApplication (definitions := definitions) source) :
    Except TheoremRuleError (AppliedTheorem source input) := by
  match siteAccepted : compileSite? source input.site with
  | none => exact .error .siteCompilationRejected
  | some siteCompilation =>
      if legal : theoremPolarityLegal input.orientation input.direction
          siteCompilation.frame.context.cutDepth then
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
                                        match resultAccepted : splice attachment with
                                        | .error error =>
                                            exact .error
                                              (.targetSpliceRejected error)
                                        | .ok result =>
                                            exact .ok
                                              (AppliedTheorem.mk siteCompilation
                                                legal sourceCompilation
                                                sourceCompilationAccepted
                                                targetCompilation
                                                targetCompilationAccepted removed
                                                removedAccepted reconstruction
                                                reconstructionAccepted
                                                reconstructionIso
                                                reconstructionIsoAccepted
                                                reconstructionCompilation
                                                reconstructionCompilationAccepted
                                                attachment
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
                                                insertion
                                                insertionAccepted result
                                                resultAccepted)
      else
        exact .error .illegalPolarity

end VisualProof
