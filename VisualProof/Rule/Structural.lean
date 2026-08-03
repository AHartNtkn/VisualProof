import VisualProof.Rule.Tag
import VisualProof.Rule.Orientation
import VisualProof.Rule.IntrinsicRegionEquality
import VisualProof.Rule.Vacuous
import VisualProof.Diagram.Concrete.Subgraph.FactorizationSemantics
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction

namespace VisualProof

universe u

namespace StructuralCore

/-- Stable refusal outcomes of the concrete structural-rule checkers. -/
inductive StructuralError
  | fragmentNotStructural
  | fragmentCompilationFailed
  | siteCompilationFailed
  | attachmentRejected
  | spliceRejected (error : WFError)
  | extractionRejected (error : ExtractionError)
  | illegalCopyDestination
  | relativeFrameCompilationFailed
  | occurrenceNotPresent
  | copyBoundaryMismatch
  | illegalDeiterationJustifier
  | ancestorTransportRejected
  | removalRejected (error : WFError)
  | reconstructionRejected
  | reconstructionIsoRejected
  | anchorCopyCompilationMismatch
  | destinationCopyCompilationMismatch
  | copyTargetMismatch
  | targetMismatch
  | forwardInsertionRequiresNegative
  | backwardInsertionRequiresPositive
  | forwardErasureRequiresPositive
  | backwardErasureRequiresNegative
  deriving Repr, DecidableEq

/-- Canonical one-identity open fragment with one boundary wire per storage
port.  Repeated host attachments are represented by the insertion target,
not by collapsing this fragment's ordered port boundary. -/
def identityFragmentRaw
    (definitionCount : Nat) (signature : Sig) (arity : Nat) :
    OpenConcreteDiagram definitionCount where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := arity
      root := ⟨0, by omega⟩
      regions := fun _ => .sheet
      nodes := fun _ => .identity ⟨0, by omega⟩ signature arity
      wires := fun wire =>
        { sig := signature
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .identity wire.val⟩] } }
  boundary := Data.Finite.allFin arity

/-- A checked canonical identity fragment together with the exact construction
facts needed to attach its ordered boundary without rediscovering its shape. -/
structure CheckedIdentityFragment
    (definitions : List (List Sig)) (signature : Sig) (arity : Nat) where
  fragment : CheckedOpenDiagram definitions
  generated :
    fragment.val = identityFragmentRaw definitions.length signature arity
  boundary_length : fragment.val.boundary.length = arity

/-- Validate the canonical identity fragment through the ordinary concrete
well-formedness authority.  This is deterministic construction, not graph or
inverse search. -/
def checkIdentityFragment
    (definitions : List (List Sig)) (signature : Sig) (arity : Nat) :
    Except WFError (CheckedIdentityFragment definitions signature arity) := by
  let raw := identityFragmentRaw definitions.length signature arity
  match accepted : ConcreteDiagram.checkWellFormed definitions raw.diagram with
  | .error error => exact .error error
  | .ok checked =>
      have generated : checked.val = raw.diagram :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      let fragment : CheckedOpenDiagram definitions :=
        ⟨raw,
          { diagram := generated ▸ checked.property
            boundary_root_scoped := by
              simp [raw, identityFragmentRaw] }⟩
      exact .ok
        { fragment := fragment
          generated := rfl
          boundary_length := by
            simp [fragment, raw, identityFragmentRaw,
              Data.Finite.allFin_eq_finRange] }

/--
Concrete input for atom/ref/identity insertion.  Boundary targets are positional:
repeated positions remain repeated and ordered.
-/
structure StructuralInsertionInput
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions) where
  orientation : Orientation
  site : base.val.RegionId
  target :
    Fin fragment.val.boundary.length → base.val.WireId

private def structuralTag?
    (fragment : CheckedOpenDiagram definitions) : Option StepTag :=
  if regionCount : fragment.val.diagram.regionCount = 1 then
    if nodeCount : fragment.val.diagram.nodeCount = 1 then
      if boundaryCovers :
          fragment.val.diagram.wiresList.all
            (fun wire => decide (wire ∈ fragment.val.boundary)) then
        match fragment.val.diagram.nodes ⟨0, by omega⟩ with
        | .atom .. => some .atomSpawn
        | .ref .. => some .refSpawn
        | .identity .. => some .identityInsert
      else
        none
    else
      none
  else
    none

private def InsertionLegal (orientation : Orientation) (depth : Nat) : Prop :=
  match orientation with
  | .forward => depth % 2 = 1
  | .backward => depth % 2 = 0

/--
Opaque concrete receipt for one accepted structural insertion.  Every proof
field is derived by `checkStructuralInsertion`.
-/
structure StructuralInsertionReceipt
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralInsertionInput base fragment) where
  private mk ::
  tag : StepTag
  private fragmentCompiled : OpenCompilation fragment
  private siteCompiled : SiteCompilation base input.site
  private legal :
    InsertionLegal input.orientation siteCompiled.frame.context.cutDepth
  private attachment :
    ConcreteSpliceAttachment base input.site fragment
  private result : ConcreteSpliceResult attachment
  private resultAccepted : splice attachment = .ok result

/--
Compile the fragment and site, enforce actual cut parity, validate the ordered
attachment, and run the concrete splice.  No semantic premise is accepted.
-/
def checkStructuralInsertion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralInsertionInput base fragment) :
    Except StructuralError (StructuralInsertionReceipt input) := by
  match tagAccepted : structuralTag? fragment with
  | none => exact .error .fragmentNotStructural
  | some tag =>
      match compiledAccepted : compileOpen fragment with
      | none => exact .error .fragmentCompilationFailed
      | some fragmentCompiled =>
          match siteAccepted : compileSite? base input.site with
          | none => exact .error .siteCompilationFailed
          | some siteCompiled =>
              have acceptWith
                  (legal :
                    InsertionLegal input.orientation
                      siteCompiled.frame.context.cutDepth) :
                  Except StructuralError
                    (StructuralInsertionReceipt input) := by
                match attachmentAccepted :
                    checkConcreteSpliceAttachment base input.site fragment
                      input.target with
                | none => exact .error .attachmentRejected
                | some attachment =>
                    match resultAccepted : splice attachment with
                    | .error error =>
                        exact .error (.spliceRejected error)
                    | .ok result =>
                        exact .ok
                          (StructuralInsertionReceipt.mk tag
                            fragmentCompiled siteCompiled legal attachment
                            result resultAccepted)
              cases orientation : input.orientation with
              | forward =>
                  if gate :
                      siteCompiled.frame.context.cutDepth % 2 = 1 then
                    exact acceptWith (by
                      simpa [InsertionLegal, orientation] using gate)
                  else
                    exact .error .forwardInsertionRequiresNegative
              | backward =>
                  if gate :
                      siteCompiled.frame.context.cutDepth % 2 = 0 then
                    exact acceptWith (by
                      simpa [InsertionLegal, orientation] using gate)
                  else
                    exact .error .backwardInsertionRequiresPositive

namespace StructuralInsertionReceipt

/-- The checked diagram before insertion. -/
def source
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (_checked : StructuralInsertionReceipt input) :
    CheckedDiagram definitions :=
  base

/-- The checked raw concrete splice result.  Identity normalization is a
separate downstream mechanism, not part of the structural primitive. -/
def target
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    CheckedDiagram definitions :=
  checked.result.raw

/-- The exact checked splice candidate produced by the primitive. -/
def rawTarget
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    CheckedDiagram definitions :=
  checked.result.raw

/-- Exact raw image of one pre-insertion region. -/
def rawHostRegion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (region : base.val.RegionId) : checked.target.val.RegionId :=
  checked.attachment.hostRegion region

/-- Exact raw image of one pre-insertion node. -/
def rawHostNode
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (node : base.val.NodeId) : checked.target.val.NodeId :=
  checked.attachment.hostNode node

/-- Exact raw image of one pre-insertion wire. -/
def rawHostWire
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (wire : base.val.WireId) : checked.target.val.WireId :=
  checked.attachment.hostWire wire

/-- Exact raw image of one inserted fragment node. -/
def rawFragmentNode
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (node : fragment.val.diagram.NodeId) : checked.target.val.NodeId :=
  checked.attachment.fragmentNode node

theorem rawHostNode_injective
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    Function.Injective checked.rawHostNode := by
  intro left right same
  apply Fin.ext
  simpa [rawHostNode, ConcreteSpliceAttachment.hostNode] using
    congrArg Fin.val same

theorem rawHostNode_ne_rawFragmentNode
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (host : base.val.NodeId)
    (inserted : fragment.val.diagram.NodeId) :
    checked.rawHostNode host ≠ checked.rawFragmentNode inserted :=
  checked.attachment.hostNode_ne_fragmentNode host inserted

/--
A checked splice into a negative context is sound in the insertion direction.
This is the direct negative-splice theorem used by backward erasure; it does
not derive that case by reversing positive erasure.
-/
theorem negative_splice_sound
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (forward : input.orientation = .forward)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv checked.source →
      denoteChecked pre definitionEnv checked.target := by
  obtain ⟨compiled, _compiledAccepted⟩ :=
    compileInsertion_complete_of_raw_splice checked.fragmentCompiled
      checked.attachment checked.result.rawResult
      (splice_success_raw checked.resultAccepted)
  have targetDenotes :
      denoteChecked pre definitionEnv checked.target ↔
        denoteRegion pre definitionEnv Env.empty compiled.inserted := by
    simpa [StructuralInsertionReceipt.target, ConcreteSpliceResult.raw,
      RawConcreteSpliceResult.checked] using
      compiled.generated_checked_denotes_inserted pre definitionEnv
  have sameSite :=
    SiteCompilation.unique compiled.site checked.siteCompiled
  have sameDepth :
      compiled.site.frame.context.cutDepth =
        checked.siteCompiled.frame.context.cutDepth :=
    congrArg (fun site => site.frame.context.cutDepth) sameSite
  have sourceDenotes :
      denoteChecked pre definitionEnv base ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody) := by
    rw [elaborate_denotes_checked]
    change
      denoteRegion pre definitionEnv Env.empty (elaborate base) ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody)
    rw [compiled.site.frame_fills_checked]
    rfl
  have contraction :
      ∀ localEnv : Env pre compiled.site.frame.visible.sigs,
        denoteRegion pre definitionEnv localEnv
            (Region.conjoin compiled.site.frame.siteBody
              (intrinsicSplice checked.fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)) →
          denoteRegion pre definitionEnv localEnv
            compiled.site.frame.siteBody := by
    intro localEnv inserted
    exact
      (Region.denote_conjoin pre definitionEnv localEnv
        compiled.site.frame.siteBody
        (intrinsicSplice checked.fragmentCompiled.openDiagram
          compiled.intrinsicAttachment)).mp inserted |>.1
  have odd :
      compiled.site.frame.context.cutDepth % 2 = 1 := by
    rw [sameDepth]
    simpa [InsertionLegal, forward] using checked.legal
  intro sourceHolds
  apply targetDenotes.mpr
  change
    denoteRegion pre definitionEnv Env.empty
      (compiled.site.frame.context.fill
        (Region.conjoin compiled.site.frame.siteBody
          (intrinsicSplice checked.fragmentCompiled.openDiagram
            compiled.intrinsicAttachment)))
  exact
    context_anti compiled.site.frame.context pre definitionEnv
      (Region.conjoin compiled.site.frame.siteBody
        (intrinsicSplice checked.fragmentCompiled.openDiagram
          compiled.intrinsicAttachment))
      compiled.site.frame.siteBody odd contraction Env.empty
      (sourceDenotes.mp sourceHolds)

/-- Accepted concrete insertion has exactly its checked orientation. -/
theorem sound
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) := by
  obtain ⟨compiled, _compiledAccepted⟩ :=
    compileInsertion_complete_of_raw_splice checked.fragmentCompiled
      checked.attachment checked.result.rawResult
      (splice_success_raw checked.resultAccepted)
  have targetDenotes :
      denoteChecked pre definitionEnv checked.target ↔
        denoteRegion pre definitionEnv Env.empty compiled.inserted := by
    simpa [StructuralInsertionReceipt.target, ConcreteSpliceResult.raw,
      RawConcreteSpliceResult.checked] using
      compiled.generated_checked_denotes_inserted pre definitionEnv
  have sameSite :=
    SiteCompilation.unique compiled.site checked.siteCompiled
  have sameDepth :
      compiled.site.frame.context.cutDepth =
        checked.siteCompiled.frame.context.cutDepth :=
    congrArg (fun site => site.frame.context.cutDepth) sameSite
  have sourceDenotes :
      denoteChecked pre definitionEnv base ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody) := by
    rw [elaborate_denotes_checked]
    change
      denoteRegion pre definitionEnv Env.empty (elaborate base) ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody)
    rw [compiled.site.frame_fills_checked]
    rfl
  have contraction :
      ∀ localEnv : Env pre compiled.site.frame.visible.sigs,
        denoteRegion pre definitionEnv localEnv
            (Region.conjoin compiled.site.frame.siteBody
              (intrinsicSplice checked.fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)) →
          denoteRegion pre definitionEnv localEnv
            compiled.site.frame.siteBody := by
    intro localEnv inserted
    exact
      (Region.denote_conjoin pre definitionEnv localEnv
        compiled.site.frame.siteBody
        (intrinsicSplice checked.fragmentCompiled.openDiagram
          compiled.intrinsicAttachment)).mp inserted |>.1
  cases orientation : input.orientation with
  | forward =>
      exact negative_splice_sound checked orientation pre definitionEnv
  | backward =>
      have even :
          compiled.site.frame.context.cutDepth % 2 = 0 := by
        rw [sameDepth]
        simpa [InsertionLegal, orientation] using checked.legal
      intro targetHolds
      apply sourceDenotes.mpr
      apply
        context_mono compiled.site.frame.context pre definitionEnv
          (Region.conjoin compiled.site.frame.siteBody
            (intrinsicSplice checked.fragmentCompiled.openDiagram
              compiled.intrinsicAttachment))
          compiled.site.frame.siteBody even contraction Env.empty
      have inserted := targetDenotes.mp targetHolds
      change
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            (Region.conjoin compiled.site.frame.siteBody
              (intrinsicSplice checked.fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)))
      exact inserted

end StructuralInsertionReceipt

/--
Concrete erasure input names the exact structural fragment and ordered
attachment whose already-spliced result is to be contracted.
-/
structure StructuralErasureInput
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions) where
  orientation : Orientation
  site : base.val.RegionId
  target :
    Fin fragment.val.boundary.length → base.val.WireId

namespace StructuralErasureInput

private def asOppositeInsertion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralErasureInput base fragment) :
    StructuralInsertionInput base fragment where
  orientation :=
    match input.orientation with
    | .forward => .backward
    | .backward => .forward
  site := input.site
  target := input.target

end StructuralErasureInput

namespace StructuralInsertionReceipt

/-- The exact opposite-orientation erasure input for this accepted insertion. -/
def inverseErasureInput
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (_checked : StructuralInsertionReceipt input) :
    StructuralErasureInput base fragment where
  orientation :=
    match input.orientation with
    | .forward => .backward
    | .backward => .forward
  site := input.site
  target := input.target

end StructuralInsertionReceipt

/-- Opaque receipt for erasure at the orientation-flipped legal polarity. -/
structure StructuralErasureReceipt
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralErasureInput base fragment) where
  private mk ::
  private inserted :
    StructuralInsertionReceipt input.asOppositeInsertion

/-- Check erasure by checking insertion in the opposite orientation. -/
def checkStructuralErasure
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralErasureInput base fragment) :
    Except StructuralError (StructuralErasureReceipt input) := by
  match accepted :
      checkStructuralInsertion input.asOppositeInsertion with
  | .ok checked =>
      exact .ok (StructuralErasureReceipt.mk checked)
  | .error .backwardInsertionRequiresPositive =>
      exact .error .forwardErasureRequiresPositive
  | .error .forwardInsertionRequiresNegative =>
      exact .error .backwardErasureRequiresNegative
  | .error error =>
      exact .error error

namespace StructuralErasureReceipt

/-- Read an accepted insertion as its exact opposite-orientation erasure. -/
def ofInsertion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    StructuralErasureReceipt checked.inverseErasureInput := by
  refine StructuralErasureReceipt.mk ?_
  have exactInput :
      checked.inverseErasureInput.asOppositeInsertion = input := by
    cases input with
    | mk orientation site target => cases orientation <;> rfl
  rw [exactInput]
  exact checked

/-- The structural constructor removed by this erasure. -/
def insertedTag
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralErasureInput base fragment}
    (checked : StructuralErasureReceipt input) : StepTag :=
  checked.inserted.tag

def tag
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralErasureInput base fragment}
    (_checked : StructuralErasureReceipt input) : StepTag :=
  .erasure

/-- Erasure starts from the concrete splice result. -/
def source
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralErasureInput base fragment}
    (checked : StructuralErasureReceipt input) :
    CheckedDiagram definitions :=
  checked.inserted.target

/-- Erasure returns the checked base diagram. -/
def target
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralErasureInput base fragment}
    (checked : StructuralErasureReceipt input) :
    CheckedDiagram definitions :=
  checked.inserted.source

@[simp] theorem ofInsertion_source
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    (ofInsertion checked).source = checked.target := by
  cases input with
  | mk orientation site target => cases orientation <;> rfl

@[simp] theorem ofInsertion_target
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    (ofInsertion checked).target = checked.source := by
  cases input with
  | mk orientation site target => cases orientation <;> rfl

@[simp] theorem ofInsertion_insertedTag
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : StructuralInsertionReceipt input) :
    (ofInsertion checked).insertedTag = checked.tag := by
  cases input with
  | mk orientation site target => cases orientation <;> rfl

/--
Erasure is the checked opposite-orientation reading of the same splice.
Backward erasure cites `negative_splice_sound` directly.
-/
theorem sound
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralErasureInput base fragment}
    (checked : StructuralErasureReceipt input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) := by
  cases orientation : input.orientation with
  | forward =>
      simpa [Directed, StructuralErasureInput.asOppositeInsertion, orientation] using
        checked.inserted.sound pre definitionEnv
  | backward =>
      have negative :=
        StructuralInsertionReceipt.negative_splice_sound checked.inserted
          (by
            simp [StructuralErasureInput.asOppositeInsertion, orientation])
          pre definitionEnv
      simpa [Directed] using negative

end StructuralErasureReceipt

namespace WireRenaming

private def weaken (bound : Sig) : WireRenaming ctx (bound :: ctx) :=
  fun {_} wire => .there wire

end WireRenaming

private theorem weakened_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (value : pre.Domain sig)
    (body : Region definitions ctx) :
    denoteRegion pre definitionEnv (env.extend value)
        (body.renameWires (WireRenaming.weaken sig)) ↔
      denoteRegion pre definitionEnv env body := by
  rw [denoteRegion_renameWires]
  have environmentsEqual :
      Env.comp (env.extend value) (WireRenaming.weaken sig) = env := by
    funext signature wire
    rfl
  rw [environmentsEqual]

private def doubleCut (body : Region definitions ctx) :
    Region definitions ctx :=
  .mk (.cons (.cut (.mk (.cons (.cut body) .nil))) .nil)

private theorem denote_doubleCut
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (body : Region definitions ctx) :
    denoteRegion pre definitionEnv env (doubleCut body) ↔
      denoteRegion pre definitionEnv env body := by
  change
    (¬ ((¬ denoteRegion pre definitionEnv env body) ∧ True)) ∧ True ↔
      denoteRegion pre definitionEnv env body
  constructor
  · rintro ⟨doubleNegated, _⟩
    exact Classical.byContradiction fun denied =>
      doubleNegated ⟨denied, trivial⟩
  · intro bodyDenotes
    exact
      ⟨fun inner => inner.1 bodyDenotes, trivial⟩

/--
Concrete double-cut input supplies both checked endpoints and the exact site in
the plain endpoint.  The checker compares the doubled endpoint with the
compiler-derived transformation.
-/
structure DoubleCutInput
    (plain doubled : CheckedDiagram definitions) where
  site : plain.val.RegionId

/-- Opaque receipt shared by double-cut introduction and elimination. -/
structure CheckedDoubleCut
    {plain doubled : CheckedDiagram definitions}
    (input : DoubleCutInput plain doubled) where
  private mk ::
  private siteCompiled : SiteCompilation plain input.site
  private exact :
    elaborate doubled =
      siteCompiled.frame.context.fill
        (doubleCut siteCompiled.frame.siteBody)

/-- Executably validate the exact compiler-level double-cut transformation. -/
def checkDoubleCut
    {plain doubled : CheckedDiagram definitions}
    (input : DoubleCutInput plain doubled) :
    Except StructuralError (CheckedDoubleCut input) := by
  match siteAccepted : compileSite? plain input.site with
  | none => exact .error .siteCompilationFailed
  | some siteCompiled =>
      if exact :
          intrinsicRegionsEqual (elaborate doubled)
              (siteCompiled.frame.context.fill
                (doubleCut siteCompiled.frame.siteBody)) = true then
        exact .ok
          (CheckedDoubleCut.mk siteCompiled
            (intrinsicRegionsEqual_sound exact))
      else
        exact .error .targetMismatch

namespace CheckedDoubleCut

def plain
    {plainDiagram doubled : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubled}
    (_checked : CheckedDoubleCut input) :
    CheckedDiagram definitions :=
  plainDiagram

def doubled
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (_checked : CheckedDoubleCut input) :
    CheckedDiagram definitions :=
  doubledDiagram

def introTag
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (_checked : CheckedDoubleCut input) : StepTag :=
  .doubleCutIntro

def elimTag
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (_checked : CheckedDoubleCut input) : StepTag :=
  .doubleCutElim

theorem equivalence
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (checked : CheckedDoubleCut input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv checked.plain ↔
      denoteChecked pre definitionEnv checked.doubled := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked,
    CheckedDoubleCut.plain, CheckedDoubleCut.doubled]
  rw [checked.exact]
  have fills :
      checked.siteCompiled.frame.context.fill
          checked.siteCompiled.frame.siteBody =
        elaborate plainDiagram := by
    simpa [SiteCompilation.checked] using
      checked.siteCompiled.frame_fills_checked
  rw [← fills]
  exact
    context_equiv checked.siteCompiled.frame.context pre definitionEnv
      checked.siteCompiled.frame.siteBody
      (doubleCut checked.siteCompiled.frame.siteBody)
      (fun env =>
        (denote_doubleCut pre definitionEnv env
          checked.siteCompiled.frame.siteBody).symm)
      Env.empty

theorem intro_sound
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (checked : CheckedDoubleCut input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.plain)
      (denoteChecked pre definitionEnv checked.doubled) :=
  (checked.equivalence pre definitionEnv).mp

theorem elim_sound
    {plainDiagram doubledDiagram : CheckedDiagram definitions}
    {input : DoubleCutInput plainDiagram doubledDiagram}
    (checked : CheckedDoubleCut input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.doubled)
      (denoteChecked pre definitionEnv checked.plain) :=
  (checked.equivalence pre definitionEnv).mpr

end CheckedDoubleCut


private def itemSeqItems :
    ItemSeq definitions ctx → List (Item definitions ctx)
  | .nil => []
  | .cons head tail => head :: itemSeqItems tail

private theorem itemSeq_denotes_of_mem
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx) :
    (whole : ItemSeq definitions ctx) →
      (item : Item definitions ctx) →
      item ∈ itemSeqItems whole →
      denoteItemSeq pre definitionEnv env whole →
      denoteItem pre definitionEnv env item
  | .nil, item, member, _ => by
      simp [itemSeqItems] at member
  | .cons head tail, item, member, wholeDenotes => by
      simp only [itemSeqItems, List.mem_cons] at member
      simp only [denoteItemSeq_cons] at wholeDenotes
      rcases member with same | tailMember
      · subst item
        exact wholeDenotes.1
      · exact
          itemSeq_denotes_of_mem pre definitionEnv env tail item
            tailMember wholeDenotes.2

open IntrinsicEquality in
private def itemsContained
    (whole selected : ItemSeq definitions ctx) : Bool :=
  (itemSeqItems selected).all fun item =>
    decide (item ∈ itemSeqItems whole)

open IntrinsicEquality in
private theorem itemsContained_sound
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (whole : ItemSeq definitions ctx) :
    (selected : ItemSeq definitions ctx) →
      itemsContained whole selected = true →
      denoteItemSeq pre definitionEnv env whole →
      denoteItemSeq pre definitionEnv env selected
  | .nil, _, _ => trivial
  | .cons head tail, accepted, wholeDenotes => by
      have split :
          decide (head ∈ itemSeqItems whole) = true ∧
            itemsContained whole tail = true := by
        simpa [itemsContained, itemSeqItems] using accepted
      exact
        ⟨itemSeq_denotes_of_mem pre definitionEnv env whole head
            (of_decide_eq_true split.1) wholeDenotes,
          itemsContained_sound pre definitionEnv env whole tail split.2
            wholeDenotes⟩

open IntrinsicEquality in
private def regionContained
    (whole selected : Region definitions ctx) : Bool :=
  match whole, selected with
  | .mk wholeItems, .mk selectedItems =>
      itemsContained wholeItems selectedItems

open IntrinsicEquality in
private theorem regionContained_sound
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (whole selected : Region definitions ctx)
    (accepted : regionContained whole selected = true)
    (wholeDenotes : denoteRegion pre definitionEnv env whole) :
    denoteRegion pre definitionEnv env selected := by
  cases whole with
  | mk wholeItems =>
      cases selected with
      | mk selectedItems =>
          exact
            itemsContained_sound pre definitionEnv env wholeItems
              selectedItems accepted wholeDenotes

/--
Compile the concrete frame strictly below an already compiled anchor.  The
caller supplies only the destination; the enclosure path is selected by the
same deterministic child search as the ordinary site compiler.
-/
private def compileRelativeFrame?
    (base : CheckedDiagram definitions)
    (anchor destination : base.val.RegionId)
    (anchorCompiled : SiteCompilation base anchor) :
    Option
      (RegionFrame definitions base.val anchorCompiled.frame.visible) := by
  if same : anchor = destination then
    exact some
      { visible := anchorCompiled.frame.visible
        siteBody := anchorCompiled.frame.siteBody
        context := .hole }
  else
    exact do
      let outer := anchorCompiled.frame.visible
      let fuel := base.val.regionCount
      let nodes ←
        ConcreteElaboration.compileNodes? definitions base.val outer
          (base.val.nodesAt anchor)
      let child ←
        (base.val.childrenOf anchor).find?
          (fun candidate => decide (base.val.Encloses candidate destination))
      let nested ←
        compileRegionFrame? definitions base.val destination
          (fuel + 1) child outer
      compileSiblingFrame? definitions base.val fuel outer child nested
        nodes (base.val.childrenOf anchor)

private def iterateInto :
    {hole outer : List Sig} →
      DiagramContext definitions hole outer →
      Region definitions outer →
      Region definitions hole →
      Region definitions outer
  | _, _, .hole, truth, body =>
      Region.conjoin body truth
  | _, _, .surround leading inner suffix, truth, body =>
      Region.surround leading (iterateInto inner truth body) suffix
  | _, _, .cut inner, truth, body =>
      .mk (.cons (.cut (iterateInto inner truth body)) .nil)
  | _, _, .bind sig inner, truth, body =>
      .mk (.cons (.bind sig
        (iterateInto inner
          (truth.renameWires (WireRenaming.weaken sig)) body)) .nil)

private theorem denote_iterateInto
    (context : DiagramContext definitions hole outer)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre outer)
    (truth : Region definitions outer)
    (body : Region definitions hole)
    (truthDenotes : denoteRegion pre definitionEnv env truth) :
    denoteRegion pre definitionEnv env
        (iterateInto context truth body) ↔
      denoteRegion pre definitionEnv env (context.fill body) := by
  induction context with
  | hole =>
      rw [iterateInto, Region.denote_conjoin]
      exact and_iff_left truthDenotes
  | surround leading inner suffix induction =>
      rw [iterateInto, DiagramContext.fill, Region.denote_surround,
        Region.denote_surround]
      exact and_congr Iff.rfl
        (and_congr
          (induction env truth body truthDenotes)
          Iff.rfl)
  | cut inner induction =>
      simp only [iterateInto, DiagramContext.fill, denoteRegion,
        denoteItemSeq, denoteItem, and_true]
      exact not_congr (induction env truth body truthDenotes)
  | bind sig inner induction =>
      simp only [iterateInto, DiagramContext.fill, denoteRegion,
        denoteItemSeq, denoteItem, and_true]
      apply exists_congr
      intro value
      apply induction (env.extend value)
      exact
        (weakened_denotes pre definitionEnv env value truth).mpr
          truthDenotes

private def occurrenceTarget
    (occurrence : Occurrence pattern host) :
    Fin pattern.val.boundary.length → host.val.WireId :=
  fun position =>
    occurrence.boundaryAttachments.get
      ⟨position.val, by
        rw [occurrence.boundaryAttachments_length]
        exact position.isLt⟩

private def copyTruth
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (extraction : CheckedExtraction selection occurrence)
    (anchorCompiled : SiteCompilation host selection.region)
    (anchorAttachment :
      ConcreteSpliceAttachment host selection.region pattern)
    (anchorInsertion :
      InsertionCompilation extraction.compilation anchorAttachment) :
    Region definitions anchorCompiled.frame.visible.sigs :=
  intrinsicSplice extraction.compilation.openDiagram
    (anchorInsertion.intrinsicAttachmentAt anchorCompiled)

/-- Exact raw input for ordinary iteration; no occurrence is searched. -/
structure OrdinaryIterationInput
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (selection : CheckedSelection host)
    (occurrence : Occurrence pattern host) where
  destination : host.val.RegionId

/-- Opaque ordinary-iteration receipt. -/
structure CheckedOrdinaryIteration
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (input : OrdinaryIterationInput selection occurrence) where
  private mk ::
  private extraction : CheckedExtraction selection occurrence
  private anchorCompiled : SiteCompilation host selection.region
  private relative :
    RegionFrame definitions host.val anchorCompiled.frame.visible
  private relativeFills :
    relative.context.fill relative.siteBody =
      anchorCompiled.frame.siteBody
  private anchorAttachment :
    ConcreteSpliceAttachment host selection.region pattern
  private anchorInsertion :
    InsertionCompilation extraction.compilation anchorAttachment
  private sourceContains :
    regionContained anchorCompiled.frame.siteBody
      (copyTruth extraction anchorCompiled anchorAttachment
        anchorInsertion) = true
  private destinationAttachment :
    ConcreteSpliceAttachment host input.destination pattern
  private result : ConcreteSpliceResult destinationAttachment
  private resultAccepted :
    splice destinationAttachment = .ok result
  private destinationInsertion :
    InsertionCompilation extraction.compilation destinationAttachment
  private destinationInsertionAccepted :
    compileInsertion? extraction.compilation destinationAttachment =
      some destinationInsertion
  private targetExact :
    destinationInsertion.inserted =
      anchorCompiled.frame.context.fill
        (iterateInto relative.context
          (copyTruth extraction anchorCompiled anchorAttachment
            anchorInsertion)
          relative.siteBody)
  private targetContains :
    regionContained
      (iterateInto relative.context
        (copyTruth extraction anchorCompiled anchorAttachment
          anchorInsertion)
        relative.siteBody)
      (copyTruth extraction anchorCompiled anchorAttachment
        anchorInsertion) = true

/--
Check exact extraction, legal same/descendant destination outside the selected
content, ordered attachments, both factorization views, and the concrete
splice.  The intrinsic equalities are computed from those receipts.
-/
def checkOrdinaryIteration
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (input : OrdinaryIterationInput selection occurrence) :
    Except StructuralError (CheckedOrdinaryIteration input) := by
  match extractionAccepted : checkExtraction selection occurrence with
  | .error error => exact .error (.extractionRejected error)
  | .ok extraction =>
      if legal :
          host.val.Encloses selection.region input.destination ∧
            input.destination ∉ selection.allRegions then
        match anchorAccepted :
            compileSite? host selection.region with
        | none => exact .error .siteCompilationFailed
        | some anchorCompiled =>
            match relativeAccepted :
                compileRelativeFrame? host selection.region
                  input.destination anchorCompiled with
            | none => exact .error .relativeFrameCompilationFailed
            | some relative =>
                if relativeExact :
                    intrinsicRegionsEqual
                      (relative.context.fill relative.siteBody)
                      anchorCompiled.frame.siteBody = true then
                  match anchorAttachmentAccepted :
                      checkConcreteSpliceAttachment host selection.region
                        pattern (occurrenceTarget occurrence) with
                  | none => exact .error .attachmentRejected
                  | some anchorAttachment =>
                      match anchorResultAccepted :
                          splice anchorAttachment with
                      | .error error =>
                          exact .error (.spliceRejected error)
                      | .ok _anchorResult =>
                          match anchorInsertionAccepted :
                              compileInsertion? extraction.compilation
                                anchorAttachment with
                          | none =>
                              exact .error .anchorCopyCompilationMismatch
                          | some anchorInsertion =>
                              let truth :=
                                copyTruth extraction anchorCompiled
                                  anchorAttachment anchorInsertion
                              if sourceContains :
                                  regionContained
                                    anchorCompiled.frame.siteBody truth =
                                      true then
                                match destinationAttachmentAccepted :
                                    checkConcreteSpliceAttachment host
                                      input.destination pattern
                                      (occurrenceTarget occurrence) with
                                | none =>
                                    exact .error .attachmentRejected
                                | some destinationAttachment =>
                                    match resultAccepted :
                                        splice destinationAttachment with
                                    | .error error =>
                                        exact .error
                                          (.spliceRejected error)
                                    | .ok result =>
                                        match destinationCompiledAccepted :
                                            compileInsertion?
                                              extraction.compilation
                                              destinationAttachment with
                                        | none =>
                                            exact .error
                                              .destinationCopyCompilationMismatch
                                        | some destinationInsertion =>
                                            let expected :=
                                              anchorCompiled.frame.context.fill
                                                (iterateInto relative.context
                                                  truth relative.siteBody)
                                            if targetExact :
                                                intrinsicRegionsEqual
                                                  destinationInsertion.inserted
                                                  expected = true then
                                              if targetContains :
                                                  regionContained
                                                    (iterateInto
                                                      relative.context truth
                                                      relative.siteBody)
                                                    truth = true then
                                                exact .ok
                                                  (CheckedOrdinaryIteration.mk
                                                    extraction anchorCompiled
                                                    relative
                                                    (intrinsicRegionsEqual_sound
                                                      relativeExact)
                                                    anchorAttachment
                                                    anchorInsertion
                                                    sourceContains
                                                    destinationAttachment
                                                    result resultAccepted
                                                    destinationInsertion
                                                    destinationCompiledAccepted
                                                    (intrinsicRegionsEqual_sound
                                                      targetExact)
                                                    targetContains)
                                              else
                                                exact .error
                                                  .occurrenceNotPresent
                                            else
                                              exact .error
                                                .copyTargetMismatch
                              else
                                exact .error .occurrenceNotPresent
                else
                  exact .error .relativeFrameCompilationFailed
      else
        exact .error .illegalCopyDestination

namespace CheckedOrdinaryIteration

def tag
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {input : OrdinaryIterationInput selection occurrence}
    (_checked : CheckedOrdinaryIteration input) : StepTag :=
  .iteration

def source
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {input : OrdinaryIterationInput selection occurrence}
    (_checked : CheckedOrdinaryIteration input) :
    CheckedDiagram definitions :=
  host

def target
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {input : OrdinaryIterationInput selection occurrence}
    (checked : CheckedOrdinaryIteration input) :
    CheckedDiagram definitions :=
  checked.result.checked

theorem equivalence
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {input : OrdinaryIterationInput selection occurrence}
    (checked : CheckedOrdinaryIteration input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv host ↔
      denoteChecked pre definitionEnv checked.result.checked := by
  let truth :=
    copyTruth checked.extraction checked.anchorCompiled
      checked.anchorAttachment checked.anchorInsertion
  let copied :=
    iterateInto checked.relative.context truth checked.relative.siteBody
  have localEquivalent :
      ∀ env : Env pre checked.anchorCompiled.frame.visible.sigs,
        denoteRegion pre definitionEnv env
            checked.anchorCompiled.frame.siteBody ↔
          denoteRegion pre definitionEnv env copied := by
    intro env
    constructor
    · intro sourceDenotes
      have truthDenotes :
          denoteRegion pre definitionEnv env truth :=
        regionContained_sound pre definitionEnv env
          checked.anchorCompiled.frame.siteBody truth
          checked.sourceContains sourceDenotes
      apply
        (denote_iterateInto checked.relative.context pre definitionEnv
          env truth checked.relative.siteBody truthDenotes).mpr
      rw [checked.relativeFills]
      exact sourceDenotes
    · intro targetDenotes
      have truthDenotes :
          denoteRegion pre definitionEnv env truth :=
        regionContained_sound pre definitionEnv env copied truth
          checked.targetContains targetDenotes
      have original :=
        (denote_iterateInto checked.relative.context pre definitionEnv
          env truth checked.relative.siteBody truthDenotes).mp
          targetDenotes
      rw [checked.relativeFills] at original
      exact original
  have framed :
      denoteChecked pre definitionEnv host ↔
        denoteRegion pre definitionEnv Env.empty
          (checked.anchorCompiled.frame.context.fill copied) := by
    rw [elaborate_denotes_checked]
    have fills :
        checked.anchorCompiled.frame.context.fill
            checked.anchorCompiled.frame.siteBody =
          elaborate host := by
      simpa [SiteCompilation.checked] using
        checked.anchorCompiled.frame_fills_checked
    rw [← fills]
    exact
      context_equiv checked.anchorCompiled.frame.context pre definitionEnv
        checked.anchorCompiled.frame.siteBody copied localEquivalent
        Env.empty
  obtain ⟨compiled, compiledAccepted, resultDenotes⟩ :=
    denote_splice checked.extraction.compilation
      checked.destinationAttachment checked.result checked.resultAccepted
      pre definitionEnv
  have sameCompilation :
      compiled = checked.destinationInsertion :=
    Option.some.inj
      (compiledAccepted.symm.trans
        checked.destinationInsertionAccepted)
  subst compiled
  exact framed.trans
    ((Iff.of_eq (congrArg
      (denoteRegion pre definitionEnv Env.empty) checked.targetExact.symm)).trans
      resultDenotes.symm)

theorem sound
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {input : OrdinaryIterationInput selection occurrence}
    (checked : CheckedOrdinaryIteration input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) := by
  exact (checked.equivalence pre definitionEnv).mp

end CheckedOrdinaryIteration

/-!
Ordinary deiteration is removal, not direction-reversed iteration.  The source
already contains both named occurrences.  The checker removes the inner one,
derives the surviving ancestor occurrence in the complement, and validates the
exact reconstruction splice.
-/

private def listsDisjoint [DecidableEq α]
    (left right : List α) : Bool :=
  left.all fun value => decide (value ∉ right)

private def DeiterationSeparated
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (inner justifier : CheckedSelection source) : Prop :=
  inner.region ≠ justifier.region ∧
    source.val.Encloses justifier.region inner.region ∧
    inner.region ∉ justifier.allRegions ∧
    listsDisjoint inner.allRegions justifier.allRegions = true ∧
    listsDisjoint inner.allNodes justifier.allNodes = true ∧
    listsDisjoint inner.internalWires justifier.internalWires = true

private def deiterationSeparatedCheck
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (inner justifier : CheckedSelection source) : Bool :=
  decide (inner.region ≠ justifier.region) &&
    decide (source.val.Encloses justifier.region inner.region) &&
    decide (inner.region ∉ justifier.allRegions) &&
    listsDisjoint inner.allRegions justifier.allRegions &&
    listsDisjoint inner.allNodes justifier.allNodes &&
    listsDisjoint inner.internalWires justifier.internalWires

private theorem deiterationSeparatedCheck_sound
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (inner justifier : CheckedSelection source)
    (accepted : deiterationSeparatedCheck inner justifier = true) :
    DeiterationSeparated inner justifier := by
  simp only [deiterationSeparatedCheck, Bool.and_eq_true] at accepted
  rcases accepted with
    ⟨⟨⟨⟨⟨different, encloses⟩, outside⟩, regions⟩, nodes⟩, wires⟩
  exact
    ⟨of_decide_eq_true different, of_decide_eq_true encloses,
      of_decide_eq_true outside, regions, nodes, wires⟩

private def AncestorRetained
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (inner justifier : Occurrence pattern source) : Prop :=
  (∀ region,
    justifier.regionMap region ∈ Removal.regions inner) ∧
  (∀ node,
    justifier.nodeMap node ∈ Removal.nodes inner) ∧
  (∀ wire,
    justifier.wireMap wire ∈ Removal.wires inner)

private def ancestorRetainedCheck
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (inner justifier : Occurrence pattern source) : Bool :=
  pattern.val.diagram.regionsList.all (fun region =>
      decide (justifier.regionMap region ∈ Removal.regions inner)) &&
    pattern.val.diagram.nodesList.all (fun node =>
      decide (justifier.nodeMap node ∈ Removal.nodes inner)) &&
    pattern.val.diagram.wiresList.all (fun wire =>
      decide (justifier.wireMap wire ∈ Removal.wires inner))

private theorem ancestorRetainedCheck_sound
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (inner justifier : Occurrence pattern source)
    (accepted : ancestorRetainedCheck inner justifier = true) :
    AncestorRetained inner justifier := by
  simp only [ancestorRetainedCheck, Bool.and_eq_true] at accepted
  rcases accepted with ⟨⟨regionsAccepted, nodesAccepted⟩, wiresAccepted⟩
  refine ⟨?_, ?_, ?_⟩
  · intro region
    exact of_decide_eq_true
      (List.all_eq_true.mp regionsAccepted region
        (Data.Finite.mem_allFin region))
  · intro node
    exact of_decide_eq_true
      (List.all_eq_true.mp nodesAccepted node
        (Data.Finite.mem_allFin node))
  · intro wire
    exact of_decide_eq_true
      (List.all_eq_true.mp wiresAccepted wire
        (Data.Finite.mem_allFin wire))

private def transportedAncestorInput
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (inner justifier : Occurrence pattern source)
    (removed : RemovalResult inner)
    (retained : AncestorRetained inner justifier) :
    OccurrenceInput pattern removed.complement := by
  have anchorRetained :
      justifier.region ∈ Removal.regions inner := by
    have rootRetained := retained.1 pattern.val.diagram.root
    simpa [justifier.maps_root] using rootRetained
  exact
    { region :=
        Removal.regionIndex inner justifier.region anchorRetained
      regionMap := fun region =>
        Removal.regionIndex inner (justifier.regionMap region)
          (retained.1 region)
      nodeMap := fun node =>
        Removal.nodeIndex inner (justifier.nodeMap node)
          (retained.2.1 node)
      wireMap := fun wire =>
        Removal.wireIndex inner (justifier.wireMap wire)
          (retained.2.2 wire) }

/--
Exact deiteration input.  Both occurrences belong to the actual source; the
inner selection identifies what is removed and the justifier selection
identifies the required strict ancestor copy.
-/
structure OrdinaryDeiterationInput
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (innerSelection : CheckedSelection source)
    (inner : Occurrence pattern source)
    (justifierSelection : CheckedSelection source)
    (justifier : Occurrence pattern source) where

/-- Opaque receipt for checker-owned ordinary-copy removal. -/
structure CheckedOrdinaryDeiteration
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection source}
    {inner : Occurrence pattern source}
    {justifierSelection : CheckedSelection source}
    {justifier : Occurrence pattern source}
    (input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier) where
  private mk ::
  private innerExtraction :
    CheckedExtraction innerSelection inner
  private justifierExtraction :
    CheckedExtraction justifierSelection justifier
  private separated :
    DeiterationSeparated innerSelection justifierSelection
  private boundaryExact :
    inner.boundaryAttachments = justifier.boundaryAttachments
  private removed : RemovalResult inner
  private removedAccepted : remove inner = .ok removed
  private ancestorRetained : AncestorRetained inner justifier
  private transportedInput :
    OccurrenceInput pattern removed.complement
  private transportedInputExact :
    transportedInput =
      transportedAncestorInput inner justifier removed ancestorRetained
  private transported :
    Occurrence pattern removed.complement
  private transportedAccepted :
    checkOccurrence transportedInput = .ok transported
  private reconstruction :
    ConcreteSpliceAttachment removed.complement removed.site pattern
  private reconstructionAccepted :
    reconstructionAttachment? inner removed = some reconstruction
  private reconstructionIso :
    ConcreteIso reconstruction.diagram source.val
  private reconstructionIsoAccepted :
    Reconstruction.extract_splice_iso? inner removed reconstruction
      reconstructionAccepted = some reconstructionIso
  private reconstructed : ConcreteSpliceResult reconstruction
  private reconstructedAccepted :
    splice reconstruction = .ok reconstructed
  private reconstructionCompilation :
    InsertionCompilation innerExtraction.compilation reconstruction
  private reconstructionCompilationAccepted :
    compileInsertion? innerExtraction.compilation reconstruction =
      some reconstructionCompilation
  private iterationInput :
    OrdinaryIterationInput transported.toSelection transported
  private iterationDestination :
    iterationInput.destination = removed.site
  private iteration :
    CheckedOrdinaryIteration iterationInput
  private insertedExact :
    reconstructionCompilation.inserted =
      iteration.destinationInsertion.inserted

/--
Validate both exact source occurrences, strict ancestry and disjointness, exact
ordered boundary correspondence, checked removal, surviving-ancestor transport,
exact reconstruction, and the complement-side iteration fact used for
soundness.  No semantic certificate is accepted.
-/
def checkOrdinaryDeiteration
    {innerSelection : CheckedSelection source}
    {inner : Occurrence pattern source}
    {justifierSelection : CheckedSelection source}
    {justifier : Occurrence pattern source}
    (input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier) :
    Except StructuralError (CheckedOrdinaryDeiteration input) := by
  match innerAccepted : checkExtraction innerSelection inner with
  | .error error => exact .error (.extractionRejected error)
  | .ok innerExtraction =>
      match justifierAccepted :
          checkExtraction justifierSelection justifier with
      | .error error => exact .error (.extractionRejected error)
      | .ok justifierExtraction =>
          if separatedAccepted :
              deiterationSeparatedCheck innerSelection justifierSelection =
                true then
            have separated :
                DeiterationSeparated innerSelection justifierSelection :=
              deiterationSeparatedCheck_sound innerSelection
                justifierSelection separatedAccepted
            if boundaryExact :
                inner.boundaryAttachments =
                  justifier.boundaryAttachments then
              match removedAccepted : remove inner with
              | .error error => exact .error (.removalRejected error)
              | .ok removed =>
                  if retainedAccepted :
                      ancestorRetainedCheck inner justifier = true then
                    have retained :
                        AncestorRetained inner justifier :=
                      ancestorRetainedCheck_sound inner justifier
                        retainedAccepted
                    let transportedInput :=
                      transportedAncestorInput inner justifier removed retained
                    match transportedAccepted :
                        checkOccurrence transportedInput with
                    | .error _ =>
                        exact .error .ancestorTransportRejected
                    | .ok transported =>
                        match reconstructionAccepted :
                            reconstructionAttachment? inner removed with
                        | none => exact .error .reconstructionRejected
                        | some reconstruction =>
                            match reconstructionIsoAccepted :
                                Reconstruction.extract_splice_iso? inner
                                  removed reconstruction
                                  reconstructionAccepted with
                            | none => exact .error .reconstructionIsoRejected
                            | some reconstructionIso =>
                              match reconstructedAccepted :
                                  splice reconstruction with
                              | .error error =>
                                  exact .error (.spliceRejected error)
                              | .ok reconstructed =>
                                match reconstructionCompiledAccepted :
                                    compileInsertion?
                                      innerExtraction.compilation
                                      reconstruction with
                                | none =>
                                    exact .error
                                      .destinationCopyCompilationMismatch
                                | some reconstructionCompilation =>
                                    let iterationInput :
                                        OrdinaryIterationInput
                                          transported.toSelection
                                          transported :=
                                      { destination := removed.site }
                                    match iterationAccepted :
                                        checkOrdinaryIteration
                                          iterationInput with
                                    | .error error => exact .error error
                                    | .ok iteration =>
                                        if insertedExact :
                                            intrinsicRegionsEqual
                                              reconstructionCompilation.inserted
                                              iteration.destinationInsertion.inserted =
                                                true then
                                          exact .ok
                                            (CheckedOrdinaryDeiteration.mk
                                              innerExtraction
                                              justifierExtraction separated
                                              boundaryExact removed
                                              removedAccepted retained
                                              transportedInput rfl transported
                                              transportedAccepted reconstruction
                                              reconstructionAccepted
                                              reconstructionIso
                                              reconstructionIsoAccepted
                                              reconstructed
                                              reconstructedAccepted
                                              reconstructionCompilation
                                              reconstructionCompiledAccepted
                                              iterationInput rfl iteration
                                              (intrinsicRegionsEqual_sound
                                                insertedExact))
                                        else
                                          exact .error .copyTargetMismatch
                  else
                    exact .error .ancestorTransportRejected
            else
              exact .error .copyBoundaryMismatch
          else
            exact .error .illegalDeiterationJustifier

namespace CheckedOrdinaryDeiteration

def tag
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (_checked : CheckedOrdinaryDeiteration input) : StepTag :=
  .deiteration

/-- Deiteration starts from the user's checked diagram containing both copies. -/
def source
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (_checked : CheckedOrdinaryDeiteration input) :
    CheckedDiagram definitions :=
  sourceDiagram

/-- Deiteration returns the checker-computed removal complement. -/
def target
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (checked : CheckedOrdinaryDeiteration input) :
    CheckedDiagram definitions :=
  checked.removed.complement

/-- The surviving exact ancestor justifier in the computed complement. -/
def survivingJustifier
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (checked : CheckedOrdinaryDeiteration input) :
    Occurrence pattern checked.target :=
  checked.transported

theorem sound
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (checked : CheckedOrdinaryDeiteration input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.source)
      (denoteChecked pre definitionEnv checked.target) := by
  let raw : CheckedDiagram definitions :=
    ⟨checked.reconstruction.diagram,
      checked.reconstructionCompilation.generated_wellFormed⟩
  have rawSource :
      denoteChecked pre definitionEnv raw ↔
        denoteChecked pre definitionEnv sourceDiagram :=
    iso_denotation
      checked.reconstructionIso
      pre definitionEnv
  have rawInserted :
      denoteChecked pre definitionEnv raw ↔
        denoteRegion pre definitionEnv Env.empty
          checked.reconstructionCompilation.inserted := by
    exact
      checked.reconstructionCompilation.generated_checked_denotes_inserted
        pre definitionEnv
  obtain
      ⟨reconstructionCompiled, reconstructionCompiledAccepted,
        reconstructedInserted⟩ :=
    denote_splice checked.innerExtraction.compilation
      checked.reconstruction checked.reconstructed
      checked.reconstructedAccepted pre definitionEnv
  have sameReconstructionCompilation :
      reconstructionCompiled = checked.reconstructionCompilation :=
    Option.some.inj
      (reconstructionCompiledAccepted.symm.trans
        checked.reconstructionCompilationAccepted)
  subst reconstructionCompiled
  obtain ⟨compiled, compiledAccepted, resultInserted⟩ :=
    denote_splice checked.iteration.extraction.compilation
      checked.iteration.destinationAttachment checked.iteration.result
      checked.iteration.resultAccepted pre definitionEnv
  have sameCompilation :
      compiled = checked.iteration.destinationInsertion :=
    Option.some.inj
      (compiledAccepted.symm.trans
        checked.iteration.destinationInsertionAccepted)
  subst compiled
  have complementIteration :
      denoteChecked pre definitionEnv checked.removed.complement ↔
        denoteChecked pre definitionEnv checked.iteration.result.checked :=
    checked.iteration.equivalence pre definitionEnv
  intro sourceDenotes
  have reconstructedDenotes :
      denoteChecked pre definitionEnv checked.reconstructed.checked :=
    reconstructedInserted.mpr
      (rawInserted.mp (rawSource.mpr sourceDenotes))
  apply complementIteration.mpr
  apply resultInserted.mpr
  rw [← checked.insertedExact]
  exact reconstructedInserted.mp reconstructedDenotes

/-- The checker-owned complement iteration also supplies the reverse
direction, so ordinary deiteration is an equivalence independently of replay
orientation. -/
theorem equivalence
    {definitions : List (List Sig)}
    {sourceDiagram : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {innerSelection : CheckedSelection sourceDiagram}
    {inner : Occurrence pattern sourceDiagram}
    {justifierSelection : CheckedSelection sourceDiagram}
    {justifier : Occurrence pattern sourceDiagram}
    {input :
      OrdinaryDeiterationInput innerSelection inner
        justifierSelection justifier}
    (checked : CheckedOrdinaryDeiteration input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv checked.source ↔
      denoteChecked pre definitionEnv checked.target := by
  constructor
  · exact checked.sound pre definitionEnv
  · intro targetDenotes
    let raw : CheckedDiagram definitions :=
      ⟨checked.reconstruction.diagram,
        checked.reconstructionCompilation.generated_wellFormed⟩
    have rawSource :
        denoteChecked pre definitionEnv raw ↔
          denoteChecked pre definitionEnv sourceDiagram :=
      iso_denotation checked.reconstructionIso pre definitionEnv
    have rawInserted :
        denoteChecked pre definitionEnv raw ↔
          denoteRegion pre definitionEnv Env.empty
            checked.reconstructionCompilation.inserted :=
      checked.reconstructionCompilation.generated_checked_denotes_inserted
        pre definitionEnv
    obtain
        ⟨reconstructionCompiled, reconstructionCompiledAccepted,
          reconstructedInserted⟩ :=
      denote_splice checked.innerExtraction.compilation
        checked.reconstruction checked.reconstructed
        checked.reconstructedAccepted pre definitionEnv
    have sameReconstructionCompilation :
        reconstructionCompiled = checked.reconstructionCompilation :=
      Option.some.inj
        (reconstructionCompiledAccepted.symm.trans
          checked.reconstructionCompilationAccepted)
    subst reconstructionCompiled
    obtain ⟨compiled, compiledAccepted, resultInserted⟩ :=
      denote_splice checked.iteration.extraction.compilation
        checked.iteration.destinationAttachment checked.iteration.result
        checked.iteration.resultAccepted pre definitionEnv
    have sameCompilation :
        compiled = checked.iteration.destinationInsertion :=
      Option.some.inj
        (compiledAccepted.symm.trans
          checked.iteration.destinationInsertionAccepted)
    subst compiled
    have complementIteration :
        denoteChecked pre definitionEnv checked.removed.complement ↔
          denoteChecked pre definitionEnv checked.iteration.result.checked :=
      checked.iteration.equivalence pre definitionEnv
    have iterationResult :
        denoteChecked pre definitionEnv checked.iteration.result.checked :=
      complementIteration.mp targetDenotes
    have reconstructionInserted :
        denoteRegion pre definitionEnv Env.empty
          checked.reconstructionCompilation.inserted := by
      rw [checked.insertedExact]
      exact resultInserted.mp iterationResult
    exact rawSource.mp (rawInserted.mpr reconstructionInserted)

end CheckedOrdinaryDeiteration

end StructuralCore

end VisualProof
