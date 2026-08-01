import VisualProof.Diagram.Concrete.WirePrimitive.ContentEndsSemantics
import VisualProof.Diagram.Concrete.WirePrimitive.ContentEmptySemantics
import VisualProof.Diagram.Concrete.WirePrimitive.ContentShapeSemantics
import VisualProof.Rule.WirePrimitive.ContentWitnesses
import VisualProof.Rule.Tag
import VisualProof.Rule.Structural

namespace VisualProof

namespace WirePrimitive

namespace Content

open ConcreteWirePrimitive

/-- Stable public refusal outcomes for content-shape wire primitives. -/
inductive WireContentError
  | endsDeleteRequiresNegative
  | endsDeleteBackwardRequiresPositive
  | endsSpawnRequiresPositive
  | endsSpawnBackwardRequiresNegative
  | scopeCompilationFailed
  | semanticLedgerRejected
  | concreteRejected (error : ConcreteWirePrimitive.ContentError)
  deriving Repr, DecidableEq

private def deletePolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

private def spawnPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

private def optionToExcept
    (error : WireContentError) : Option α → Except WireContentError α
  | none => .error error
  | some value => .ok value

private structure CheckedDeletePolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    deletePolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedSpawnPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    spawnPolarityLegal orientation compiled.frame.context.cutDepth = true

private def requireDeletePolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireContentError
      (CheckedDeletePolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          deletePolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .endsDeleteRequiresNegative
          | .backward => .endsDeleteBackwardRequiresPositive

private def requireSpawnPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireContentError
      (CheckedSpawnPolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          spawnPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .endsSpawnRequiresPositive
          | .backward => .endsSpawnBackwardRequiresNegative

/-- Opaque accepted cut-wrap transformation. -/
structure AppliedCutWrap
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  private checked : CutWrapResult source wire
  private ledger : CutWrapResult.SiteLedger checked

namespace AppliedCutWrap

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedCutWrap source wire) : CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutWrap source wire) :
    CheckedDiagram definitions :=
  applied.checked.checked

/-- Receipt-owned wire on which the exact inverse absorb acts. -/
def inverseWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutWrap source wire) : applied.target.val.WireId :=
  applied.checked.targetWire

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedCutWrap source wire) : StepTag :=
  .cutWrap

end AppliedCutWrap

/-- Opaque accepted cut-absorb transformation. -/
structure AppliedCutAbsorb
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  private checked : CutAbsorbResult source wire
  private inverseLedger :
    CutWrapResult.SiteLedger checked.inverse

namespace AppliedCutAbsorb

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedCutAbsorb source wire) : CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutAbsorb source wire) :
    CheckedDiagram definitions :=
  applied.checked.checked

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedCutAbsorb source wire) : StepTag :=
  .cutAbsorb

end AppliedCutAbsorb

/-- Opaque accepted parallel-split transformation. -/
structure AppliedParallelSplit
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  private checked : ParallelSplitResult source wire
  private ledger : ParallelSplitResult.SiteLedger checked

namespace AppliedParallelSplit

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedParallelSplit source wire) :
    CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire) :
    CheckedDiagram definitions :=
  applied.checked.checked

/-- Receipt-owned first wire of the exact inverse fuse. -/
def inverseLeft
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire) : applied.target.val.WireId :=
  applied.checked.firstWire

/-- Receipt-owned second wire of the exact inverse fuse. -/
def inverseRight
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire) : applied.target.val.WireId :=
  applied.checked.secondWire

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_ : AppliedParallelSplit source wire) : StepTag :=
  .parallelSplit

end AppliedParallelSplit

/-- Opaque accepted parallel-fuse transformation. -/
structure AppliedParallelFuse
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId) where
  private mk ::
  private checked : ParallelFuseResult source left right
  private inverseLedger :
    ParallelSplitResult.SiteLedger checked.inverse

namespace AppliedParallelFuse

def source
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (_ : AppliedParallelFuse source left right) :
    CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (applied : AppliedParallelFuse source left right) :
    CheckedDiagram definitions :=
  applied.checked.checked

def tag
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (_ : AppliedParallelFuse source left right) : StepTag :=
  .parallelFuse

end AppliedParallelFuse

/-- Opaque accepted all-ends deletion with its checked directional gate. -/
structure AppliedEndsDelete
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  private mk ::
  private polarity : CheckedDeletePolarity source orientation wire
  private checked : EndsDeleteResult source wire
  private ledger : EndsDeleteResult.SiteLedger checked

namespace AppliedEndsDelete

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (_ : AppliedEndsDelete source orientation wire) :
    CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire) :
    CheckedDiagram definitions :=
  applied.checked.checked

/-- Exact endpoint-free acted wire retained by all-ends deletion. -/
def inverseWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire) :
    applied.target.val.WireId :=
  applied.checked.targetWire

/-- Exact ordered sites deleted by the step, transported into its target. -/
def inverseSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire) :
    List (EndSite applied.target applied.inverseWire) :=
  applied.checked.targetSites

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (_ : AppliedEndsDelete source orientation wire) : StepTag :=
  .endsDelete

end AppliedEndsDelete

/-- Opaque accepted end spawning with its checked directional gate. -/
structure AppliedEndsSpawn
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (sites : List (EndSite source wire)) where
  private mk ::
  private polarity : CheckedSpawnPolarity source orientation wire
  private checked : EndsSpawnResult source wire sites
  private inverseLedger :
    EndsDeleteResult.SiteLedger checked.inverse
  private cut_depth_exact :
    polarity.compiled.frame.context.cutDepth =
      inverseLedger.sourceScope.frame.context.cutDepth

namespace AppliedEndsSpawn

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (_ : AppliedEndsSpawn source orientation wire sites) :
    CheckedDiagram definitions :=
  source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (applied : AppliedEndsSpawn source orientation wire sites) :
    CheckedDiagram definitions :=
  applied.checked.checked

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (_ : AppliedEndsSpawn source orientation wire sites) : StepTag :=
  .endsSpawn

end AppliedEndsSpawn

/-- Check and apply uniform cut wrapping. -/
def applyCutWrap
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except WireContentError (AppliedCutWrap source wire) := do
  let checked ←
    (ConcreteWirePrimitive.cutWrap source wire).mapError .concreteRejected
  let ledger ←
    optionToExcept .semanticLedgerRejected checked.checkSiteLedger
  pure ⟨checked, ledger⟩

/-- Check and apply exact cut absorption. -/
def applyCutAbsorb
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except WireContentError (AppliedCutAbsorb source wire) := do
  let checked ←
    (ConcreteWirePrimitive.cutAbsorb source wire).mapError .concreteRejected
  let inverseLedger ←
    optionToExcept .semanticLedgerRejected checked.inverse.checkSiteLedger
  pure ⟨checked, inverseLedger⟩

/-- Check and apply uniform parallel splitting. -/
def applyParallelSplit
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except WireContentError (AppliedParallelSplit source wire) := do
  let checked ←
    (ConcreteWirePrimitive.parallelSplit source wire).mapError
      .concreteRejected
  let ledger ←
    optionToExcept .semanticLedgerRejected checked.checkSiteLedger
  pure ⟨checked, ledger⟩

/-- Check and apply exact pairwise parallel fusion. -/
def applyParallelFuse
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId) :
    Except WireContentError (AppliedParallelFuse source left right) := do
  let checked ←
    (ConcreteWirePrimitive.parallelFuse source left right).mapError
      .concreteRejected
  let inverseLedger ←
    optionToExcept .semanticLedgerRejected checked.inverse.checkSiteLedger
  pure ⟨checked, inverseLedger⟩

/-- Check and apply gated deletion of every applied end. -/
def applyEndsDelete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation) :
    Except WireContentError
      (AppliedEndsDelete source orientation wire) := do
  let polarity ← requireDeletePolarity source orientation wire
  let checked ←
    (ConcreteWirePrimitive.deleteEnds source wire).mapError .concreteRejected
  let ledger ←
    optionToExcept .semanticLedgerRejected checked.checkSiteLedger
  pure ⟨polarity, checked, ledger⟩

/-- Check and apply gated spawning at every requested site. -/
def applyEndsSpawn
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : List (EndSite source wire))
    (orientation : Orientation) :
    Except WireContentError
      (AppliedEndsSpawn source orientation wire sites) := do
  let polarity ← requireSpawnPolarity source orientation wire
  let checked ←
    (ConcreteWirePrimitive.spawnEnds source wire sites).mapError
      .concreteRejected
  let inverseLedger ←
    optionToExcept .semanticLedgerRejected checked.inverse.checkSiteLedger
  if exact :
      polarity.compiled.frame.context.cutDepth =
        inverseLedger.sourceScope.frame.context.cutDepth then
    pure ⟨polarity, checked, inverseLedger, exact⟩
  else
    throw .semanticLedgerRejected

/-- Cut wrapping is a checked whole-diagram equivalence. -/
theorem cut_wrap_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (applied : AppliedCutWrap source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Exact cut absorption is the checked inverse of cut wrapping. -/
theorem cut_absorb_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (applied : AppliedCutAbsorb source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target := by
  have inverseSound :=
    applied.inverseLedger.denotes model definitionEnv
  have inverseLanding :=
    iso_denotation applied.checked.inverseIso model.toPreModel definitionEnv
  exact inverseLanding.symm.trans inverseSound.symm

/-- Parallel splitting is a checked whole-diagram equivalence. -/
theorem parallel_split_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (applied : AppliedParallelSplit source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Exact parallel fusion is the checked inverse of parallel splitting. -/
theorem parallel_fuse_sound
    {source : CheckedDiagram definitions}
    (left right : source.val.WireId)
    (applied : AppliedParallelFuse source left right)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target := by
  have inverseSound :=
    applied.inverseLedger.denotes model definitionEnv
  have inverseLanding :=
    iso_denotation applied.checked.inverseIso model.toPreModel definitionEnv
  exact inverseLanding.symm.trans inverseSound.symm

/-- All-end deletion is sound in the checker-selected orientation. -/
theorem ends_delete_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (applied : AppliedEndsDelete source orientation wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  have sound :=
    applied.ledger.denotes model definitionEnv
  have scopes :
      applied.polarity.compiled = applied.ledger.sourceScope :=
    SiteCompilation.unique _ _
  cases orientation with
  | forward =>
      have odd :
          applied.ledger.sourceScope.frame.context.cutDepth % 2 = 1 := by
        rw [← scopes]
        exact of_decide_eq_true (by
          simpa [deletePolarityLegal] using applied.polarity.legal)
      exact sound.2 odd
  | backward =>
      have even :
          applied.ledger.sourceScope.frame.context.cutDepth % 2 = 0 := by
        rw [← scopes]
        exact of_decide_eq_true (by
          simpa [deletePolarityLegal] using applied.polarity.legal)
      exact sound.1 even

/-- Endpoint spawning is the checked inverse of all-end deletion. -/
theorem ends_spawn_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (sites : List (EndSite source wire))
    (applied : AppliedEndsSpawn source orientation wire sites)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  have sound :=
    applied.inverseLedger.denotes model definitionEnv
  have inverseLanding :=
    iso_denotation applied.checked.inverseIso model.toPreModel definitionEnv
  cases orientation with
  | forward =>
      have even :
          applied.inverseLedger.sourceScope.frame.context.cutDepth % 2 = 0 := by
        rw [← applied.cut_depth_exact]
        exact of_decide_eq_true (by
          simpa [spawnPolarityLegal] using applied.polarity.legal)
      intro sourceHolds
      exact sound.1 even (inverseLanding.mpr sourceHolds)
  | backward =>
      have odd :
          applied.inverseLedger.sourceScope.frame.context.cutDepth % 2 = 1 := by
        rw [← applied.cut_depth_exact]
        exact of_decide_eq_true (by
          simpa [spawnPolarityLegal] using applied.polarity.legal)
      intro targetHolds
      exact inverseLanding.mp (sound.2 odd targetHolds)

namespace AppliedCutWrap

/-- Method-form soundness carried by an accepted cut-wrap receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutWrap source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  cut_wrap_sound wire applied model definitionEnv

end AppliedCutWrap

namespace AppliedCutAbsorb

/-- Method-form soundness carried by an accepted cut-absorb receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutAbsorb source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  cut_absorb_sound wire applied model definitionEnv

end AppliedCutAbsorb

namespace AppliedParallelSplit

/-- Method-form soundness carried by an accepted parallel-split receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  parallel_split_sound wire applied model definitionEnv

end AppliedParallelSplit

namespace AppliedParallelFuse

/-- Method-form soundness carried by an accepted parallel-fuse receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (applied : AppliedParallelFuse source left right)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  parallel_fuse_sound left right applied model definitionEnv

end AppliedParallelFuse

namespace AppliedEndsDelete

/-- Method-form soundness carried by an accepted all-end deletion receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  ends_delete_sound orientation wire applied model definitionEnv

end AppliedEndsDelete

namespace AppliedEndsSpawn

/-- Method-form soundness carried by an accepted endpoint-spawn receipt. -/
theorem sound
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (applied : AppliedEndsSpawn source orientation wire sites)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  ends_spawn_sound orientation wire sites applied model definitionEnv

end AppliedEndsSpawn

end Content

export Content
  (WireContentError AppliedCutWrap AppliedCutAbsorb AppliedParallelSplit
    AppliedParallelFuse AppliedEndsDelete AppliedEndsSpawn applyCutWrap
    applyCutAbsorb applyParallelSplit applyParallelFuse applyEndsDelete
    applyEndsSpawn cut_wrap_sound cut_absorb_sound parallel_split_sound
    parallel_fuse_sound ends_delete_sound ends_spawn_sound)

end WirePrimitive

export WirePrimitive
  (WireContentError AppliedCutWrap AppliedCutAbsorb AppliedParallelSplit
    AppliedParallelFuse AppliedEndsDelete AppliedEndsSpawn applyCutWrap
    applyCutAbsorb applyParallelSplit applyParallelFuse applyEndsDelete
    applyEndsSpawn cut_wrap_sound cut_absorb_sound parallel_split_sound
    parallel_fuse_sound ends_delete_sound ends_spawn_sound)

end VisualProof
