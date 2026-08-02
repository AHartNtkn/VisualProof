import VisualProof.Diagram.Concrete.WirePrimitive.ContentEndsSemantics
import VisualProof.Diagram.Concrete.WirePrimitive.ContentEmptySemantics
import VisualProof.Diagram.Concrete.WirePrimitive.ContentOrigin
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

private theorem castAllAppliedSites_length
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (exact : left = right)
    (sites : AllAppliedSites source left) :
    (exact ▸ sites).sites.length = sites.sites.length := by
  subst right
  rfl

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

/-- The exact concrete construction accepted by this opaque wrap receipt.
Compiler factorization consumes its carrier-origin maps; it does not rerun the
content checker. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutWrap source wire) :
    CutWrapResult source wire :=
  applied.checked

/-- The accepted positional/common-core evidence paired with the wrap
construction. -/
def constructionLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedCutWrap source wire) :
    CutWrapResult.SiteLedger applied.constructionResult :=
  applied.ledger

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

/-- The exact concrete construction accepted by this opaque split receipt. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire) :
    ParallelSplitResult source wire :=
  applied.checked

/-- The accepted positional/common-core evidence paired with the split
construction. -/
def constructionLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (applied : AppliedParallelSplit source wire) :
    ParallelSplitResult.SiteLedger applied.constructionResult :=
  applied.ledger

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

/-- The exact concrete construction accepted by this opaque all-ends
deletion receipt. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire) :
    EndsDeleteResult source wire :=
  applied.checked

/-- The accepted common-core and deletion evidence paired with the all-ends
construction. -/
def constructionLedger
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedEndsDelete source orientation wire) :
    EndsDeleteResult.SiteLedger applied.constructionResult :=
  applied.ledger

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

/-- Accepted content-pair inverse landing.  Its isomorphism is total once the
three receipt-owned carrier equivalences pass exact structural validation. -/
structure InverseLanding
    (target planned : CheckedDiagram definitions) where
  private mk ::
  iso : ConcreteIso target.val planned.val

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

namespace AppliedEndsDelete

/-- Exact acted wire transported backward through the supplied suffix iso. -/
def transportedInverseWire
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : planned.val.WireId}
    (forward : AppliedEndsDelete planned orientation wire)
    (targetIso : ConcreteIso real.val forward.target.val) :
    real.val.WireId :=
  targetIso.wires.symm forward.inverseWire

/-- Exact ordered deleted sites transported backward through the supplied
suffix iso. -/
def transportedInverseSites
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : planned.val.WireId}
    (forward : AppliedEndsDelete planned orientation wire)
    (targetIso : ConcreteIso real.val forward.target.val) :
    List (EndSite real (forward.transportedInverseWire targetIso)) :=
  forward.inverseSites.map fun site =>
    { region := targetIso.regions.symm site.region
      arguments := site.arguments.map targetIso.wires.symm }

/-- Receipt-owned inverse cancellation for all-end deletion followed by the
accepted transported spawn.  The exact region/wire carriers compose the two
constructions with the suffix iso; nodes additionally preserve the ordered
generated-site suffix before reconstructing the deleted source nodes. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {joinOrientation orientation : Orientation}
    {wire : planned.val.WireId}
    (forward : AppliedEndsDelete planned joinOrientation wire)
    (targetIso : ConcreteIso real.val forward.target.val)
    (backward : AppliedEndsSpawn real orientation
      (forward.transportedInverseWire targetIso)
      (forward.transportedInverseSites targetIso)) :
    Except WireContentError (InverseLanding backward.target planned) := do
  let siteCountExact :
      (forward.transportedInverseSites targetIso).length =
        forward.checked.sites.sites.length := by
    rw [show (forward.transportedInverseSites targetIso).length =
        forward.inverseSites.length by
      exact List.length_map _]
    change forward.checked.targetSites.length = _
    exact List.length_map _
  let regions := backward.checked.regionOriginEquiv.trans <|
    targetIso.regions.trans forward.checked.regionOriginEquiv
  let nodes := backward.checked.constructionNodeEquiv |>.trans <|
    (ConcreteWirePrimitive.ContentConstruction.addRightEquiv targetIso.nodes
      (forward.transportedInverseSites targetIso).length).trans <|
      (ConcreteWirePrimitive.ContentConstruction.finEquivOfEq
        (congrArg (fun count => forward.target.val.nodeCount + count)
          siteCountExact)).trans forward.checked.reconstructionNodeEquiv
  let wires := backward.checked.wireOriginEquiv.trans <|
    targetIso.wires.trans forward.checked.wireOriginEquiv
  let iso ← optionToExcept .semanticLedgerRejected <|
    ConcreteIso.checkEquivs? backward.target.val planned.val
      regions nodes wires
  pure ⟨iso⟩

end AppliedEndsDelete

namespace AppliedCutWrap

/-- Exact acted wire transported backward through the supplied suffix iso. -/
def transportedInverseWire
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : AppliedCutWrap planned wire)
    (targetIso : ConcreteIso real.val forward.target.val) :
    real.val.WireId :=
  targetIso.wires.symm forward.inverseWire

/-- Receipt-owned inverse cancellation for cut wrapping followed by the
accepted transported absorb. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : AppliedCutWrap planned wire)
    (targetIso : ConcreteIso real.val forward.target.val)
    (backward : AppliedCutAbsorb real
      (forward.transportedInverseWire targetIso)) :
    Except WireContentError (InverseLanding backward.target planned) := do
  let inverseWire := forward.transportedInverseWire targetIso
  let wireExact : targetIso.wires inverseWire = forward.inverseWire :=
    targetIso.wires.right_inv forward.inverseWire
  let targetSites : AllAppliedSites forward.target
      (targetIso.wires inverseWire) :=
    wireExact.symm ▸ forward.ledger.targetSites
  let siteEquiv := AllAppliedSites.transportPositionEquiv targetIso
    backward.checked.sites targetSites
  let siteCountExact : backward.checked.sites.sites.length =
      forward.checked.sites.sites.length := by
    rw [ConcreteWirePrimitive.ContentConstruction.finCount_eq siteEquiv]
    rw [show targetSites.sites.length =
        forward.ledger.targetSites.sites.length by
      exact castAllAppliedSites_length wireExact.symm
        forward.ledger.targetSites]
    exact forward.ledger.correspondence.1.symm
  let extendedRegions :=
    backward.checked.reconstructionRegionEquiv.trans <|
      targetIso.regions.trans forward.checked.extendedRegionOriginEquiv
  let regionCountExact : backward.target.val.regionCount =
      planned.val.regionCount := by
    have extendedCount :=
      ConcreteWirePrimitive.ContentConstruction.finCount_eq extendedRegions
    have siteCount := siteCountExact
    change backward.checked.checked.val.regionCount +
        backward.checked.sites.sites.length =
      planned.val.regionCount + forward.checked.sites.sites.length
      at extendedCount
    change backward.checked.sites.sites.length =
      forward.checked.sites.sites.length at siteCount
    change backward.checked.checked.val.regionCount = planned.val.regionCount
    omega
  let regions :=
    ConcreteWirePrimitive.ContentConstruction.finEquivOfEq regionCountExact
  let nodes := backward.checked.nodeOriginEquiv.trans <|
    targetIso.nodes.trans forward.checked.nodeOriginEquiv
  let wires := backward.checked.wireOriginEquiv.trans <|
    targetIso.wires.trans forward.checked.wireOriginEquiv
  let iso ← optionToExcept .semanticLedgerRejected <|
    ConcreteIso.checkEquivs? backward.target.val planned.val
      regions nodes wires
  pure ⟨iso⟩

end AppliedCutWrap

namespace AppliedParallelSplit

/-- Exact first generated wire transported backward through the supplied
suffix iso. -/
def transportedInverseLeft
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : AppliedParallelSplit planned wire)
    (targetIso : ConcreteIso real.val forward.target.val) :
    real.val.WireId :=
  targetIso.wires.symm forward.inverseLeft

/-- Exact second generated wire transported backward through the supplied
suffix iso. -/
def transportedInverseRight
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : AppliedParallelSplit planned wire)
    (targetIso : ConcreteIso real.val forward.target.val) :
    real.val.WireId :=
  targetIso.wires.symm forward.inverseRight

/-- Receipt-owned inverse cancellation for parallel splitting followed by the
accepted transported fuse. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : AppliedParallelSplit planned wire)
    (targetIso : ConcreteIso real.val forward.target.val)
    (backward : AppliedParallelFuse real
      (forward.transportedInverseLeft targetIso)
      (forward.transportedInverseRight targetIso)) :
    Except WireContentError (InverseLanding backward.target planned) := do
  let inverseRight := forward.transportedInverseRight targetIso
  let rightExact : targetIso.wires inverseRight = forward.inverseRight :=
    targetIso.wires.right_inv forward.inverseRight
  let targetSites : AllAppliedSites forward.target
      (targetIso.wires inverseRight) :=
    rightExact.symm ▸ forward.ledger.secondSites
  let siteEquiv := AllAppliedSites.transportPositionEquiv targetIso
    backward.checked.rightSites targetSites
  let siteCountExact : backward.checked.rightSites.sites.length =
      forward.checked.sites.sites.length := by
    rw [ConcreteWirePrimitive.ContentConstruction.finCount_eq siteEquiv]
    rw [show targetSites.sites.length =
        forward.ledger.secondSites.sites.length by
      exact castAllAppliedSites_length rightExact.symm
        forward.ledger.secondSites]
    exact forward.ledger.correspondence.2.1.symm
  let inverseSiteCountExact :
      backward.checked.inverse.sites.sites.length =
        forward.checked.sites.sites.length :=
    backward.checked.inverseSites_length.trans siteCountExact
  let regions := backward.checked.regionOriginEquiv.trans <|
    targetIso.regions.trans forward.checked.regionOriginEquiv
  let nodeCountExact : backward.target.val.nodeCount =
      planned.val.nodeCount := by
    have inverseDelta :
        backward.checked.inverse.checked.val.nodeCount =
          backward.checked.checked.val.nodeCount +
            backward.checked.inverse.sites.sites.length := by
      have construction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          backward.checked.inverse.constructionNodeEquiv
      have reconstruction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          backward.checked.inverse.reconstructionNodeEquiv
      have combine : ∀ (base count checked original : Nat),
          checked = base + (count + count) → base + count = original →
            checked = original + count := by
        omega
      exact combine _ _ _ _ construction reconstruction
    have forwardDelta : forward.target.val.nodeCount =
        planned.val.nodeCount + forward.checked.sites.sites.length := by
      have construction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          forward.checked.constructionNodeEquiv
      have reconstruction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          forward.checked.reconstructionNodeEquiv
      have combine : ∀ (base count checked original : Nat),
          checked = base + (count + count) → base + count = original →
            checked = original + count := by
        omega
      exact combine _ _ _ _ construction reconstruction
    have inverseLanding :=
      ConcreteIso.nodeCount_eq backward.checked.inverseIso
    have suffixCount := ConcreteIso.nodeCount_eq targetIso
    have siteCount := inverseSiteCountExact
    change backward.checked.checked.val.nodeCount = planned.val.nodeCount
    omega
  let wireCountExact : backward.target.val.wireCount =
      planned.val.wireCount := by
    have inverseDelta :
        backward.checked.inverse.checked.val.wireCount =
          backward.checked.checked.val.wireCount + 1 := by
      have construction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          backward.checked.inverse.constructionWireEquiv
      have reconstruction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          backward.checked.inverse.reconstructionWireEquiv
      have combine : ∀ (base checked original : Nat),
          checked = base + 2 → base + 1 = original →
            checked = original + 1 := by
        omega
      exact combine _ _ _ construction reconstruction
    have forwardDelta : forward.target.val.wireCount =
        planned.val.wireCount + 1 := by
      have construction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          forward.checked.constructionWireEquiv
      have reconstruction :=
        ConcreteWirePrimitive.ContentConstruction.finCount_eq
          forward.checked.reconstructionWireEquiv
      have combine : ∀ (base checked original : Nat),
          checked = base + 2 → base + 1 = original →
            checked = original + 1 := by
        omega
      exact combine _ _ _ construction reconstruction
    have inverseLanding :=
      ConcreteIso.wireCount_eq backward.checked.inverseIso
    have suffixCount := ConcreteIso.wireCount_eq targetIso
    change backward.checked.checked.val.wireCount = planned.val.wireCount
    omega
  let nodes :=
    ConcreteWirePrimitive.ContentConstruction.finEquivOfEq nodeCountExact
  let wires :=
    ConcreteWirePrimitive.ContentConstruction.finEquivOfEq wireCountExact
  let iso ← optionToExcept .semanticLedgerRejected <|
    ConcreteIso.checkEquivs? backward.target.val planned.val
      regions nodes wires
  pure ⟨iso⟩

end AppliedParallelSplit

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
