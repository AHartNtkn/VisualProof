import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationLocal
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationCompleteness
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsConstructionNaturality
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsSiteFactorization

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

open WirePrimitive
open ContentAlignment

/-- Embed the shared site-outer context beyond the two explicit normalized
relation-head slots. -/
def localOuterRenaming :
    WireRenaming outer
      ((.rel sourceArguments) :: (.rel targetArguments) :: outer) :=
  fun {_} value => .there (.there value)

/-- Explicit normalized slot for the source relation head. -/
def localSourceHead :
    Var ((.rel sourceArguments) :: (.rel targetArguments) :: outer)
      (.rel sourceArguments) :=
  .here

/-- Explicit normalized slot for the target relation head. -/
def localTargetHead :
    Var ((.rel sourceArguments) :: (.rel targetArguments) :: outer)
      (.rel targetArguments) :=
  .there .here

/-- Normalize one concrete scope-local binder block around an explicit head
slot before abstracting every uniformly applied occurrence. -/
def normalizedArgumentShape
    (removal :
      LocalHeadRemoval (.rel arguments) bound reduced)
    (headSlot :
      Var
        ((.rel sourceArguments) :: (.rel targetArguments) :: outer)
        (.rel arguments))
    (body : Region definitions (bound ++ outer)) :
    UniformIntrinsicRegion definitions arguments
      ((.rel sourceArguments) :: (.rel targetArguments) :: outer) :=
  wrapArgumentBinds reduced
    (UniformIntrinsicRegion.abstractApplied
      (Var.appendRight reduced headSlot)
      (body.renameWires
        (removal.rename localOuterRenaming headSlot)))

private theorem normalizedArgumentShape_denotes
    (removal :
      LocalHeadRemoval (.rel arguments) bound reduced)
    (headSlot :
      Var
        ((.rel sourceArguments) :: (.rel targetArguments) :: outer)
        (.rel arguments))
    (body : Region definitions (bound ++ outer))
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (commonEnv :
      Env pre
        ((.rel sourceArguments) :: (.rel targetArguments) :: outer))
    (headValue : pre.Domain (.rel arguments))
    (headExact : commonEnv _ headSlot = headValue) :
    (normalizedArgumentShape removal headSlot body).denote
        pre definitionEnv commonEnv (pre.apply headValue) ↔
      ∃ reducedValues : ConcreteElaboration.WireValues pre reduced,
        denoteRegion pre definitionEnv
          (ContentShapeSemantics.extendValues
            (removal.assembleValues headValue reducedValues)
            (Env.comp commonEnv localOuterRenaming))
          body := by
  unfold normalizedArgumentShape
  rw [wrapArgumentBinds_denotes]
  constructor
  · rintro ⟨reducedValues, shapeHolds⟩
    let normalizedEnv :=
      ContentShapeSemantics.extendValues reducedValues commonEnv
    have normalizedHead :
        normalizedEnv _
            (Var.appendRight reduced headSlot) =
          headValue := by
      dsimp only [normalizedEnv]
      rw [ContentShapeSemantics.extendValues_outer]
      exact headExact
    have abstractLaw :=
      UniformIntrinsicRegion.abstractApplied_denotes pre definitionEnv
        normalizedEnv (Var.appendRight reduced headSlot)
        (body.renameWires
          (removal.rename localOuterRenaming headSlot))
    rw [normalizedHead] at abstractLaw
    have abstracted :=
      abstractLaw.mpr shapeHolds
    have renamed :=
      (denoteRegion_renameWires pre definitionEnv normalizedEnv
        (removal.rename localOuterRenaming headSlot) body).mp
        abstracted
    have restored :=
      removal.rename_environment localOuterRenaming
        (Env.comp commonEnv localOuterRenaming) commonEnv rfl
        headValue reducedValues headExact
    rw [restored] at renamed
    exact ⟨reducedValues, renamed⟩
  · rintro ⟨reducedValues, bodyHolds⟩
    let normalizedEnv :=
      ContentShapeSemantics.extendValues reducedValues commonEnv
    have restored :=
      removal.rename_environment localOuterRenaming
        (Env.comp commonEnv localOuterRenaming) commonEnv rfl
        headValue reducedValues headExact
    have renamed :
        denoteRegion pre definitionEnv normalizedEnv
          (body.renameWires
            (removal.rename localOuterRenaming headSlot)) := by
      apply
        (denoteRegion_renameWires pre definitionEnv normalizedEnv
          (removal.rename localOuterRenaming headSlot) body).mpr
      rw [restored]
      exact bodyHolds
    refine ⟨reducedValues, ?_⟩
    have normalizedHead :
        normalizedEnv _
            (Var.appendRight reduced headSlot) =
          headValue := by
      dsimp only [normalizedEnv]
      rw [ContentShapeSemantics.extendValues_outer]
      exact headExact
    have abstractLaw :=
      UniformIntrinsicRegion.abstractApplied_denotes pre definitionEnv
        normalizedEnv (Var.appendRight reduced headSlot)
        (body.renameWires
          (removal.rename localOuterRenaming headSlot))
    rw [normalizedHead] at abstractLaw
    exact abstractLaw.mp renamed

/--
Arity-only scope factorization.  Unlike ordinary argument rewrites, this
normalizes the complete scope-local binder block after removing the rewritten
relation head.  Fresh wires at the acted scope and below it are therefore
owned by the same cylindrification certificate.
-/
structure LocalCylindricalFrame
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  targetSites : AllAppliedSites result.checked result.targetWire
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  targetScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope
  context :
    ContentAlignment.SiteContextFactorization sourceScope targetScope
  sourceHead :
    Var
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      (.rel sourceArguments)
  sourceHead_origin :
    ConcreteElaboration.WireContext.origin source.val
      (source.val.wiresAt (source.val.wires wire).scope) sourceHead = wire
  targetHead :
    Var
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      (.rel result.targetArguments)
  targetHead_origin :
    ConcreteElaboration.WireContext.origin result.checked.val
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope) targetHead =
      result.targetWire
  sourceReduced : List Sig
  targetReduced : List Sig
  sourceRemoval :
    LocalHeadRemoval (.rel sourceArguments)
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      sourceReduced
  sourceRemoval_head : sourceRemoval.head = sourceHead
  targetRemoval :
    LocalHeadRemoval (.rel result.targetArguments)
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      targetReduced
  targetRemoval_head : targetRemoval.head = targetHead

def LocalCylindricalFrame.sourceShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    UniformIntrinsicRegion definitions sourceArguments
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter) :=
  normalizedArgumentShape frame.sourceRemoval localSourceHead
    (frame.context.sourceBody frame.sourceScope.frame.siteBody)

def LocalCylindricalFrame.targetShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    UniformIntrinsicRegion definitions result.targetArguments
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter) :=
  normalizedArgumentShape frame.targetRemoval localTargetHead
    (frame.context.targetBody frame.targetScope.frame.siteBody)

def checkLocalCylindricalFrameFromSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    Option (LocalCylindricalFrame result sourceArguments) := do
  let sourceScope ←
    compileSite? source (source.val.wires wire).scope
  let targetScope ←
    compileSite? result.checked
      (result.checked.val.wires result.targetWire).scope
  let context ←
    ContentAlignment.checkSiteContextFactorization sourceScope targetScope
  have sourceMember :
      wire ∈ source.val.wiresAt (source.val.wires wire).scope := by
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩
  have targetMember :
      result.targetWire ∈
        result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope := by
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩
  let sourceHead :
      Var
        (ContentAlignment.localSignatures source.val
          (source.val.wires wire).scope)
        (.rel sourceArguments) :=
    InsertionCompilation.NaturalityInternal.castVar sourceSignature
      (InsertionCompilation.NaturalityInternal.varForMember source.val
        (source.val.wiresAt (source.val.wires wire).scope) wire
        sourceMember)
  let targetHead :
      Var
        (ContentAlignment.localSignatures result.checked.val
          (result.checked.val.wires result.targetWire).scope)
        (.rel result.targetArguments) :=
    InsertionCompilation.NaturalityInternal.castVar
      result.targetWire_signature
      (InsertionCompilation.NaturalityInternal.varForMember
        result.checked.val
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        result.targetWire targetMember)
  let sourceRemovalResult := LocalHeadRemoval.ofVar sourceHead
  let sourceReduced := sourceRemovalResult.1
  let sourceRemoval := sourceRemovalResult.2
  let targetRemovalResult := LocalHeadRemoval.ofVar targetHead
  let targetReduced := targetRemovalResult.1
  let targetRemoval := targetRemovalResult.2
  pure
    { targetSites := targetSites
      sourceScope := sourceScope
      targetScope := targetScope
      context := context
      sourceHead := sourceHead
      sourceHead_origin := by
        exact
          (InsertionCompilation.NaturalityInternal.origin_castVar source.val
            (source.val.wiresAt (source.val.wires wire).scope)
            sourceSignature _).trans
            (InsertionCompilation.NaturalityInternal.varForMember_origin
              source.val
              (source.val.wiresAt (source.val.wires wire).scope) wire
              sourceMember)
      targetHead := targetHead
      targetHead_origin := by
        exact
          (InsertionCompilation.NaturalityInternal.origin_castVar
            result.checked.val
            (result.checked.val.wiresAt
              (result.checked.val.wires result.targetWire).scope)
            result.targetWire_signature _).trans
            (InsertionCompilation.NaturalityInternal.varForMember_origin
              result.checked.val
              (result.checked.val.wiresAt
                (result.checked.val.wires result.targetWire).scope)
              result.targetWire targetMember)
      sourceReduced := sourceReduced
      targetReduced := targetReduced
      sourceRemoval := sourceRemoval
      sourceRemoval_head := LocalHeadRemoval.ofVar_head sourceHead
      targetRemoval := targetRemoval
      targetRemoval_head := LocalHeadRemoval.ofVar_head targetHead }

theorem checkLocalCylindricalFrameFromSites_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    ∃ frame,
      checkLocalCylindricalFrameFromSites result sourceArguments
          sourceSignature targetSites = some frame := by
  obtain ⟨sourceScope, sourceAccepted⟩ :=
    compileSite_complete source (source.val.wires wire).scope
  obtain ⟨targetScope, targetAccepted⟩ :=
    compileSite_complete result.checked
      (result.checked.val.wires result.targetWire).scope
  obtain ⟨context, contextAccepted⟩ :=
    checkSiteContextFactorization_argument_complete result localized
      sourceScope targetScope
  unfold checkLocalCylindricalFrameFromSites
  simp [sourceAccepted, targetAccepted, contextAccepted]

private def sourceCylindricalShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame :
      ArgumentFrameFactorization result sourceArguments) :
    UniformIntrinsicRegion definitions sourceArguments
      ((.rel sourceArguments) :: frame.targetScope.frame.visible.sigs) :=
  UniformIntrinsicRegion.abstractApplied
    (.here :
      Var
        ((.rel sourceArguments) :: frame.targetScope.frame.visible.sigs)
        (.rel sourceArguments))
    (frame.sourceScope.frame.siteBody.renameWires
      (frame.alignment.sourceRenaming frame.sourceSignature))

private def targetCylindricalShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame :
      ArgumentFrameFactorization result sourceArguments) :
    UniformIntrinsicRegion definitions result.targetArguments
      ((.rel sourceArguments) :: frame.targetScope.frame.visible.sigs) :=
  UniformIntrinsicRegion.abstractApplied
    (.there frame.targetHead :
      Var
        ((.rel sourceArguments) :: frame.targetScope.frame.visible.sigs)
        (.rel result.targetArguments))
    (frame.targetScope.frame.siteBody.renameWires
      (fun {_} value => .there value))

/-- Complete checker-owned arity-shift receipt. -/
private structure ArityShiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (fixedSignature : Sig) where
  insertion :
    TypedArguments.InsertionEvidence result.targetArguments
      sourceArguments fixedSignature
  frame : ArgumentFrameFactorization result sourceArguments
  accepted :
    CheckedCylindricalShape insertion
      (fun {_} value => value)
      (sourceCylindricalShape frame)
      (targetCylindricalShape frame)

/-- Complete checker-owned arity-unshift receipt. -/
private structure ArityUnshiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (fixedSignature : Sig) where
  insertion :
    TypedArguments.InsertionEvidence sourceArguments
      result.targetArguments fixedSignature
  frame : ArgumentFrameFactorization result sourceArguments
  accepted :
    CheckedCylindricalShape insertion
      (fun {_} value => value)
      (targetCylindricalShape frame)
      (sourceCylindricalShape frame)

private def checkArityShiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (fixedSignature : Sig) :
    Option
      (ArityShiftLedger result sourceArguments fixedSignature) := do
  if targetExact :
      ConcreteWirePrimitive.insertAt sourceArguments
          sourceArguments.length fixedSignature =
        result.targetArguments then
    let insertion :
        TypedArguments.InsertionEvidence result.targetArguments
          sourceArguments fixedSignature :=
      ⟨sourceArguments.length, targetExact⟩
    let frame ←
      checkArgumentFrameFactorization result sourceArguments sourceSignature
    let accepted ←
      checkCylindricalShape insertion
        (fun {_} value => value)
        (sourceCylindricalShape frame)
        (targetCylindricalShape frame)
    pure ⟨insertion, frame, accepted⟩
  else
    none

private def checkArityUnshiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat)
    (fixedSignature : Sig) :
    Option
      (ArityUnshiftLedger result sourceArguments fixedSignature) := do
  if sourceExact :
      ConcreteWirePrimitive.insertAt result.targetArguments
          position fixedSignature =
        sourceArguments then
    let insertion :
        TypedArguments.InsertionEvidence sourceArguments
          result.targetArguments fixedSignature :=
      ⟨position, sourceExact⟩
    let frame ←
      checkArgumentFrameFactorization result sourceArguments sourceSignature
    let accepted ←
      checkCylindricalShape insertion
        (fun {_} value => value)
        (targetCylindricalShape frame)
        (sourceCylindricalShape frame)
    pure ⟨insertion, frame, accepted⟩
  else
    none

/--
Complete scope-normalized arity-shift receipt.  This is the public arity
receipt used by the rule layer; the earlier ambient-frame receipt remains
available only as the simpler proof path for argument shapes with identical
scope-local binder blocks.
-/
structure ScopedArityShiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (fixedSignature : Sig) where
  insertion :
    TypedArguments.InsertionEvidence result.targetArguments
      sourceArguments fixedSignature
  position_exact : insertion.position = sourceArguments.length
  frame : LocalCylindricalFrame result sourceArguments
  accepted :
    CheckedCylindricalShape insertion
      (fun {_} value => value)
      frame.sourceShape frame.targetShape

/-- Complete scope-normalized arity-unshift receipt. -/
structure ScopedArityUnshiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (fixedSignature : Sig) where
  insertion :
    TypedArguments.InsertionEvidence sourceArguments
      result.targetArguments fixedSignature
  frame : LocalCylindricalFrame result sourceArguments
  accepted :
    CheckedCylindricalShape insertion
      (fun {_} value => value)
      frame.targetShape frame.sourceShape

def checkScopedArityShiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (fixedSignature : Sig) :
    Option
      (ScopedArityShiftLedger result sourceArguments fixedSignature) := do
  if targetExact :
      ConcreteWirePrimitive.insertAt sourceArguments
          sourceArguments.length fixedSignature =
        result.targetArguments then
    let insertion :
        TypedArguments.InsertionEvidence result.targetArguments
          sourceArguments fixedSignature :=
      ⟨sourceArguments.length, targetExact⟩
    let frame ←
      checkLocalCylindricalFrameFromSites result sourceArguments
        sourceSignature result.targetSites
    let accepted ←
      checkCylindricalShape insertion
        (fun {_} value => value)
        frame.sourceShape frame.targetShape
    pure ⟨insertion, rfl, frame, accepted⟩
  else
    none

private def checkScopedArityShiftLedgerFromSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (fixedSignature : Sig)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    Option
      (ScopedArityShiftLedger result sourceArguments fixedSignature) := do
  if targetExact :
      ConcreteWirePrimitive.insertAt sourceArguments
          sourceArguments.length fixedSignature =
        result.targetArguments then
    let insertion :
        TypedArguments.InsertionEvidence result.targetArguments
          sourceArguments fixedSignature :=
      ⟨sourceArguments.length, targetExact⟩
    let frame ←
      checkLocalCylindricalFrameFromSites result sourceArguments
        sourceSignature targetSites
    let accepted ←
      checkCylindricalShape insertion
        (fun {_} value => value)
        frame.sourceShape frame.targetShape
    pure ⟨insertion, rfl, frame, accepted⟩
  else
    none

def checkScopedArityUnshiftLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat)
    (fixedSignature : Sig) :
    Option
      (ScopedArityUnshiftLedger result sourceArguments fixedSignature) := do
  if sourceExact :
      ConcreteWirePrimitive.insertAt result.targetArguments
          position fixedSignature =
        sourceArguments then
    let insertion :
        TypedArguments.InsertionEvidence sourceArguments
          result.targetArguments fixedSignature :=
      ⟨position, sourceExact⟩
    let frame ←
      checkLocalCylindricalFrameFromSites result sourceArguments
        sourceSignature result.targetSites
    let accepted ←
      checkCylindricalShape insertion
        (fun {_} value => value)
        frame.targetShape frame.sourceShape
    pure ⟨insertion, frame, accepted⟩
  else
    none

namespace ArityShiftLedger

noncomputable def forward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments)) :
    model.toPreModel.Domain (.rel result.targetArguments) :=
  reifyRelation model
    (cylindricalLift ledger.insertion
      (model.toPreModel.apply sourceRelation))

noncomputable def backward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (targetRelation :
      model.toPreModel.Domain (.rel result.targetArguments)) :
    model.toPreModel.Domain (.rel sourceArguments) :=
  reifyRelation model
    (cylindricalProject ledger.insertion
      (model.toPreModel.apply targetRelation))

theorem forwardSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments))
    (targetEnv :
      Env model.toPreModel
        ledger.frame.targetScope.frame.visible.sigs)
    (targetHeadExact :
      targetEnv _ ledger.frame.targetHead =
        ledger.forward model sourceRelation) :
    denoteRegion model.toPreModel definitionEnv
        (Env.comp (targetEnv.extend sourceRelation)
          (ledger.frame.alignment.sourceRenaming
            ledger.frame.sourceSignature))
        ledger.frame.sourceScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv targetEnv
        ledger.frame.targetScope.frame.siteBody := by
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceRenaming :
      WireRenaming ledger.frame.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    ledger.frame.alignment.sourceRenaming
      ledger.frame.sourceSignature
  let targetRenaming :
      WireRenaming ledger.frame.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  have envExact :
      Env.comp commonEnv ledger.accepted.receipt.embedding =
        commonEnv := by
    funext signature value
    simp only [Env.comp]
    rw [ledger.accepted.embedding_exact value]
  have cylinder :=
    ledger.accepted.receipt.forward_denotes
      ledger.accepted.consistent model.toPreModel definitionEnv
      commonEnv commonEnv envExact
      (model.toPreModel.apply sourceRelation)
  rw [ledger.accepted.smaller_exact,
    ledger.accepted.larger_exact] at cylinder
  have targetSiteExact :
      model.toPreModel.apply
          (commonEnv _ (.there ledger.frame.targetHead)) =
        cylindricalLift ledger.insertion
          (model.toPreModel.apply sourceRelation) := by
    funext values
    apply propext
    change
      model.toPreModel.apply
          (targetEnv _ ledger.frame.targetHead) values ↔
        cylindricalLift ledger.insertion
          (model.toPreModel.apply sourceRelation) values
    rw [targetHeadExact]
    exact apply_reifyRelation model _ values
  have targetAbstract :
      (targetCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (cylindricalLift ledger.insertion
            (model.toPreModel.apply sourceRelation)) ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody := by
    rw [← targetSiteExact]
    exact
      (UniformIntrinsicRegion.abstractApplied_denotes
        model.toPreModel definitionEnv commonEnv
        (.there ledger.frame.targetHead)
        (ledger.frame.targetScope.frame.siteBody.renameWires
          targetRenaming)).symm.trans
        (denoteRegion_renameWires model.toPreModel definitionEnv
          commonEnv targetRenaming
          ledger.frame.targetScope.frame.siteBody)
  have moved :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
      sourceRenaming
      ledger.frame.sourceScope.frame.siteBody).symm.trans
      ((UniformIntrinsicRegion.abstractApplied_denotes model.toPreModel
        definitionEnv commonEnv
        (.here :
          Var
            ((.rel sourceArguments) ::
              ledger.frame.targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        (ledger.frame.sourceScope.frame.siteBody.renameWires
          sourceRenaming)).trans
        (cylinder.trans targetAbstract))
  simpa [commonEnv, sourceRenaming, targetRenaming, Env.comp] using moved

theorem backwardSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (targetEnv :
      Env model.toPreModel
        ledger.frame.targetScope.frame.visible.sigs) :
    denoteRegion model.toPreModel definitionEnv
        (Env.comp
          (targetEnv.extend
            (ledger.backward model
              (targetEnv _ ledger.frame.targetHead)))
          (ledger.frame.alignment.sourceRenaming
            ledger.frame.sourceSignature))
        ledger.frame.sourceScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv targetEnv
        ledger.frame.targetScope.frame.siteBody := by
  let targetRelation :=
    targetEnv _ ledger.frame.targetHead
  let sourceRelation := ledger.backward model targetRelation
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceRenaming :
      WireRenaming ledger.frame.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    ledger.frame.alignment.sourceRenaming
      ledger.frame.sourceSignature
  let targetRenaming :
      WireRenaming ledger.frame.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  have envExact :
      Env.comp commonEnv ledger.accepted.receipt.embedding =
        commonEnv := by
    funext signature value
    simp only [Env.comp]
    rw [ledger.accepted.embedding_exact value]
  have cylinder :=
    ledger.accepted.receipt.backward_denotes
      ledger.accepted.consistent model.toPreModel definitionEnv
      commonEnv commonEnv envExact
      (model.toPreModel.apply targetRelation)
  rw [ledger.accepted.smaller_exact,
    ledger.accepted.larger_exact] at cylinder
  have sourceSiteExact :
      model.toPreModel.apply
          (commonEnv _ (.here :
            Var
              ((.rel sourceArguments) ::
                ledger.frame.targetScope.frame.visible.sigs)
              (.rel sourceArguments))) =
        cylindricalProject ledger.insertion
          (model.toPreModel.apply targetRelation) := by
    funext values
    apply propext
    change
      model.toPreModel.apply sourceRelation values ↔
        cylindricalProject ledger.insertion
          (model.toPreModel.apply targetRelation) values
    exact apply_reifyRelation model _ values
  have sourceAbstract :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        (sourceCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (cylindricalProject ledger.insertion
            (model.toPreModel.apply targetRelation)) := by
    rw [← sourceSiteExact]
    exact
      (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
        sourceRenaming
        ledger.frame.sourceScope.frame.siteBody).symm.trans
        (UniformIntrinsicRegion.abstractApplied_denotes
          model.toPreModel definitionEnv commonEnv
          (.here :
            Var
              ((.rel sourceArguments) ::
                ledger.frame.targetScope.frame.visible.sigs)
              (.rel sourceArguments))
          (ledger.frame.sourceScope.frame.siteBody.renameWires
            sourceRenaming))
  have targetAbstract :
      (targetCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    (UniformIntrinsicRegion.abstractApplied_denotes
      model.toPreModel definitionEnv commonEnv
      (.there ledger.frame.targetHead)
      (ledger.frame.targetScope.frame.siteBody.renameWires
        targetRenaming)).symm.trans
      (denoteRegion_renameWires model.toPreModel definitionEnv
        commonEnv targetRenaming
        ledger.frame.targetScope.frame.siteBody)
  have moved :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    sourceAbstract.trans (cylinder.trans targetAbstract)
  simpa [commonEnv, sourceRenaming, targetRenaming, sourceRelation,
    targetRelation, Env.comp] using moved

end ArityShiftLedger

namespace ArityUnshiftLedger

noncomputable def forward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments)) :
    model.toPreModel.Domain (.rel result.targetArguments) :=
  reifyRelation model
    (cylindricalProject ledger.insertion
      (model.toPreModel.apply sourceRelation))

noncomputable def backward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (targetRelation :
      model.toPreModel.Domain (.rel result.targetArguments)) :
    model.toPreModel.Domain (.rel sourceArguments) :=
  reifyRelation model
    (cylindricalLift ledger.insertion
      (model.toPreModel.apply targetRelation))

theorem forwardSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments))
    (targetEnv :
      Env model.toPreModel
        ledger.frame.targetScope.frame.visible.sigs)
    (targetHeadExact :
      targetEnv _ ledger.frame.targetHead =
        ledger.forward model sourceRelation) :
    denoteRegion model.toPreModel definitionEnv
        (Env.comp (targetEnv.extend sourceRelation)
          (ledger.frame.alignment.sourceRenaming
            ledger.frame.sourceSignature))
        ledger.frame.sourceScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv targetEnv
        ledger.frame.targetScope.frame.siteBody := by
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceRenaming :
      WireRenaming ledger.frame.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    ledger.frame.alignment.sourceRenaming
      ledger.frame.sourceSignature
  let targetRenaming :
      WireRenaming ledger.frame.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  have envExact :
      Env.comp commonEnv ledger.accepted.receipt.embedding =
        commonEnv := by
    funext signature value
    simp only [Env.comp]
    rw [ledger.accepted.embedding_exact value]
  have cylinder :=
    ledger.accepted.receipt.backward_denotes
      ledger.accepted.consistent model.toPreModel definitionEnv
      commonEnv commonEnv envExact
      (model.toPreModel.apply sourceRelation)
  rw [ledger.accepted.smaller_exact,
    ledger.accepted.larger_exact] at cylinder
  have targetSiteExact :
      model.toPreModel.apply
          (commonEnv _ (.there ledger.frame.targetHead)) =
        cylindricalProject ledger.insertion
          (model.toPreModel.apply sourceRelation) := by
    funext values
    apply propext
    change
      model.toPreModel.apply
          (targetEnv _ ledger.frame.targetHead) values ↔
        cylindricalProject ledger.insertion
          (model.toPreModel.apply sourceRelation) values
    rw [targetHeadExact]
    exact apply_reifyRelation model _ values
  have sourceAbstract :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        (sourceCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation) :=
    (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
      sourceRenaming
      ledger.frame.sourceScope.frame.siteBody).symm.trans
      (UniformIntrinsicRegion.abstractApplied_denotes
        model.toPreModel definitionEnv commonEnv
        (.here :
          Var
            ((.rel sourceArguments) ::
              ledger.frame.targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        (ledger.frame.sourceScope.frame.siteBody.renameWires
          sourceRenaming))
  have targetAbstract :
      (targetCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (cylindricalProject ledger.insertion
            (model.toPreModel.apply sourceRelation)) ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody := by
    rw [← targetSiteExact]
    exact
      (UniformIntrinsicRegion.abstractApplied_denotes
        model.toPreModel definitionEnv commonEnv
        (.there ledger.frame.targetHead)
        (ledger.frame.targetScope.frame.siteBody.renameWires
          targetRenaming)).symm.trans
        (denoteRegion_renameWires model.toPreModel definitionEnv
          commonEnv targetRenaming
          ledger.frame.targetScope.frame.siteBody)
  have moved :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    sourceAbstract.trans (cylinder.symm.trans targetAbstract)
  simpa [commonEnv, sourceRenaming, targetRenaming, Env.comp] using moved

theorem backwardSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (targetEnv :
      Env model.toPreModel
        ledger.frame.targetScope.frame.visible.sigs) :
    denoteRegion model.toPreModel definitionEnv
        (Env.comp
          (targetEnv.extend
            (ledger.backward model
              (targetEnv _ ledger.frame.targetHead)))
          (ledger.frame.alignment.sourceRenaming
            ledger.frame.sourceSignature))
        ledger.frame.sourceScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv targetEnv
        ledger.frame.targetScope.frame.siteBody := by
  let targetRelation :=
    targetEnv _ ledger.frame.targetHead
  let sourceRelation := ledger.backward model targetRelation
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceRenaming :
      WireRenaming ledger.frame.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    ledger.frame.alignment.sourceRenaming
      ledger.frame.sourceSignature
  let targetRenaming :
      WireRenaming ledger.frame.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          ledger.frame.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  have envExact :
      Env.comp commonEnv ledger.accepted.receipt.embedding =
        commonEnv := by
    funext signature value
    simp only [Env.comp]
    rw [ledger.accepted.embedding_exact value]
  have cylinder :=
    ledger.accepted.receipt.forward_denotes
      ledger.accepted.consistent model.toPreModel definitionEnv
      commonEnv commonEnv envExact
      (model.toPreModel.apply targetRelation)
  rw [ledger.accepted.smaller_exact,
    ledger.accepted.larger_exact] at cylinder
  have sourceSiteExact :
      model.toPreModel.apply
          (commonEnv _ (.here :
            Var
              ((.rel sourceArguments) ::
                ledger.frame.targetScope.frame.visible.sigs)
              (.rel sourceArguments))) =
        cylindricalLift ledger.insertion
          (model.toPreModel.apply targetRelation) := by
    funext values
    apply propext
    change
      model.toPreModel.apply sourceRelation values ↔
        cylindricalLift ledger.insertion
          (model.toPreModel.apply targetRelation) values
    exact apply_reifyRelation model _ values
  have sourceAbstract :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        (sourceCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (cylindricalLift ledger.insertion
            (model.toPreModel.apply targetRelation)) := by
    rw [← sourceSiteExact]
    exact
      (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
        sourceRenaming
        ledger.frame.sourceScope.frame.siteBody).symm.trans
        (UniformIntrinsicRegion.abstractApplied_denotes
          model.toPreModel definitionEnv commonEnv
          (.here :
            Var
              ((.rel sourceArguments) ::
                ledger.frame.targetScope.frame.visible.sigs)
              (.rel sourceArguments))
          (ledger.frame.sourceScope.frame.siteBody.renameWires
            sourceRenaming))
  have targetAbstract :
      (targetCylindricalShape ledger.frame).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    (UniformIntrinsicRegion.abstractApplied_denotes
      model.toPreModel definitionEnv commonEnv
      (.there ledger.frame.targetHead)
      (ledger.frame.targetScope.frame.siteBody.renameWires
        targetRenaming)).symm.trans
      (denoteRegion_renameWires model.toPreModel definitionEnv
        commonEnv targetRenaming
        ledger.frame.targetScope.frame.siteBody)
  have moved :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          ledger.frame.sourceScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          ledger.frame.targetScope.frame.siteBody :=
    sourceAbstract.trans (cylinder.symm.trans targetAbstract)
  simpa [commonEnv, sourceRenaming, targetRenaming, sourceRelation,
    targetRelation, Env.comp] using moved

end ArityUnshiftLedger

namespace ArgumentFrameFactorization

theorem reconstructSource
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (factorization :
      ArgumentFrameFactorization result sourceArguments)
    (sourceEnv :
      Env pre factorization.sourceScope.frame.visible.sigs)
    (targetRelation :
      pre.Domain (.rel result.targetArguments)) :
    let targetEnv :
        Env pre factorization.targetScope.frame.visible.sigs :=
      Env.comp (sourceEnv.extend targetRelation)
        (factorization.alignment.targetRenaming
          result.targetWire_signature)
    Env.comp
        (targetEnv.extend
          (sourceEnv _ factorization.sourceHead))
        (factorization.alignment.sourceRenaming
          factorization.sourceSignature) =
      sourceEnv := by
  dsimp only
  funext signature value
  simp only [Env.comp]
  by_cases isHead :
      ConcreteElaboration.WireContext.origin source.val
          factorization.sourceScope.frame.visible.ids value =
        wire
  · have signatureExact :=
      ConcreteElaboration.WireContext.origin_signature source.val
        factorization.sourceScope.frame.visible.ids value
    rw [isHead, factorization.sourceSignature] at signatureExact
    cases signatureExact
    have valueExact :
        value = factorization.sourceHead :=
      InsertionCompilation.NaturalityInternal.origin_injective source.val
        factorization.sourceScope.frame.visible.ids
        (siteVisibleNodup factorization.sourceScope)
        (isHead.trans factorization.sourceHead_origin.symm)
    subst value
    rw [factorization.alignment.sourceRenaming_head
      factorization.sourceSignature factorization.sourceHead
      factorization.sourceHead_origin]
    rfl
  · have sourceMapped :
        factorization.alignment.sourceRenaming
            factorization.sourceSignature value =
          .there
            (factorization.alignment.sourceFallback value isHead) := by
      simp [RetainedHeadAlignment.sourceRenaming, isHead]
    rw [sourceMapped]
    simp only [Env.comp, Env.extend_there]
    rw [factorization.alignment.targetRenaming_sourceFallback
      (siteVisibleNodup factorization.sourceScope)
      result.targetWire_signature value isHead]
    rfl

theorem localEquivalentWith
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (factorization :
      ArgumentFrameFactorization result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (forward :
      model.toPreModel.Domain (.rel sourceArguments) →
        model.toPreModel.Domain (.rel result.targetArguments))
    (backward :
      model.toPreModel.Domain (.rel result.targetArguments) →
        model.toPreModel.Domain (.rel sourceArguments))
    (forwardDenotes :
      ∀ (sourceRelation)
        (targetEnv :
          Env model.toPreModel
            factorization.targetScope.frame.visible.sigs),
        targetEnv _ factorization.targetHead =
            forward sourceRelation →
          (denoteRegion model.toPreModel definitionEnv
              (Env.comp (targetEnv.extend sourceRelation)
                (factorization.alignment.sourceRenaming
                  factorization.sourceSignature))
              factorization.sourceScope.frame.siteBody ↔
            denoteRegion model.toPreModel definitionEnv targetEnv
              factorization.targetScope.frame.siteBody))
    (backwardDenotes :
      ∀ (targetEnv :
          Env model.toPreModel
            factorization.targetScope.frame.visible.sigs),
        denoteRegion model.toPreModel definitionEnv
            (Env.comp
              (targetEnv.extend
                (backward
                  (targetEnv _ factorization.targetHead)))
              (factorization.alignment.sourceRenaming
                factorization.sourceSignature))
            factorization.sourceScope.frame.siteBody ↔
          denoteRegion model.toPreModel definitionEnv targetEnv
            factorization.targetScope.frame.siteBody)
    (siteEnv :
      Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody)) ↔
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody)) := by
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceLocalHolds⟩
    let sourceLocalEnv :=
      ContentShapeSemantics.extendValues sourceValues siteEnv
    let sourceEnv :=
      factorization.context.sourceEnvironment sourceLocalEnv
    let sourceRelation :=
      sourceEnv _ factorization.sourceHead
    let targetRelation := forward sourceRelation
    let targetEnv :
        Env model.toPreModel
          factorization.targetScope.frame.visible.sigs :=
      Env.comp (sourceEnv.extend targetRelation)
        (factorization.alignment.targetRenaming
          result.targetWire_signature)
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          factorization.sourceScope.frame.siteBody :=
      (factorization.context.sourceBody_denotes model.toPreModel
        definitionEnv sourceLocalEnv
        factorization.sourceScope.frame.siteBody).mp sourceLocalHolds
    have reconstructed :
        Env.comp (targetEnv.extend sourceRelation)
            (factorization.alignment.sourceRenaming
              factorization.sourceSignature) =
          sourceEnv := by
      simpa [sourceRelation, targetRelation, targetEnv] using
        factorization.reconstructSource sourceEnv targetRelation
    have targetHeadExact :
        targetEnv _ factorization.targetHead = targetRelation := by
      have targetHeadMap :=
        factorization.alignment.targetRenaming_head
          result.targetWire_signature factorization.targetHead
          factorization.targetHead_origin
      simp [targetEnv, targetRelation, Env.comp, targetHeadMap]
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          factorization.targetScope.frame.siteBody :=
      (forwardDenotes sourceRelation targetEnv targetHeadExact).mp
        (by rw [reconstructed]; exact sourceHolds)
    let targetLocalEnv :=
      factorization.context.targetLocalEnvironment targetEnv
    have targetLocalHolds :
        denoteRegion model.toPreModel definitionEnv targetLocalEnv
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody) := by
      apply
        (factorization.context.targetBody_denotes model.toPreModel
          definitionEnv targetLocalEnv
          factorization.targetScope.frame.siteBody).mpr
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetEnvironment_local]
      exact targetHolds
    have targetOuter :
        ∀ {signature : Sig}
          (value : Var factorization.context.siteOuter signature),
          targetLocalEnv signature
              (Var.appendRight
                (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetLocalEnvironment_outer]
      calc
        targetEnv signature
            (factorization.context.targetOuterEmbedding value) =
          (sourceEnv.extend targetRelation) signature
            (factorization.alignment.targetRenaming
              result.targetWire_signature
              (factorization.context.targetOuterEmbedding value)) := rfl
        _ =
          (sourceEnv.extend targetRelation) signature
            (.there
              (factorization.context.sourceOuterEmbedding value)) := by
                rw [factorization.targetOuter.agrees value]
        _ =
          sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) := rfl
        _ =
          sourceLocalEnv signature
            (Var.appendRight
              (ContentAlignment.localSignatures source.val
                (source.val.wires wire).scope) value) :=
            factorization.context.sourceEnvironment_outer
              sourceLocalEnv value
        _ = siteEnv signature value :=
          ContentShapeSemantics.extendValues_outer sourceValues siteEnv value
    refine
      ⟨ContentShapeSemantics.valuesFromEnv
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          targetLocalEnv, ?_⟩
    rw [ContentShapeSemantics.extendValues_from
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      targetLocalEnv siteEnv targetOuter]
    exact targetLocalHolds
  · rintro ⟨targetValues, targetLocalHolds⟩
    let targetLocalEnv :=
      ContentShapeSemantics.extendValues targetValues siteEnv
    let targetEnv :=
      factorization.context.targetEnvironment targetLocalEnv
    let targetRelation :=
      targetEnv _ factorization.targetHead
    let sourceRelation := backward targetRelation
    let sourceEnv :
        Env model.toPreModel
          factorization.sourceScope.frame.visible.sigs :=
      Env.comp (targetEnv.extend sourceRelation)
        (factorization.alignment.sourceRenaming
          factorization.sourceSignature)
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          factorization.targetScope.frame.siteBody :=
      (factorization.context.targetBody_denotes model.toPreModel
        definitionEnv targetLocalEnv
        factorization.targetScope.frame.siteBody).mp targetLocalHolds
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          factorization.sourceScope.frame.siteBody := by
      have moved := (backwardDenotes targetEnv).mpr targetHolds
      simpa [sourceEnv, sourceRelation, targetRelation] using moved
    let sourceLocalEnv :=
      factorization.context.sourceLocalEnvironment sourceEnv
    have sourceLocalHolds :
        denoteRegion model.toPreModel definitionEnv sourceLocalEnv
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody) := by
      apply
        (factorization.context.sourceBody_denotes model.toPreModel
          definitionEnv sourceLocalEnv
          factorization.sourceScope.frame.siteBody).mpr
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceEnvironment_local]
      exact sourceHolds
    have sourceOuter :
        ∀ {signature : Sig}
          (value : Var factorization.context.siteOuter signature),
          sourceLocalEnv signature
              (Var.appendRight
                (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceLocalEnvironment_outer]
      calc
        sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) =
          (targetEnv.extend sourceRelation) signature
            (factorization.alignment.sourceRenaming
              factorization.sourceSignature
              (factorization.context.sourceOuterEmbedding value)) := rfl
        _ =
          (targetEnv.extend sourceRelation) signature
            (.there
              (factorization.context.targetOuterEmbedding value)) := by
                rw [factorization.sourceOuter.agrees value]
        _ =
          targetEnv signature
            (factorization.context.targetOuterEmbedding value) := rfl
        _ =
          targetLocalEnv signature
            (Var.appendRight
              (ContentAlignment.localSignatures result.checked.val
                (result.checked.val.wires result.targetWire).scope)
              value) :=
            factorization.context.targetEnvironment_outer
              targetLocalEnv value
        _ = siteEnv signature value :=
          ContentShapeSemantics.extendValues_outer targetValues siteEnv value
    refine
      ⟨ContentShapeSemantics.valuesFromEnv
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          sourceLocalEnv, ?_⟩
    rw [ContentShapeSemantics.extendValues_from
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      sourceLocalEnv siteEnv sourceOuter]
    exact sourceLocalHolds

theorem equivalentWith
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (factorization :
      ArgumentFrameFactorization result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (forward :
      model.toPreModel.Domain (.rel sourceArguments) →
        model.toPreModel.Domain (.rel result.targetArguments))
    (backward :
      model.toPreModel.Domain (.rel result.targetArguments) →
        model.toPreModel.Domain (.rel sourceArguments))
    (forwardDenotes :
      ∀ (sourceRelation)
        (targetEnv :
          Env model.toPreModel
            factorization.targetScope.frame.visible.sigs),
        targetEnv _ factorization.targetHead =
            forward sourceRelation →
          (denoteRegion model.toPreModel definitionEnv
              (Env.comp (targetEnv.extend sourceRelation)
                (factorization.alignment.sourceRenaming
                  factorization.sourceSignature))
              factorization.sourceScope.frame.siteBody ↔
            denoteRegion model.toPreModel definitionEnv targetEnv
              factorization.targetScope.frame.siteBody))
    (backwardDenotes :
      ∀ (targetEnv :
          Env model.toPreModel
            factorization.targetScope.frame.visible.sigs),
        denoteRegion model.toPreModel definitionEnv
            (Env.comp
              (targetEnv.extend
                (backward
                  (targetEnv _ factorization.targetHead)))
              (factorization.alignment.sourceRenaming
                factorization.sourceSignature))
            factorization.sourceScope.frame.siteBody ↔
          denoteRegion model.toPreModel definitionEnv targetEnv
            factorization.targetScope.frame.siteBody) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      factorization.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      factorization.targetScope model.toPreModel definitionEnv]
  exact
    factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        factorization.localEquivalentWith model definitionEnv
          forward backward forwardDenotes backwardDenotes siteEnv)

end ArgumentFrameFactorization

namespace ArityShiftLedger

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked :=
  ledger.frame.equivalentWith model definitionEnv
    (ledger.forward model) (ledger.backward model)
    (ledger.forwardSite model definitionEnv)
    (ledger.backwardSite model definitionEnv)

end ArityShiftLedger

namespace ArityUnshiftLedger

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked :=
  ledger.frame.equivalentWith model definitionEnv
    (ledger.forward model) (ledger.backward model)
    (ledger.forwardSite model definitionEnv)
    (ledger.backwardSite model definitionEnv)

end ArityUnshiftLedger

namespace ScopedArityShiftLedger

noncomputable def forward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments)) :
    model.toPreModel.Domain (.rel result.targetArguments) :=
  reifyRelation model
    (cylindricalLift ledger.insertion
      (model.toPreModel.apply sourceRelation))

noncomputable def backward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (targetRelation :
      model.toPreModel.Domain (.rel result.targetArguments)) :
    model.toPreModel.Domain (.rel sourceArguments) :=
  reifyRelation model
    (cylindricalProject ledger.insertion
      (model.toPreModel.apply targetRelation))

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityShiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      ledger.frame.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      ledger.frame.targetScope model.toPreModel definitionEnv]
  apply
    ledger.frame.context.closeDenotes model.toPreModel definitionEnv
  intro siteEnv
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceHolds⟩
    let sourceSplit :=
      ledger.frame.sourceRemoval.splitValues sourceValues
    let sourceRelation := sourceSplit.1
    let sourceReduced := sourceSplit.2
    let targetRelation := ledger.forward model sourceRelation
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            ledger.frame.context.siteOuter) :=
      (siteEnv.extend targetRelation).extend sourceRelation
    have sourceNormalized :
        ledger.frame.sourceShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply sourceRelation) := by
      apply
        (normalizedArgumentShape_denotes
          ledger.frame.sourceRemoval localSourceHead
          (ledger.frame.context.sourceBody
            ledger.frame.sourceScope.frame.siteBody)
          model.toPreModel definitionEnv commonEnv sourceRelation rfl).mpr
      refine ⟨sourceReduced, ?_⟩
      simpa [sourceSplit, sourceRelation, sourceReduced, commonEnv,
        localOuterRenaming, Env.comp] using sourceHolds
    have envExact :
        Env.comp commonEnv ledger.accepted.receipt.embedding =
          commonEnv := by
      funext signature value
      simp only [Env.comp]
      rw [ledger.accepted.embedding_exact value]
    have cylinder :=
      ledger.accepted.receipt.forward_denotes
        ledger.accepted.consistent model.toPreModel definitionEnv
        commonEnv commonEnv envExact
        (model.toPreModel.apply sourceRelation)
    rw [ledger.accepted.smaller_exact,
      ledger.accepted.larger_exact] at cylinder
    have targetCylinder := cylinder.mp sourceNormalized
    have targetNormalized :
        ledger.frame.targetShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply targetRelation) := by
      apply
        (ledger.frame.targetShape.denote_site_congr model.toPreModel
          definitionEnv commonEnv
          (model.toPreModel.apply targetRelation)
          (cylindricalLift ledger.insertion
            (model.toPreModel.apply sourceRelation))
          (fun values => by
            change
              model.toPreModel.apply
                  (ledger.forward model sourceRelation) values ↔
                cylindricalLift ledger.insertion
                  (model.toPreModel.apply sourceRelation) values
            exact apply_reifyRelation model _ values)).mpr
      exact targetCylinder
    obtain ⟨targetReduced, targetHolds⟩ :=
      (normalizedArgumentShape_denotes
        ledger.frame.targetRemoval localTargetHead
        (ledger.frame.context.targetBody
          ledger.frame.targetScope.frame.siteBody)
        model.toPreModel definitionEnv commonEnv targetRelation rfl).mp
        targetNormalized
    refine
      ⟨ledger.frame.targetRemoval.assembleValues targetRelation
          targetReduced, ?_⟩
    simpa [commonEnv, localOuterRenaming, Env.comp] using targetHolds
  · rintro ⟨targetValues, targetHolds⟩
    let targetSplit :=
      ledger.frame.targetRemoval.splitValues targetValues
    let targetRelation := targetSplit.1
    let targetReduced := targetSplit.2
    let sourceRelation := ledger.backward model targetRelation
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            ledger.frame.context.siteOuter) :=
      (siteEnv.extend targetRelation).extend sourceRelation
    have targetNormalized :
        ledger.frame.targetShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply targetRelation) := by
      apply
        (normalizedArgumentShape_denotes
          ledger.frame.targetRemoval localTargetHead
          (ledger.frame.context.targetBody
            ledger.frame.targetScope.frame.siteBody)
          model.toPreModel definitionEnv commonEnv targetRelation rfl).mpr
      refine ⟨targetReduced, ?_⟩
      simpa [targetSplit, targetRelation, targetReduced, commonEnv,
        localOuterRenaming, Env.comp] using targetHolds
    have envExact :
        Env.comp commonEnv ledger.accepted.receipt.embedding =
          commonEnv := by
      funext signature value
      simp only [Env.comp]
      rw [ledger.accepted.embedding_exact value]
    have cylinder :=
      ledger.accepted.receipt.backward_denotes
        ledger.accepted.consistent model.toPreModel definitionEnv
        commonEnv commonEnv envExact
        (model.toPreModel.apply targetRelation)
    rw [ledger.accepted.smaller_exact,
      ledger.accepted.larger_exact] at cylinder
    have sourceCylinder := cylinder.mpr targetNormalized
    have sourceNormalized :
        ledger.frame.sourceShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply sourceRelation) := by
      apply
        (ledger.frame.sourceShape.denote_site_congr model.toPreModel
          definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation)
          (cylindricalProject ledger.insertion
            (model.toPreModel.apply targetRelation))
          (fun values => by
            change
              model.toPreModel.apply
                  (ledger.backward model targetRelation) values ↔
                cylindricalProject ledger.insertion
                  (model.toPreModel.apply targetRelation) values
            exact apply_reifyRelation model _ values)).mpr
      exact sourceCylinder
    obtain ⟨sourceReduced, sourceHolds⟩ :=
      (normalizedArgumentShape_denotes
        ledger.frame.sourceRemoval localSourceHead
        (ledger.frame.context.sourceBody
          ledger.frame.sourceScope.frame.siteBody)
        model.toPreModel definitionEnv commonEnv sourceRelation rfl).mp
        sourceNormalized
    refine
      ⟨ledger.frame.sourceRemoval.assembleValues sourceRelation
          sourceReduced, ?_⟩
    simpa [commonEnv, localOuterRenaming, Env.comp] using sourceHolds

end ScopedArityShiftLedger

namespace ScopedArityUnshiftLedger

noncomputable def forward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (sourceRelation :
      model.toPreModel.Domain (.rel sourceArguments)) :
    model.toPreModel.Domain (.rel result.targetArguments) :=
  reifyRelation model
    (cylindricalProject ledger.insertion
      (model.toPreModel.apply sourceRelation))

noncomputable def backward
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (targetRelation :
      model.toPreModel.Domain (.rel result.targetArguments)) :
    model.toPreModel.Domain (.rel sourceArguments) :=
  reifyRelation model
    (cylindricalLift ledger.insertion
      (model.toPreModel.apply targetRelation))

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {fixedSignature : Sig}
    (ledger :
      ScopedArityUnshiftLedger result sourceArguments fixedSignature)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      ledger.frame.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      ledger.frame.targetScope model.toPreModel definitionEnv]
  apply
    ledger.frame.context.closeDenotes model.toPreModel definitionEnv
  intro siteEnv
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceHolds⟩
    let sourceSplit :=
      ledger.frame.sourceRemoval.splitValues sourceValues
    let sourceRelation := sourceSplit.1
    let sourceReduced := sourceSplit.2
    let targetRelation := ledger.forward model sourceRelation
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            ledger.frame.context.siteOuter) :=
      (siteEnv.extend targetRelation).extend sourceRelation
    have sourceNormalized :
        ledger.frame.sourceShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply sourceRelation) := by
      apply
        (normalizedArgumentShape_denotes
          ledger.frame.sourceRemoval localSourceHead
          (ledger.frame.context.sourceBody
            ledger.frame.sourceScope.frame.siteBody)
          model.toPreModel definitionEnv commonEnv sourceRelation rfl).mpr
      refine ⟨sourceReduced, ?_⟩
      simpa [sourceSplit, sourceRelation, sourceReduced, commonEnv,
        localOuterRenaming, Env.comp] using sourceHolds
    have envExact :
        Env.comp commonEnv ledger.accepted.receipt.embedding =
          commonEnv := by
      funext signature value
      simp only [Env.comp]
      rw [ledger.accepted.embedding_exact value]
    have cylinder :=
      ledger.accepted.receipt.backward_denotes
        ledger.accepted.consistent model.toPreModel definitionEnv
        commonEnv commonEnv envExact
        (model.toPreModel.apply sourceRelation)
    rw [ledger.accepted.smaller_exact,
      ledger.accepted.larger_exact] at cylinder
    have targetCylinder := cylinder.mpr sourceNormalized
    have targetNormalized :
        ledger.frame.targetShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply targetRelation) := by
      apply
        (ledger.frame.targetShape.denote_site_congr model.toPreModel
          definitionEnv commonEnv
          (model.toPreModel.apply targetRelation)
          (cylindricalProject ledger.insertion
            (model.toPreModel.apply sourceRelation))
          (fun values => by
            change
              model.toPreModel.apply
                  (ledger.forward model sourceRelation) values ↔
                cylindricalProject ledger.insertion
                  (model.toPreModel.apply sourceRelation) values
            exact apply_reifyRelation model _ values)).mpr
      exact targetCylinder
    obtain ⟨targetReduced, targetHolds⟩ :=
      (normalizedArgumentShape_denotes
        ledger.frame.targetRemoval localTargetHead
        (ledger.frame.context.targetBody
          ledger.frame.targetScope.frame.siteBody)
        model.toPreModel definitionEnv commonEnv targetRelation rfl).mp
        targetNormalized
    refine
      ⟨ledger.frame.targetRemoval.assembleValues targetRelation
          targetReduced, ?_⟩
    simpa [commonEnv, localOuterRenaming, Env.comp] using targetHolds
  · rintro ⟨targetValues, targetHolds⟩
    let targetSplit :=
      ledger.frame.targetRemoval.splitValues targetValues
    let targetRelation := targetSplit.1
    let targetReduced := targetSplit.2
    let sourceRelation := ledger.backward model targetRelation
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            ledger.frame.context.siteOuter) :=
      (siteEnv.extend targetRelation).extend sourceRelation
    have targetNormalized :
        ledger.frame.targetShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply targetRelation) := by
      apply
        (normalizedArgumentShape_denotes
          ledger.frame.targetRemoval localTargetHead
          (ledger.frame.context.targetBody
            ledger.frame.targetScope.frame.siteBody)
          model.toPreModel definitionEnv commonEnv targetRelation rfl).mpr
      refine ⟨targetReduced, ?_⟩
      simpa [targetSplit, targetRelation, targetReduced, commonEnv,
        localOuterRenaming, Env.comp] using targetHolds
    have envExact :
        Env.comp commonEnv ledger.accepted.receipt.embedding =
          commonEnv := by
      funext signature value
      simp only [Env.comp]
      rw [ledger.accepted.embedding_exact value]
    have cylinder :=
      ledger.accepted.receipt.forward_denotes
        ledger.accepted.consistent model.toPreModel definitionEnv
        commonEnv commonEnv envExact
        (model.toPreModel.apply targetRelation)
    rw [ledger.accepted.smaller_exact,
      ledger.accepted.larger_exact] at cylinder
    have sourceCylinder := cylinder.mp targetNormalized
    have sourceNormalized :
        ledger.frame.sourceShape.denote model.toPreModel definitionEnv
          commonEnv (model.toPreModel.apply sourceRelation) := by
      apply
        (ledger.frame.sourceShape.denote_site_congr model.toPreModel
          definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation)
          (cylindricalLift ledger.insertion
            (model.toPreModel.apply targetRelation))
          (fun values => by
            change
              model.toPreModel.apply
                  (ledger.backward model targetRelation) values ↔
                cylindricalLift ledger.insertion
                  (model.toPreModel.apply targetRelation) values
            exact apply_reifyRelation model _ values)).mpr
      exact sourceCylinder
    obtain ⟨sourceReduced, sourceHolds⟩ :=
      (normalizedArgumentShape_denotes
        ledger.frame.sourceRemoval localSourceHead
        (ledger.frame.context.sourceBody
          ledger.frame.sourceScope.frame.siteBody)
        model.toPreModel definitionEnv commonEnv sourceRelation rfl).mp
        sourceNormalized
    refine
      ⟨ledger.frame.sourceRemoval.assembleValues sourceRelation
          sourceReduced, ?_⟩
    simpa [commonEnv, localOuterRenaming, Env.comp] using sourceHolds

end ScopedArityUnshiftLedger

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
