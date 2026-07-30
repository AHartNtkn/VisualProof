import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalReflection

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace ExhaustedWireRemovalSemantics

open Internal

/-- The checked plain diagram obtained by deleting the exhausted wire. -/
def deletedCheckedDiagram
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions) :
    CheckedDiagram definitions :=
  ⟨Target source removed, targetWellFormed⟩

/--
The one canonical final-deletion receipt. It retains the exact plain site
compilation, the paired context zipper stopped above the dying scope, and the
two equations identifying those filled contexts with the checked roots.
-/
structure FinalDeletionOuterReceipt
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (bound :
      SiteCompilation source (source.val.wires removed).scope) where
  plain :
    SiteCompilation
      (deletedCheckedDiagram source removed targetWellFormed)
      (targetRegion source removed (source.val.wires removed).scope)
  reflected :
    AboveScopeReflection.{u} source removed
      (ConcreteElaboration.WireContext.empty source.val)
      (ConcreteElaboration.WireContext.empty (Target source removed))
      bound.frame plain.frame
  boundRootFill :
    bound.checked =
      reflected.sourceAbove.fill
        (ConcreteElaboration.finishRegion source.val
          reflected.sourceSiteOuter (source.val.wires removed).scope
          reflected.sourceBody)
  plainRootFill :
    plain.checked =
      reflected.targetAbove.fill
        (ConcreteElaboration.finishRegion (Target source removed)
          reflected.targetSiteOuter
          (targetRegion source removed (source.val.wires removed).scope)
          reflected.targetBody)

/--
Reflect a generated bound site receipt into the single plain outer receipt.
The exact target frame equation is retained by `SiteCompilation.ofFrame`;
there is no second site compiler run or search.
-/
theorem siteCompilation_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (bound :
      SiteCompilation source (source.val.wires removed).scope) :
    Nonempty
      (FinalDeletionOuterReceipt.{u} source removed targetWellFormed
        bound) := by
  have rootAbove :
      ConcreteElaboration.ContextAbove source.val
        (ConcreteElaboration.WireContext.empty source.val)
        source.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  obtain ⟨targetFrame, targetGenerated, ⟨reflected⟩⟩ :=
    compileRegionFrame_reflect_outer.{u} source removed targetWellFormed
      removedEndpoints (source.val.regionCount + 1) source.val.root
      (ConcreteElaboration.WireContext.empty (Target source removed))
      (ConcreteElaboration.WireContext.empty source.val)
      (empty_contexts_correspond source removed)
      (by simp [ConcreteElaboration.WireContext.empty])
      rootAbove bound.frame_generated
  let plain :
      SiteCompilation
        (deletedCheckedDiagram source removed targetWellFormed)
        (targetRegion source removed (source.val.wires removed).scope) :=
    SiteCompilation.ofFrame targetFrame (by
      simpa [deletedCheckedDiagram, target_regionCount, target_root] using
        targetGenerated)
  have sourceRoot :
      bound.checked =
        reflected.sourceAbove.fill
          (ConcreteElaboration.finishRegion source.val
            reflected.sourceSiteOuter (source.val.wires removed).scope
            reflected.sourceBody) :=
    bound.frame_fills_checked.symm.trans reflected.sourceFill
  have targetRoot :
      plain.checked =
        reflected.targetAbove.fill
          (ConcreteElaboration.finishRegion (Target source removed)
            reflected.targetSiteOuter
            (targetRegion source removed
              (source.val.wires removed).scope)
            reflected.targetBody) :=
    plain.frame_fills_checked.symm.trans reflected.targetFill
  exact
    ⟨{ plain := plain
       reflected := reflected
       boundRootFill := sourceRoot
       plainRootFill := targetRoot }⟩

namespace FinalDeletionOuterReceipt

/-- The exact stopped-above decomposition of the compiled bound source site. -/
def boundCanonical
    {source : CheckedDiagram definitions}
    {removed : source.val.WireId}
    {targetWellFormed : (Target source removed).WellFormed definitions}
    {bound :
      SiteCompilation source (source.val.wires removed).scope}
    (receipt :
      FinalDeletionOuterReceipt.{u} source removed targetWellFormed bound) :
    SiteCompilation.AboveScopeDecomposition bound where
  siteOuter := receipt.reflected.sourceSiteOuter
  above := receipt.reflected.sourceAbove
  visibleExact := receipt.reflected.sourceVisibleExact
  contextDecomposition := receipt.reflected.sourceDecomposition

/--
Lift the receipt-owned dying-scope body law through the retained outer
contexts for the caller-selected removed value. Even cut depth points
plain-to-bound; odd depth reverses that outer direction.
-/
theorem scopeParity
    {source : CheckedDiagram definitions}
    {removed : source.val.WireId}
    {targetWellFormed : (Target source removed).WellFormed definitions}
    {bound :
      SiteCompilation source (source.val.wires removed).scope}
    (receipt :
      FinalDeletionOuterReceipt.{u} source removed targetWellFormed bound)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (fixed : Env pre [])
    (specified :
      ∀ (targetOuterEnv :
          Env pre receipt.reflected.targetSiteOuter.sigs)
        (targetValues :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig)),
        pre.Domain (source.val.wires removed).sig)
    :
    (receipt.reflected.sourceAbove.cutDepth % 2 = 0 →
      denoteRegion pre definitionEnv fixed
          (receipt.reflected.targetAbove.fill
            (ConcreteElaboration.finishRegion (Target source removed)
              receipt.reflected.targetSiteOuter
              (targetRegion source removed
                (source.val.wires removed).scope)
              receipt.reflected.targetBody)) →
        denoteRegion pre definitionEnv
          (Env.comp fixed
            (contextProjection source removed
              (ConcreteElaboration.WireContext.empty
                (Target source removed))
              (ConcreteElaboration.WireContext.empty source.val)
              receipt.reflected.outerCorrespond
              receipt.reflected.outerRemovedAbsent))
          (receipt.reflected.sourceAbove.fill
            (ConcreteElaboration.finishRegion source.val
              receipt.reflected.sourceSiteOuter
              (source.val.wires removed).scope
              receipt.reflected.sourceBody))) ∧
    (receipt.reflected.sourceAbove.cutDepth % 2 = 1 →
      denoteRegion pre definitionEnv
          (Env.comp fixed
            (contextProjection source removed
              (ConcreteElaboration.WireContext.empty
                (Target source removed))
              (ConcreteElaboration.WireContext.empty source.val)
              receipt.reflected.outerCorrespond
              receipt.reflected.outerRemovedAbsent))
          (receipt.reflected.sourceAbove.fill
            (ConcreteElaboration.finishRegion source.val
              receipt.reflected.sourceSiteOuter
              (source.val.wires removed).scope
              receipt.reflected.sourceBody)) →
        denoteRegion pre definitionEnv fixed
          (receipt.reflected.targetAbove.fill
            (ConcreteElaboration.finishRegion (Target source removed)
              receipt.reflected.targetSiteOuter
              (targetRegion source removed
                (source.val.wires removed).scope)
              receipt.reflected.targetBody))) := by
  apply receipt.reflected.composable.toSemanticZipper.targetToSource
    pre definitionEnv
  intro descendant _preserves targetFinished
  exact
    finishDyingRegion_implication source removed
      receipt.reflected.targetSiteOuter
      receipt.reflected.sourceSiteOuter
      receipt.reflected.siteCorrespond
      receipt.reflected.siteRemovedAbsent
      receipt.reflected.sourceVisibleNodup pre definitionEnv descendant
      (specified descendant) receipt.reflected.targetBody
      receipt.reflected.sourceBody
      (fun chosen targetEnv =>
        receipt.reflected.localBodyLaw pre definitionEnv chosen targetEnv)
      targetFinished

/-- Specialize `scopeParity` to the exact bound and plain checked roots. -/
theorem rootParity
    {source : CheckedDiagram definitions}
    {removed : source.val.WireId}
    {targetWellFormed : (Target source removed).WellFormed definitions}
    {bound :
      SiteCompilation source (source.val.wires removed).scope}
    (receipt :
      FinalDeletionOuterReceipt.{u} source removed targetWellFormed bound)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (specified :
      ∀ (targetOuterEnv :
          Env pre receipt.reflected.targetSiteOuter.sigs)
        (targetValues :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig)),
        pre.Domain (source.val.wires removed).sig)
    :
    (receipt.reflected.sourceAbove.cutDepth % 2 = 0 →
      denoteRegion pre definitionEnv Env.empty receipt.plain.checked →
        denoteRegion pre definitionEnv Env.empty bound.checked) ∧
    (receipt.reflected.sourceAbove.cutDepth % 2 = 1 →
      denoteRegion pre definitionEnv Env.empty bound.checked →
        denoteRegion pre definitionEnv Env.empty receipt.plain.checked) := by
  have parity :=
    receipt.scopeParity pre definitionEnv Env.empty specified
  have emptySource :
      Env.comp (Env.empty : Env pre [])
          (contextProjection source removed
            (ConcreteElaboration.WireContext.empty (Target source removed))
            (ConcreteElaboration.WireContext.empty source.val)
            receipt.reflected.outerCorrespond
            receipt.reflected.outerRemovedAbsent) =
        Env.empty := by
    funext sig value
    nomatch value
  constructor
  · intro even plainDenotes
    rw [receipt.plainRootFill] at plainDenotes
    have sourceDenotes := parity.1 even plainDenotes
    rw [emptySource] at sourceDenotes
    rw [receipt.boundRootFill]
    exact sourceDenotes
  · intro odd boundDenotes
    rw [receipt.boundRootFill] at boundDenotes
    have sourceDenotes :
        denoteRegion pre definitionEnv
            (Env.comp Env.empty
              (contextProjection source removed
                (ConcreteElaboration.WireContext.empty
                  (Target source removed))
                (ConcreteElaboration.WireContext.empty source.val)
                receipt.reflected.outerCorrespond
                receipt.reflected.outerRemovedAbsent))
            (receipt.reflected.sourceAbove.fill
              (ConcreteElaboration.finishRegion source.val
                receipt.reflected.sourceSiteOuter
                (source.val.wires removed).scope
                receipt.reflected.sourceBody)) := by
      simpa only [emptySource] using boundDenotes
    have targetDenotes := parity.2 odd sourceDenotes
    rw [receipt.plainRootFill]
    exact targetDenotes

end FinalDeletionOuterReceipt

end ExhaustedWireRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
