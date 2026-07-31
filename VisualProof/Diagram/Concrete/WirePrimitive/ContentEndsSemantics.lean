import VisualProof.Diagram.Concrete.WirePrimitive.ContentSemantics

namespace VisualProof

namespace ConcreteWirePrimitive.EndsDeleteResult.SiteLedger

open ConcreteWireQuantifier.SingletonRemovalSemantics
open ConcreteWireQuantifier.ExhaustedWireRemovalSemantics

universe u

/--
Deleting all applications is sound in the binder direction selected by the
acted scope. The final endpoint-free binder is reassigned a canonical
universal relation value before the folded site-erasure transport is applied.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : EndsDeleteResult source wire}
    (ledger : EndsDeleteResult.SiteLedger result)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    (ledger.sourceScope.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) ∧
    (ledger.sourceScope.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) := by
  let transport :=
    ledger.erasureTrace.universal_outer_transport
  cases transport with
  | mk sourceScope targetSite targetSiteEq targetScope sourceCanonical
      targetCanonical outerProjection visibleProjection
      visibleExtendsOuter visibleMapsWire body composable =>
    cases targetSiteEq
    obtain ⟨deletionReceipt⟩ :=
      ConcreteWireQuantifier.ExhaustedWireRemovalSemantics.siteCompilation_reflect
        ledger.erasureTrace.target ledger.erasureTrace.targetWire
        ledger.targetDeletionWellFormed
        ledger.erasureTrace.target_empty targetScope
    let sourceVisibleSigs :=
      congrArg ConcreteElaboration.WireContext.sigs
        sourceCanonical.visibleExact
    let targetVisibleSigs :=
      congrArg ConcreteElaboration.WireContext.sigs
        targetCanonical.visibleExact
    let sourceFinished :=
      ConcreteElaboration.finishRegion source.val
        sourceCanonical.siteOuter (source.val.wires wire).scope
        (sourceVisibleSigs ▸ sourceScope.frame.siteBody)
    let targetFinished :=
      ConcreteElaboration.finishRegion ledger.erasureTrace.target.val
        targetCanonical.siteOuter
        (ledger.erasureTrace.target.val.wires
          ledger.erasureTrace.targetWire).scope
        (targetVisibleSigs ▸ targetScope.frame.siteBody)
    have parity :=
      composable.toSemanticZipper.targetToSource model.toPreModel
        definitionEnv sourceFinished targetFinished Env.empty (by
          intro targetOuterEnv _preserves targetFinishedHolds
          obtain ⟨targetValues, targetBodyHolds⟩ :=
            (ConcreteElaboration.denote_finishRegion definitions
              ledger.erasureTrace.target.val targetCanonical.siteOuter
              (ledger.erasureTrace.target.val.wires
                ledger.erasureTrace.targetWire).scope
              model.toPreModel definitionEnv targetOuterEnv
              (targetVisibleSigs ▸ targetScope.frame.siteBody)).mp
                targetFinishedHolds
          let targetExtended :=
            ConcreteElaboration.extendEnvironment
              ledger.erasureTrace.target.val targetCanonical.siteOuter
              (ledger.erasureTrace.target.val.wires
                ledger.erasureTrace.targetWire).scope
              targetValues targetOuterEnv
          let targetFrameEnv :
              Env model.toPreModel targetScope.frame.visible.sigs :=
            targetVisibleSigs.symm ▸ targetExtended
          have targetFrameHolds :
              denoteRegion model.toPreModel definitionEnv targetFrameEnv
                targetScope.frame.siteBody := by
            apply
              (denoteRegion_transport targetVisibleSigs model.toPreModel
                definitionEnv targetFrameEnv
                targetScope.frame.siteBody).mpr
            rw [castEnv_roundtrip targetVisibleSigs targetExtended]
            exact targetBodyHolds
          obtain ⟨reassigned, universal, targetOuterAgreement,
              reassignedBody⟩ :=
            endpointFree_reassign_frame deletionReceipt targetCanonical
              model definitionEnv targetFrameEnv targetFrameHolds
          have sourceBodyHolds :
              denoteRegion model.toPreModel definitionEnv
                (Env.comp reassigned visibleProjection)
                sourceScope.frame.siteBody :=
            (body model.toPreModel definitionEnv reassigned universal).mp
              reassignedBody
          let sourceFrameEnv :=
            Env.comp reassigned visibleProjection
          let sourceExtended :
              Env model.toPreModel
                (sourceCanonical.siteOuter.extend
                  (source.val.wires wire).scope).sigs :=
            sourceVisibleSigs ▸ sourceFrameEnv
          let sourceValues :=
            ConcreteElaboration.valuesFromEnvironmentFor source.val
              sourceCanonical.siteOuter.ids
              (source.val.wiresAt (source.val.wires wire).scope)
              sourceExtended
          have sourceReconstructed :
              ConcreteElaboration.extendEnvironment source.val
                  sourceCanonical.siteOuter (source.val.wires wire).scope
                  sourceValues
                  (Env.comp targetOuterEnv outerProjection) =
                sourceExtended := by
            apply
              ConcreteElaboration.extendEnvironmentFor_from source.val
                sourceCanonical.siteOuter.ids
                (source.val.wiresAt (source.val.wires wire).scope)
            intro signature value
            calc
              sourceExtended _
                  (ConcreteElaboration.appendRightVar source.val
                    (source.val.wiresAt (source.val.wires wire).scope)
                    value) =
                sourceFrameEnv _ (scopeEmbedOuter sourceCanonical value) :=
                  castVisibleEnv_appendRight sourceCanonical sourceFrameEnv
                    value
              _ = reassigned _
                    (visibleProjection
                      (scopeEmbedOuter sourceCanonical value)) := rfl
              _ = reassigned _
                    (scopeEmbedOuter targetCanonical
                      (outerProjection value)) := by
                  rw [visibleExtendsOuter value]
              _ = targetFrameEnv _
                    (scopeEmbedOuter targetCanonical
                      (outerProjection value)) :=
                  targetOuterAgreement (outerProjection value)
              _ = targetExtended _
                    (ConcreteElaboration.appendRightVar
                      ledger.erasureTrace.target.val
                      (ledger.erasureTrace.target.val.wiresAt
                        (ledger.erasureTrace.target.val.wires
                          ledger.erasureTrace.targetWire).scope)
                      (outerProjection value)) := by
                  rw [← castVisibleEnv_appendRight targetCanonical
                    targetFrameEnv (outerProjection value)]
                  exact congrFun
                    (congrFun
                      (castEnv_roundtrip targetVisibleSigs targetExtended)
                      signature)
                    (ConcreteElaboration.appendRightVar
                      ledger.erasureTrace.target.val
                      (ledger.erasureTrace.target.val.wiresAt
                        (ledger.erasureTrace.target.val.wires
                          ledger.erasureTrace.targetWire).scope)
                      (outerProjection value))
              _ = targetOuterEnv _ (outerProjection value) :=
                  ConcreteElaboration.extendEnvironment_appendRightVar
                    ledger.erasureTrace.target.val
                    targetCanonical.siteOuter
                    (ledger.erasureTrace.target.val.wires
                      ledger.erasureTrace.targetWire).scope
                    targetValues targetOuterEnv (outerProjection value)
          have sourceExtendedHolds :
              denoteRegion model.toPreModel definitionEnv sourceExtended
                (sourceVisibleSigs ▸ sourceScope.frame.siteBody) := by
            apply
              (denoteRegion_transport sourceVisibleSigs model.toPreModel
                definitionEnv sourceFrameEnv
                sourceScope.frame.siteBody).mp
            exact sourceBodyHolds
          apply
            (ConcreteElaboration.denote_finishRegion definitions
              source.val sourceCanonical.siteOuter
              (source.val.wires wire).scope model.toPreModel definitionEnv
              (Env.comp targetOuterEnv outerProjection)
              (sourceVisibleSigs ▸ sourceScope.frame.siteBody)).mpr
          exact
            ⟨sourceValues,
              sourceReconstructed.symm ▸ sourceExtendedHolds⟩)
    have sourceRoot :
        sourceScope.checked =
          sourceCanonical.above.fill sourceFinished := by
      exact sourceScope.frame_fills_checked.symm.trans
        (aboveScope_fill_finishRegion sourceCanonical)
    have targetRoot :
        targetScope.checked =
          targetCanonical.above.fill targetFinished := by
      exact targetScope.frame_fills_checked.symm.trans
        (aboveScope_fill_finishRegion targetCanonical)
    have depthExact :
        ledger.sourceScope.frame.context.cutDepth =
          sourceCanonical.above.cutDepth := by
      rw [← aboveScope_cutDepth_eq sourceCanonical]
      cases SiteCompilation.unique ledger.sourceScope sourceScope
      rfl
    have landing :=
      iso_denotation ledger.erasureIso model.toPreModel definitionEnv
    constructor
    · intro even resultHolds
      have targetChecked :
          denoteChecked model.toPreModel definitionEnv
            ledger.erasureTrace.target :=
        landing.mpr resultHolds
      rw [elaborate_denotes_checked] at targetChecked
      change
        denoteRegion model.toPreModel definitionEnv Env.empty
          targetScope.checked at targetChecked
      rw [targetRoot] at targetChecked
      have sourceFilled :=
        parity.1 (by
          rw [← depthExact]
          exact even) targetChecked
      rw [← sourceRoot] at sourceFilled
      rw [elaborate_denotes_checked]
      change
        denoteRegion model.toPreModel definitionEnv Env.empty
          sourceScope.checked
      exact sourceFilled
    · intro odd sourceHolds
      rw [elaborate_denotes_checked] at sourceHolds
      change
        denoteRegion model.toPreModel definitionEnv Env.empty
          sourceScope.checked at sourceHolds
      rw [sourceRoot] at sourceHolds
      have targetFilled :=
        parity.2 (by
          rw [← depthExact]
          exact odd) sourceHolds
      rw [← targetRoot] at targetFilled
      have traceHolds :
          denoteChecked model.toPreModel definitionEnv
            ledger.erasureTrace.target := by
        rw [elaborate_denotes_checked]
        change
          denoteRegion model.toPreModel definitionEnv Env.empty
            targetScope.checked
        exact targetFilled
      exact landing.mp traceHolds

end ConcreteWirePrimitive.EndsDeleteResult.SiteLedger

end VisualProof
