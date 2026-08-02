import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinFrameReflection

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

open Internal
open Internal.RelationJoinStep

/--
One projection authority for a compiled scope. The visible projection extends
the zipper's site-outer projection through each endpoint's actual ordered local
binder block; those blocks need not be equal.
-/
structure RelationJoinSemanticTrace.ScopeProjection
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {target : CheckedDiagram definitions}
    {targetSite : target.val.RegionId}
    {targetScope : SiteCompilation target targetSite}
    (sourceCanonical :
      SiteCompilation.AboveScopeDecomposition sourceScope)
    (targetCanonical :
      SiteCompilation.AboveScopeDecomposition targetScope)
    (outerProjection :
      WireRenaming sourceCanonical.siteOuter.sigs
        targetCanonical.siteOuter.sigs) where
  visibleProjection :
    WireRenaming sourceScope.frame.visible.sigs
      targetScope.frame.visible.sigs
  visibleExtendsOuter :
    ∀ {sig : Sig} (value : Var sourceCanonical.siteOuter.sigs sig),
      visibleProjection (aboveScopeEmbedOuter sourceCanonical value) =
        aboveScopeEmbedOuter targetCanonical (outerProjection value)

theorem RelationJoinStep.aboveDyingScopeReceipt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope))
    (checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)) :
    Nonempty
      (RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) := by
  let candidateWellFormed :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        step.prior step.priorApplication).WellFormed definitions := by
    rw [← step.base_generated]
    exact step.base.property
  have baseExact :
      step.base =
        singletonErasureBase step.prior step.priorApplication
          candidateWellFormed :=
    Subtype.ext step.base_generated
  let generatedChecked : CheckedDiagram definitions :=
    ⟨step.attachment.diagram, compiled.generated_wellFormed⟩
  have checkedExact : generatedChecked = step.checked :=
    Subtype.ext step.checked_generated.symm
  let rawScope :=
    SingletonRemovalSemantics.targetRegion step.prior
      step.priorApplication
      (step.priorRegionImage (source.val.wires dying).scope)
  have baseScopeExact :
      baseExact.symm ▸ rawScope =
        step.baseRegionImage (source.val.wires dying).scope := by
    apply Fin.ext
    exact
      (transport_checked_region_val baseExact.symm rawScope).trans
        (congrArg Fin.val
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetRegion_eq_baseRegionImage
            step (source.val.wires dying).scope))
  have checkedSiteExact :
      checkedExact ▸
          step.attachment.hostRegion (baseExact.symm ▸ rawScope) =
        step.checkedRegionImage (source.val.wires dying).scope := by
    apply Fin.ext
    calc
      _ = (step.attachment.hostRegion
            (baseExact.symm ▸ rawScope)).val :=
        transport_checked_region_val checkedExact _
      _ = (step.attachment.hostRegion
            (step.baseRegionImage (source.val.wires dying).scope)).val :=
        congrArg Fin.val
          (congrArg step.attachment.hostRegion baseScopeExact)
      _ = _ :=
        (congrArg Fin.val
          (step.checkedRegionImageExact
            (source.val.wires dying).scope)).symm
  apply RelationJoinStep.aboveDyingScopeReceiptOfExplicitBase.{u} step
    contentCompiled candidateWellFormed step.base baseExact step.site
    ?_ step.attachment compiled
    checkedExact checkedSiteExact priorScope checkedScope
  · apply Fin.ext
    have removedRegionExact :
        (step.prior.val.nodes step.priorApplication).region =
          step.priorRegionImage step.sourceRegion := by
      rw [step.priorNodeExact]
      rfl
    calc
      step.site.val =
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage step.sourceRegion)).val :=
        (congrArg Fin.val
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetSite_eq_site
            step)).symm
      _ =
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.prior.val.nodes step.priorApplication).region).val := by
        rw [removedRegionExact]
      _ = _ :=
        (transport_checked_region_val baseExact.symm
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.prior.val.nodes step.priorApplication).region)).symm

theorem Internal.RelationJoinStep.preBinderDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterScopes :
      ∀ position : Fin step.sourceParameters.length,
        source.val.Encloses
          (source.val.wires
            (step.sourceParameters.get position)).scope
          (source.val.wires dying).scope) :
    ∃ (priorScope :
        SiteCompilation step.prior
          (step.priorRegionImage (source.val.wires dying).scope))
      (checkedScope :
        SiteCompilation step.checked
          (step.checkedRegionImage (source.val.wires dying).scope))
      (aboveReceipt :
        RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
          checkedScope)
      (scopeProjection :
        RelationJoinSemanticTrace.ScopeProjection
          aboveReceipt.priorCanonical aboveReceipt.checkedCanonical
          aboveReceipt.siteProjection)
      (priorHead :
        Var priorScope.frame.visible.sigs (.rel step.relationArgs))
      (checkedHead :
        Var checkedScope.frame.visible.sigs (.rel step.relationArgs))
      (priorParameters :
        Vars priorScope.frame.visible.sigs parameterSigs)
      (checkedParameters :
        Vars checkedScope.frame.visible.sigs parameterSigs),
      ConcreteElaboration.variableOrigins step.prior.val
          priorScope.frame.visible (.cons priorHead .nil) =
        [step.priorWireImage dying] ∧
      ConcreteElaboration.variableOrigins step.checked.val
          checkedScope.frame.visible (.cons checkedHead .nil) =
        [step.checkedWireImage dying] ∧
      ConcreteElaboration.variableOrigins step.prior.val
          priorScope.frame.visible priorParameters =
        step.sourceParameters.map step.priorWireImage ∧
      ConcreteElaboration.variableOrigins step.checked.val
          checkedScope.frame.visible checkedParameters =
        step.sourceParameters.map step.checkedWireImage ∧
      scopeProjection.visibleProjection
          (sig := .rel step.relationArgs) priorHead =
        checkedHead ∧
      Vars.rename scopeProjection.visibleProjection priorParameters =
        checkedParameters ∧
      ∀ checkedEnv :
          Env model.toPreModel checkedScope.frame.visible.sigs,
        checkedEnv (.rel step.relationArgs) checkedHead =
            WireQuantifierSemantics.contentRelation model definitionEnv
              contentCompiled boundaryExact
                (Vars.denote checkedEnv checkedParameters) →
          denoteRegion model.toPreModel definitionEnv checkedEnv
              checkedScope.frame.siteBody →
            denoteRegion model.toPreModel definitionEnv
              (Env.comp checkedEnv scopeProjection.visibleProjection)
              priorScope.frame.siteBody := by
  obtain ⟨priorScope, priorOuter, fuel, priorFrame, priorVisible,
      priorInner, priorScopeVisible, priorAbove, priorGenerated,
      priorFrameBody, priorDecomposition, priorScopeBody, pairedErasure⟩ :=
    RelationJoinStep.dyingScopeErasure step
  obtain ⟨head, arguments, applicationCompiled, headOrigin,
      argumentOrigins⟩ :=
    Internal.RelationJoinStep.relativeCompiledApplication step priorFrame priorVisible
  have priorHeadMember :
      step.priorWireImage dying ∈ priorScope.frame.visible.ids := by
    apply priorScope.visible_of_encloses
    rw [step.priorWireScopeExact]
    exact step.prior.val.encloses_refl _
  have priorHeadSignature :
      (step.prior.val.wires (step.priorWireImage dying)).sig =
        .rel step.relationArgs := by
    rw [← headOrigin]
    exact
      ConcreteElaboration.WireContext.origin_signature step.prior.val
        priorFrame.visible.ids head
  let priorHead :
      Var priorScope.frame.visible.sigs (.rel step.relationArgs) :=
    InsertionCompilation.NaturalityInternal.castVar priorHeadSignature
      (variableOfMember step.prior.val priorScope.frame.visible.ids
        (step.priorWireImage dying) priorHeadMember)
  have priorHeadOrigin :
      ConcreteElaboration.variableOrigins step.prior.val
          priorScope.frame.visible (.cons priorHead .nil) =
        [step.priorWireImage dying] := by
    change
      [ConcreteElaboration.WireContext.origin step.prior.val
        priorScope.frame.visible.ids priorHead] =
        [step.priorWireImage dying]
    congr 1
    unfold priorHead
    exact
      (InsertionCompilation.NaturalityInternal.origin_castVar
        step.prior.val priorScope.frame.visible.ids priorHeadSignature
        (variableOfMember step.prior.val priorScope.frame.visible.ids
          (step.priorWireImage dying) priorHeadMember)).trans
        (variableOfMember_origin step.prior.val
          priorScope.frame.visible.ids (step.priorWireImage dying)
          priorHeadMember)
  have priorParameterSignatures :=
    Internal.RelationJoinStep.priorParameterSignatures step boundaryExact
      priorFrame.visible arguments argumentOrigins
  let priorParameterWires :=
    step.sourceParameters.map step.priorWireImage
  have priorParameterMembers :
      ∀ wire, wire ∈ priorParameterWires →
        wire ∈ priorScope.frame.visible.ids := by
    intro wire member
    obtain ⟨sourceWire, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨position, rfl⟩ := List.get_of_mem sourceMember
    apply priorScope.visible_of_encloses
    rw [← step.priorWireScopeExact dying]
    exact
      Internal.RelationJoinStep.priorParameterScopes step parameterScopes position
  let priorParameterNative :=
    variablesOfMembers step.prior.val priorScope.frame.visible
      priorParameterWires priorParameterMembers
  have priorParameterNativeSignatures :
      priorParameterWires.map
          (fun wire => (step.prior.val.wires wire).sig) =
        parameterSigs := by
    unfold priorParameterWires
    rw [List.map_map]
    exact priorParameterSignatures
  let priorParameters :
      Vars priorScope.frame.visible.sigs parameterSigs :=
    priorParameterNativeSignatures ▸ priorParameterNative
  have priorParameterOrigins :
      ConcreteElaboration.variableOrigins step.prior.val
          priorScope.frame.visible priorParameters =
        step.sourceParameters.map step.priorWireImage := by
    unfold priorParameters
    rw [variableOrigins_cast]
    exact
      variablesOfMembers_origins step.prior.val priorScope.frame.visible
        priorParameterWires priorParameterMembers
  obtain ⟨rawFrame, erasureProvenance, siteOuter, generatedFrame,
      pairedInsertion⟩ :=
    RelationJoinStep.pairedInsertionAtDying step contentCompiled compiled
      priorVisible pairedErasure
  have sourceEncloses :
      source.val.Encloses
        (source.val.wires dying).scope step.sourceRegion :=
    (step.priorRegionImageEncloses
      (source.val.wires dying).scope step.sourceRegion).mp
        step.prior_dying_scope_encloses_site
  have baseEncloses :
      step.base.val.Encloses
        (step.baseRegionImage (source.val.wires dying).scope) step.site := by
    rw [step.siteExact]
    exact
      (step.baseRegionImageEncloses
        (source.val.wires dying).scope step.sourceRegion).2 sourceEncloses
  obtain ⟨baseScope, baseOuter, baseFuel, baseFrame,
      baseRelativeVisible, baseInner, baseScopeVisible, _baseRootInner,
      baseAbove, baseGenerated, _baseRelativeBody,
      baseDecomposition, baseScopeBody, _baseRootBody,
      _baseReplacementBody, _baseCutDepth⟩ :=
    compiled.site.factorAt_relative_origin
      (step.baseRegionImage (source.val.wires dying).scope)
      (by simpa [step.siteExact] using baseEncloses)
  obtain ⟨canonicalSiteOuter, _canonicalSiteFuel, _canonicalSiteNodes,
      _canonicalSiteChildren, canonicalSiteVisible,
      _canonicalSiteNodesCompiled, _canonicalSiteChildrenCompiled,
      _canonicalSiteBody⟩ :=
    compiled.site.site_origin
  obtain ⟨canonicalGeneratedFrame, canonicalPairedInsertion⟩ :=
    InsertionCompilation.pairedGeneratedFrame compiled
      (step.baseRegionImage (source.val.wires dying).scope) baseFuel
      baseOuter canonicalSiteOuter baseFrame baseAbove canonicalSiteVisible
      (baseRelativeVisible.trans canonicalSiteVisible) baseGenerated
  obtain ⟨canonicalInner, generatedScope, generatedScopeVisible,
      canonicalSourceInner, generatedScopeBody⟩ :=
    canonicalPairedInsertion.canonicalTargetScope baseScope baseScopeVisible
      baseInner baseDecomposition baseScopeBody
  let baseReceipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel priorOuter rawFrame erasureProvenance.targetGenerated
  have baseFrameVisibleExact :
      baseFrame.visible = baseReceipt.frame.visible :=
    baseRelativeVisible.trans
      (pairedInsertion.siteVisible.trans
        pairedInsertion.sourceVisible.symm)
  have baseOuterExact : baseOuter = baseReceipt.outer :=
    InsertionCompilation.compileRegionFrame?_outer_of_visible definitions
      step.base.val step.site baseFuel fuel
      (step.baseRegionImage (source.val.wires dying).scope)
      baseOuter baseReceipt.outer baseFrame baseReceipt.frame
      baseGenerated pairedInsertion.sourceGenerated baseFrameVisibleExact
  subst baseOuter
  let commonSourceFuel := baseFuel + fuel
  have baseFrameAtCommon :
      compileRegionFrame? definitions step.base.val step.site
          commonSourceFuel
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer =
        some baseFrame :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions step.base.val step.site baseFuel commonSourceFuel
      (by unfold commonSourceFuel; omega)
      (step.baseRegionImage (source.val.wires dying).scope)
      baseReceipt.outer baseGenerated
  have receiptFrameAtCommon :
      compileRegionFrame? definitions step.base.val step.site
          commonSourceFuel
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer =
        some baseReceipt.frame :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions step.base.val step.site fuel commonSourceFuel
      (by unfold commonSourceFuel; omega)
      (step.baseRegionImage (source.val.wires dying).scope)
      baseReceipt.outer pairedInsertion.sourceGenerated
  have baseFrameExact : baseFrame = baseReceipt.frame :=
    Option.some.inj
      (baseFrameAtCommon.symm.trans receiptFrameAtCommon)
  subst baseFrame
  have canonicalSiteOuterExact : canonicalSiteOuter = siteOuter := by
    apply InsertionCompilation.wireContext_extend_injective
      step.base.val step.site
    exact canonicalSiteVisible.symm.trans pairedInsertion.siteVisible
  subst canonicalSiteOuter
  let commonTargetFuel :=
    (baseFuel + content.val.diagram.regionCount) +
      (fuel + content.val.diagram.regionCount)
  have canonicalTargetAtCommon :
      compileRegionFrame? definitions step.attachment.diagram
          (step.attachment.hostRegion step.site) commonTargetFuel
          (step.attachment.hostRegion
            (step.baseRegionImage (source.val.wires dying).scope))
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment baseReceipt.outer) =
        some canonicalGeneratedFrame :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions step.attachment.diagram
      (step.attachment.hostRegion step.site)
      (baseFuel + content.val.diagram.regionCount) commonTargetFuel
      (by unfold commonTargetFuel; omega)
      (step.attachment.hostRegion
        (step.baseRegionImage (source.val.wires dying).scope))
      (InsertionCompilation.NaturalityInternal.hostContext
        step.attachment baseReceipt.outer)
      canonicalPairedInsertion.provenance.targetGenerated
  have generatedTargetAtCommon :
      compileRegionFrame? definitions step.attachment.diagram
          (step.attachment.hostRegion step.site) commonTargetFuel
          (step.attachment.hostRegion
            (step.baseRegionImage (source.val.wires dying).scope))
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment baseReceipt.outer) =
        some generatedFrame :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions step.attachment.diagram
      (step.attachment.hostRegion step.site)
      (fuel + content.val.diagram.regionCount) commonTargetFuel
      (by unfold commonTargetFuel; omega)
      (step.attachment.hostRegion
        (step.baseRegionImage (source.val.wires dying).scope))
      (InsertionCompilation.NaturalityInternal.hostContext
        step.attachment baseReceipt.outer)
      pairedInsertion.provenance.targetGenerated
  have canonicalGeneratedExact :
      canonicalGeneratedFrame = generatedFrame :=
    Option.some.inj
      (canonicalTargetAtCommon.symm.trans generatedTargetAtCommon)
  subst canonicalGeneratedFrame
  let generatedChecked :
      CheckedDiagram definitions :=
    ⟨step.attachment.diagram, compiled.generated_wellFormed⟩
  have checkedExact : step.checked = generatedChecked :=
    Subtype.ext step.checked_generated
  let rawCheckedScope :=
    transportSiteCompilation checkedExact.symm generatedScope
  have checkedSiteExact :
      checkedExact.symm ▸
          step.attachment.hostRegion
            (step.baseRegionImage (source.val.wires dying).scope) =
        step.checkedRegionImage (source.val.wires dying).scope := by
    rw [step.checkedRegionImageExact]
    apply Fin.ext
    exact
      transport_checked_region_val checkedExact.symm
        (step.attachment.hostRegion
          (step.baseRegionImage (source.val.wires dying).scope))
  let checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope) :=
    checkedSiteExact ▸ rawCheckedScope
  have baseReceiptOuter :
      baseReceipt.outer =
        step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication priorOuter := by
    unfold baseReceipt checkedBaseFrameReceipt
    exact
      GeneratedFrameReceipt.transport_outer step.base_generated.symm
        { site :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
          region :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)
          outer :=
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorOuter
          frame := rawFrame
          generated := erasureProvenance.targetGenerated }
  have baseReceiptRegion :
      baseReceipt.region =
        step.baseRegionImage (source.val.wires dying).scope :=
    (checkedBaseFrameReceipt_region step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel priorOuter rawFrame erasureProvenance.targetGenerated).trans
        (SingletonRemovalSemantics.RelationJoinStep.rawTargetRegion_eq_baseRegionImage
          step (source.val.wires dying).scope)
  have baseReceiptRegionTransport :
      baseReceipt.region =
        step.base_generated.symm ▸
          SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope) := by
    apply Fin.ext
    unfold baseReceipt checkedBaseFrameReceipt
    exact
      (GeneratedFrameReceipt.transport_region_val step.base_generated.symm
        { site :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
          region :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)
          outer :=
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorOuter
          frame := rawFrame
          generated := erasureProvenance.targetGenerated }).trans
        (transport_region_val step.base_generated.symm
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope))).symm
  have baseExtendedContextExact :
      step.base_generated.symm ▸
          (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorOuter).extend
            (SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)) =
        baseReceipt.outer.extend
          (step.baseRegionImage (source.val.wires dying).scope) := by
    calc
      _ =
          (step.base_generated.symm ▸
              SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication priorOuter).extend
            (step.base_generated.symm ▸
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage
                  (source.val.wires dying).scope)) :=
        (transport_extended_context step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication priorOuter)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope))).symm
      _ = _ := by
        rw [← baseReceiptOuter, ← baseReceiptRegionTransport,
          baseReceiptRegion]
  have checkedGeneratedVisibleExact :
      checkedExact.symm ▸ generatedScope.frame.visible =
        checkedScope.frame.visible :=
    by
      change
        checkedExact.symm ▸ generatedScope.frame.visible =
          (checkedSiteExact ▸ rawCheckedScope).frame.visible
      exact
        (transportSiteCompilation_visible checkedExact.symm
          generatedScope).symm.trans
            (castSiteCompilation_visible checkedSiteExact rawCheckedScope).symm
  let projection :
      WireRenaming priorScope.frame.visible.sigs
        checkedScope.frame.visible.sigs :=
    fun {_} value =>
      transportCheckedVariable checkedExact.symm
        generatedScope.frame.visible
        checkedScope.frame.visible checkedGeneratedVisibleExact
        (transportVariable rfl
          ((InsertionCompilation.NaturalityInternal.hostContext
              step.attachment baseReceipt.outer).extend
            (step.attachment.hostRegion
              (step.baseRegionImage (source.val.wires dying).scope)))
          generatedScope.frame.visible generatedScopeVisible.symm
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer
            (transportVariable step.base_generated.symm
              ((SingletonRemovalSemantics.targetContext step.prior
                  step.priorApplication priorOuter).extend
                (SingletonRemovalSemantics.targetRegion step.prior
                  step.priorApplication
                  (step.priorRegionImage
                    (source.val.wires dying).scope)))
              (baseReceipt.outer.extend
                (step.baseRegionImage (source.val.wires dying).scope))
              baseExtendedContextExact
              (SingletonRemovalSemantics.extendedContextRenaming step.prior
                step.priorApplication priorOuter
                (step.priorRegionImage
                  (source.val.wires dying).scope)
                (transportVariable rfl priorScope.frame.visible
                  (priorOuter.extend
                    (step.priorRegionImage
                      (source.val.wires dying).scope))
                  priorScopeVisible value)))))
  have enclosingProjectionOrigin :
      ∀ {sig : Sig}
        (value :
          Var
            (baseReceipt.outer.extend
              (step.baseRegionImage
                (source.val.wires dying).scope)).sigs sig),
        ConcreteElaboration.WireContext.origin step.attachment.diagram
            ((InsertionCompilation.NaturalityInternal.hostContext
                step.attachment baseReceipt.outer).extend
              (step.attachment.hostRegion
                (step.baseRegionImage
                  (source.val.wires dying).scope))).ids
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer value) =
          step.attachment.hostWire
            (ConcreteElaboration.WireContext.origin step.base.val
              (baseReceipt.outer.extend
                (step.baseRegionImage
                  (source.val.wires dying).scope)).ids value) := by
    intro sig value
    exact
      InsertionCompilation.enclosingRenaming_contextAction compiled
        (step.baseRegionImage (source.val.wires dying).scope)
        baseReceipt.outer value
  have projectionOriginGeneral :
      ∀ {sig : Sig}
        (value : Var priorScope.frame.visible.sigs sig),
        ConcreteElaboration.WireContext.origin step.checked.val
            checkedScope.frame.visible.ids (projection value) =
          relationJoinPriorToCheckedWire step
            (ConcreteElaboration.WireContext.origin step.prior.val
              priorScope.frame.visible.ids value) := by
    intro sig value
    unfold projection
    rw [transportCheckedVariable_origin,
      transportVariable_origin, enclosingProjectionOrigin,
      transportVariable_origin, extendedContextRenaming_origin,
      transportVariable_origin]
    unfold relationJoinPriorToCheckedWire transportWire
    apply Fin.ext
    rfl
  have projectionOrigin :
      ∀ (sourceWire : source.val.WireId)
        {sig : Sig}
        (value : Var priorScope.frame.visible.sigs sig),
        ConcreteElaboration.WireContext.origin step.prior.val
            priorScope.frame.visible.ids value =
            step.priorWireImage sourceWire →
          ConcreteElaboration.WireContext.origin step.checked.val
              checkedScope.frame.visible.ids (projection value) =
            step.checkedWireImage sourceWire := by
    intro sourceWire sig value sourceOrigin
    rw [projectionOriginGeneral, sourceOrigin]
    rw [step.checkedWireImageExact, step.baseWireImageExact]
    apply Fin.ext
    rfl
  let checkedHead :
      Var checkedScope.frame.visible.sigs (.rel step.relationArgs) :=
    projection priorHead
  let checkedParameters :
      Vars checkedScope.frame.visible.sigs parameterSigs :=
    Vars.rename projection priorParameters
  have checkedHeadOrigin :
      ConcreteElaboration.variableOrigins step.checked.val
          checkedScope.frame.visible (.cons checkedHead .nil) =
        [step.checkedWireImage dying] := by
    change
      [ConcreteElaboration.WireContext.origin step.checked.val
        checkedScope.frame.visible.ids checkedHead] =
        [step.checkedWireImage dying]
    congr 1
    apply projectionOrigin dying priorHead
    exact (List.cons.inj priorHeadOrigin).1
  have checkedParameterOrigins :
      ConcreteElaboration.variableOrigins step.checked.val
          checkedScope.frame.visible checkedParameters =
        step.sourceParameters.map step.checkedWireImage := by
    unfold checkedParameters
    exact
      variableOrigins_rename_mapped step.prior.val step.checked.val
        priorScope.frame.visible checkedScope.frame.visible projection
        step.priorWireImage step.checkedWireImage
        (fun sourceWire {_} value sourceOrigin =>
          projectionOrigin sourceWire value sourceOrigin)
        priorParameters step.sourceParameters priorParameterOrigins
  obtain ⟨aboveReceipt⟩ :=
    RelationJoinStep.aboveDyingScopeReceipt step contentCompiled compiled
      priorScope checkedScope
  let scopeProjection :
      RelationJoinSemanticTrace.ScopeProjection
        aboveReceipt.priorCanonical aboveReceipt.checkedCanonical
        aboveReceipt.siteProjection :=
    {
      visibleProjection := projection
      visibleExtendsOuter := by
        intro sig value
        apply
          InsertionCompilation.NaturalityInternal.origin_injective
            step.checked.val checkedScope.frame.visible.ids
        · exact siteCompilation_visible_nodup checkedScope
        · rw [projectionOriginGeneral]
          rw [aboveScopeEmbedOuter_origin,
              aboveScopeEmbedOuter_origin]
          exact (aboveReceipt.siteProjectionOrigin value).symm
    }
  refine
    ⟨priorScope, checkedScope, aboveReceipt, scopeProjection,
      priorHead, checkedHead,
      priorParameters, checkedParameters, priorHeadOrigin,
      checkedHeadOrigin, priorParameterOrigins, checkedParameterOrigins,
      rfl, rfl, ?_⟩
  intro checkedEnv checkedHeadValue checkedHolds
  let parameterValues := Vars.denote checkedEnv checkedParameters
  have checkedParameterValues :
      Vars.denote checkedEnv checkedParameters = parameterValues := rfl
  by_cases coScoped :
      (source.val.wires dying).scope = step.sourceRegion
  · have baseAtSite :
        step.baseRegionImage (source.val.wires dying).scope = step.site := by
      rw [coScoped, step.siteExact]
    obtain ⟨siteInner, siteSourceVisible, siteSourceFill, siteLaw⟩ :=
      pairedInsertion.siteInsertionDenotationRestrict baseAtSite
        model.toPreModel definitionEnv
    let siteSourceSigs :=
      congrArg ConcreteElaboration.WireContext.sigs siteSourceVisible
    obtain ⟨generatedCheckedSigs, generatedCheckedBody⟩ :=
      transportedSiteCompilation_body checkedExact.symm generatedScope
        checkedSiteExact
    have generatedScopeHolds :
        denoteRegion model.toPreModel definitionEnv
          (Env.comp checkedEnv
            (InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs))
          generatedScope.frame.siteBody := by
      apply
        (InsertionCompilation.NaturalityInternal.denoteRegion_castContext
          model.toPreModel definitionEnv generatedCheckedSigs checkedEnv
          generatedScope.frame.siteBody).mp
      rw [generatedCheckedBody]
      exact checkedHolds
    let generatedVisibleExact :=
      congrArg ConcreteElaboration.WireContext.sigs generatedScopeVisible
    let generatedFixed :
        Env model.toPreModel
          ((InsertionCompilation.NaturalityInternal.hostContext
              step.attachment baseReceipt.outer).extend
            (step.attachment.hostRegion
              (step.baseRegionImage
                (source.val.wires dying).scope))).sigs :=
      generatedVisibleExact ▸
        Env.comp checkedEnv
          (InsertionCompilation.NaturalityInternal.equalityRenaming
            generatedCheckedSigs)
    have canonicalTargetHolds :
        denoteRegion model.toPreModel definitionEnv generatedFixed
          (canonicalInner.targetInner.fill generatedFrame.siteBody) := by
      have transported :=
        (denoteRegion_transport generatedVisibleExact model.toPreModel
          definitionEnv
          (Env.comp checkedEnv
            (InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs))
          generatedScope.frame.siteBody).mp generatedScopeHolds
      unfold generatedFixed
      rw [generatedScopeBody] at transported
      exact transported
    have siteSourceInner :
        siteInner.sourceInner = baseInner := by
      apply
        bindContextFor_injective step.base.val baseReceipt.outer.ids
          (step.base.val.wiresAt
            (step.baseRegionImage (source.val.wires dying).scope))
      exact siteInner.sourceDecomposition.symm.trans baseDecomposition
    have canonicalSiteTargetInner :
        canonicalInner.targetInner = siteInner.targetInner := by
      apply
        bindContextFor_injective step.attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment baseReceipt.outer).ids
          (step.attachment.diagram.wiresAt
            (step.attachment.hostRegion
              (step.baseRegionImage (source.val.wires dying).scope)))
      exact
        canonicalInner.targetDecomposition.symm.trans
          siteInner.targetDecomposition
    have canonicalSiteSourceInner :
        canonicalInner.sourceInner = siteInner.sourceInner :=
      canonicalSourceInner.trans siteSourceInner.symm
    have insertedHolds :
        denoteRegion model.toPreModel definitionEnv
          (Env.comp generatedFixed
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer))
          (siteInner.sourceInner.fill siteInner.replacement) := by
      apply siteLaw generatedFixed
      rw [← canonicalSiteTargetInner]
      exact canonicalTargetHolds
    have pairedFixed :
        SingletonRemovalSemantics.PairedGeneratedFrame step.prior
          step.priorApplication
          (step.prior.val.nodes step.priorApplication).region
          (step.prior.val.nodes step.priorApplication).region fuel
          priorOuter priorFrame := by
      simpa [step.priorNodeExact, coScoped] using pairedErasure
    obtain ⟨fixedTarget, fixedGenerated, fixedVisible, fixedLaw⟩ :=
      SingletonRemovalSemantics.PairedGeneratedFrame.fixedScope_replacement_denotation
        step.prior step.priorApplication
        (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
        fuel priorOuter priorFrame pairedFixed (.atom head arguments)
        applicationCompiled model.toPreModel definitionEnv
    have fixedTargetExact : fixedTarget = rawFrame := by
      apply Option.some.inj
      exact fixedGenerated.symm.trans (by
        simpa [step.priorNodeExact, coScoped] using
          erasureProvenance.targetGenerated)
    subst fixedTarget
    let baseVisibleExact :=
      RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
        compiled rawFrame erasureProvenance pairedInsertion
    let canonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication priorFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let replacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          erasureProvenance.targetVisible.symm ▸ canonicalReplacement
    have transportFrameSiteBody :
        ∀ {left right : ConcreteDiagram definitions.length}
          (same : left = right)
          (receipt : GeneratedFrameReceipt definitions left fuel),
          HEq (same ▸ receipt).frame.siteBody receipt.frame.siteBody := by
      intro left right same receipt
      cases same
      exact HEq.rfl
    have sourceBodyExact :
        HEq baseReceipt.frame.siteBody rawFrame.siteBody := by
      unfold baseReceipt checkedBaseFrameReceipt
      exact
        transportFrameSiteBody step.base_generated.symm
          { site :=
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage step.sourceRegion)
            region :=
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage (source.val.wires dying).scope)
            outer :=
              SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication priorOuter
            frame := rawFrame
            generated := erasureProvenance.targetGenerated }
    have replacementExact :
        HEq replacement
          (intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment) := by
      unfold replacement canonicalReplacement untransportRegion
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply eqRec_heq
    have insertedExact :
        HEq
          (congrArg ConcreteElaboration.WireContext.sigs
              (siteInner.siteVisible.trans
                siteInner.sourceVisible.symm) ▸
            intrinsicSplice contentCompiled.openDiagram
              compiled.intrinsicAttachment)
          (intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment) := by
      apply eqRec_heq
    have baseFrameVisibleTransport :
        baseReceipt.frame.visible =
          step.base_generated.symm ▸ rawFrame.visible := by
      unfold baseReceipt checkedBaseFrameReceipt
      exact
        GeneratedFrameReceipt.transport_frame_visible
          step.base_generated.symm
          { site :=
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage step.sourceRegion)
            region :=
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage (source.val.wires dying).scope)
            outer :=
              SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication priorOuter
            frame := rawFrame
            generated := erasureProvenance.targetGenerated }
    have holeSigsExact :
        baseReceipt.frame.visible.sigs = rawFrame.visible.sigs :=
      (congrArg ConcreteElaboration.WireContext.sigs
        baseFrameVisibleTransport).trans
          (transport_context_sigs step.base_generated.symm
            rawFrame.visible)
    let holeRegionTypeExact :=
      congrArg (Region definitions) holeSigsExact
    have sourceBodyCast :
        cast holeRegionTypeExact baseReceipt.frame.siteBody =
          rawFrame.siteBody :=
      eq_of_heq
        ((cast_heq holeRegionTypeExact
          baseReceipt.frame.siteBody).trans sourceBodyExact)
    have insertedCast :
        cast holeRegionTypeExact
            (congrArg ConcreteElaboration.WireContext.sigs
                (siteInner.siteVisible.trans
                  siteInner.sourceVisible.symm) ▸
              intrinsicSplice contentCompiled.openDiagram
                compiled.intrinsicAttachment) =
          replacement :=
      eq_of_heq
        ((cast_heq holeRegionTypeExact
          (congrArg ConcreteElaboration.WireContext.sigs
              (siteInner.siteVisible.trans
                siteInner.sourceVisible.symm) ▸
            intrinsicSplice contentCompiled.openDiagram
              compiled.intrinsicAttachment)).trans
          (insertedExact.trans replacementExact.symm))
    have castConjoin :
        ∀ {left right : List Sig}
          (same : left = right)
          (first second : Region definitions left),
          cast (congrArg (Region definitions) same)
              (first.conjoin second) =
            (cast (congrArg (Region definitions) same) first).conjoin
              (cast (congrArg (Region definitions) same) second) := by
      intro left right same first second
      cases same
      rfl
    have bodyCast :
        cast holeRegionTypeExact siteInner.replacement =
          rawFrame.siteBody.conjoin replacement := by
      unfold InsertionCompilation.PairedInnerFrame.replacement
      rw [castConjoin holeSigsExact, sourceBodyCast, insertedCast]
    have fixedSigsExact :
        (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs =
          rawFrame.visible.sigs :=
      siteSourceSigs.trans holeSigsExact
    have filledCast :
        fixedSigsExact ▸
            siteInner.sourceInner.fill siteInner.replacement =
          rawFrame.siteBody.conjoin replacement := by
      calc
        _ =
            holeSigsExact ▸
              siteSourceSigs ▸
                siteInner.sourceInner.fill siteInner.replacement :=
          cast_region_trans siteSourceSigs holeSigsExact
            (siteInner.sourceInner.fill siteInner.replacement)
        _ = holeSigsExact ▸ siteInner.replacement := by
          rw [siteSourceFill]
        _ = cast holeRegionTypeExact siteInner.replacement :=
          cast_region_eq holeSigsExact siteInner.replacement
        _ = _ := bodyCast
    have rawSameOrder :=
      (denoteRegion_transport fixedSigsExact model.toPreModel definitionEnv
        (Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer))
        (siteInner.sourceInner.fill siteInner.replacement)).mp insertedHolds
    rw [filledCast] at rawSameOrder
    let rawEnv : Env model.toPreModel rawFrame.visible.sigs :=
      fixedSigsExact ▸
        Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer)
    have replacementFirst :
        denoteRegion model.toPreModel definitionEnv rawEnv
          (replacement.conjoin rawFrame.siteBody) := by
      apply
        (by
          rw [Region.denote_conjoin, Region.denote_conjoin]
          exact and_comm :
          denoteRegion model.toPreModel definitionEnv rawEnv
              (rawFrame.siteBody.conjoin replacement) ↔
            denoteRegion model.toPreModel definitionEnv rawEnv
              (replacement.conjoin rawFrame.siteBody)).mp
      exact rawSameOrder
    have priorScopeSiteExact :
        priorScope.frame = step.priorSite.frame := by
      have siteExact :
          step.priorRegionImage (source.val.wires dying).scope =
            step.priorRegionImage step.sourceRegion :=
        congrArg step.priorRegionImage coScoped
      have scopeGenerated :
          compileRegionFrame? definitions step.prior.val
              (step.priorRegionImage step.sourceRegion)
              (step.prior.val.regionCount + 1) step.prior.val.root
              (ConcreteElaboration.WireContext.empty step.prior.val) =
            some priorScope.frame := by
        simpa only [siteExact] using priorScope.frame_generated
      exact Option.some.inj
        (scopeGenerated.symm.trans step.priorSite.frame_generated)
    have priorScopeFrameVisible :
        priorScope.frame.visible = priorFrame.visible :=
      (congrArg RegionFrame.visible priorScopeSiteExact).trans
        priorVisible.symm
    let priorFrameHead :=
      transportVariable rfl priorScope.frame.visible priorFrame.visible
        priorScopeFrameVisible priorHead
    have priorFrameHeadExact : priorFrameHead = head := by
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          step.prior.val priorFrame.visible.ids
      · rw [← priorScopeFrameVisible]
        exact siteCompilation_visible_nodup priorScope
      · unfold priorFrameHead
        rw [transportVariable_origin]
        exact
          (List.cons.inj priorHeadOrigin).1.trans headOrigin.symm
    let priorFrameParameters :=
      transportVariables rfl priorScope.frame.visible priorFrame.visible
        priorScopeFrameVisible priorParameters
    have priorFrameParameterOrigins :
        ConcreteElaboration.variableOrigins step.prior.val
            priorFrame.visible priorFrameParameters =
          step.sourceParameters.map step.priorWireImage := by
      unfold priorFrameParameters
      rw [transportVariables_origins]
      simpa using priorParameterOrigins
    have canonicalParameterExact :
        parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
          baseRenamedVariables step priorFrame.visible
            compiled.site.frame.visible baseVisibleExact
            priorFrameParameters :=
      Internal.RelationJoinStep.parameterVariables_exact step contentCompiled compiled
        boundaryExact priorFrame.visible baseVisibleExact arguments
        argumentOrigins priorFrameParameters priorFrameParameterOrigins
    let baseFixed :
        Env model.toPreModel
          ((baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs) :=
      Env.comp generatedFixed
        (InsertionCompilation.enclosingRenaming compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer)
    have baseCompiledVisible :
        baseReceipt.frame.visible = compiled.site.frame.visible :=
      siteInner.sourceVisible.trans siteInner.siteVisible.symm
    have compiledSigsExact :
        (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs =
          compiled.site.frame.visible.sigs :=
      siteSourceSigs.trans
        (congrArg ConcreteElaboration.WireContext.sigs baseCompiledVisible)
    let compiledEnv : Env model.toPreModel compiled.site.frame.visible.sigs :=
      compiledSigsExact ▸ baseFixed
    let compiledHead :
        Var compiled.site.frame.visible.sigs (.rel step.relationArgs) :=
      Internal.RelationJoinStep.baseRenamedVariable step priorFrame.visible
        compiled.site.frame.visible baseVisibleExact priorFrameHead
    let baseHead :
        Var
          ((baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs)
          (.rel step.relationArgs) :=
      compiledSigsExact.symm ▸ compiledHead
    let generatedHead :
        Var generatedScope.frame.visible.sigs (.rel step.relationArgs) :=
      generatedVisibleExact.symm ▸
        InsertionCompilation.enclosingRenaming compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer baseHead
    let projectedFrameHead :
        Var checkedScope.frame.visible.sigs (.rel step.relationArgs) :=
      InsertionCompilation.NaturalityInternal.equalityRenaming
        generatedCheckedSigs generatedHead
    have compiledHeadOrigin :
        ConcreteElaboration.WireContext.origin step.base.val
            compiled.site.frame.visible.ids compiledHead =
          step.baseWireImage dying := by
      unfold compiledHead Internal.RelationJoinStep.baseRenamedVariable
      rw [transportVariable_origin,
        SingletonRemovalSemantics.contextRenaming_action,
        show
        ConcreteElaboration.WireContext.origin step.prior.val
            priorFrame.visible.ids priorFrameHead =
          step.priorWireImage dying by
            rw [priorFrameHeadExact]
            exact headOrigin,
        SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
          step dying]
    have baseExtendedCompiledVisible :
        baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope) =
          compiled.site.frame.visible :=
      siteSourceVisible.trans baseCompiledVisible
    have baseHeadOrigin :
        ConcreteElaboration.WireContext.origin step.base.val
            (baseReceipt.outer.extend
              (step.baseRegionImage (source.val.wires dying).scope)).ids
            baseHead =
          step.baseWireImage dying := by
      have proofExact :
          compiledSigsExact.symm =
            congrArg ConcreteElaboration.WireContext.sigs
              baseExtendedCompiledVisible.symm :=
        Subsingleton.elim _ _
      unfold baseHead
      rw [proofExact,
        origin_cast_context step.base.val
          baseExtendedCompiledVisible.symm compiledHead]
      exact compiledHeadOrigin
    have generatedHeadOrigin :
        ConcreteElaboration.WireContext.origin step.attachment.diagram
            generatedScope.frame.visible.ids generatedHead =
          step.attachment.hostWire (step.baseWireImage dying) := by
      unfold generatedHead
      rw [origin_cast_context step.attachment.diagram
        generatedScopeVisible.symm,
        enclosingProjectionOrigin, baseHeadOrigin]
    have projectedFrameHeadTransport :
        projectedFrameHead =
          transportCheckedVariable checkedExact.symm
            generatedScope.frame.visible checkedScope.frame.visible
            checkedGeneratedVisibleExact generatedHead := by
      unfold projectedFrameHead
        InsertionCompilation.NaturalityInternal.equalityRenaming
      apply eq_of_heq
      have left :
          HEq (generatedCheckedSigs ▸ generatedHead) generatedHead :=
        cast_variable_heq generatedCheckedSigs generatedHead
      exact left.trans
        (transportCheckedVariable_heq checkedExact.symm
          generatedScope.frame.visible checkedScope.frame.visible
          checkedGeneratedVisibleExact generatedHead).symm
    have projectedFrameHeadOrigin :
        ConcreteElaboration.WireContext.origin step.checked.val
            checkedScope.frame.visible.ids projectedFrameHead =
          step.checkedWireImage dying := by
      rw [projectedFrameHeadTransport,
        transportCheckedVariable_origin, generatedHeadOrigin,
        step.checkedWireImageExact]
    have projectedFrameHeadExact : projectedFrameHead = checkedHead := by
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          step.checked.val checkedScope.frame.visible.ids
      · exact siteCompilation_visible_nodup checkedScope
      · exact projectedFrameHeadOrigin.trans
          (List.cons.inj checkedHeadOrigin).1.symm
    let frameProjection :
        WireRenaming priorFrame.visible.sigs
          checkedScope.frame.visible.sigs :=
      fun {_} value =>
        InsertionCompilation.NaturalityInternal.equalityRenaming
          generatedCheckedSigs
          (generatedVisibleExact.symm ▸
            InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer
              (compiledSigsExact.symm ▸
                Internal.RelationJoinStep.baseRenamedVariable step
                  priorFrame.visible compiled.site.frame.visible
                  baseVisibleExact value))
    have frameProjectionOrigin :
        ∀ (sourceWire : source.val.WireId) {sig : Sig}
          (value : Var priorFrame.visible.sigs sig),
          ConcreteElaboration.WireContext.origin step.prior.val
              priorFrame.visible.ids value =
              step.priorWireImage sourceWire →
            ConcreteElaboration.WireContext.origin step.checked.val
                checkedScope.frame.visible.ids (frameProjection value) =
              step.checkedWireImage sourceWire := by
      intro sourceWire sig value sourceOrigin
      let compiledValue :=
        Internal.RelationJoinStep.baseRenamedVariable step priorFrame.visible
          compiled.site.frame.visible baseVisibleExact value
      let baseValue :=
        compiledSigsExact.symm ▸ compiledValue
      let generatedValue :=
        generatedVisibleExact.symm ▸
          InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseValue
      have compiledOrigin :
          ConcreteElaboration.WireContext.origin step.base.val
              compiled.site.frame.visible.ids compiledValue =
            step.baseWireImage sourceWire := by
        unfold compiledValue Internal.RelationJoinStep.baseRenamedVariable
        rw [transportVariable_origin,
          SingletonRemovalSemantics.contextRenaming_action, sourceOrigin,
          SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage]
      have baseOrigin :
          ConcreteElaboration.WireContext.origin step.base.val
              (baseReceipt.outer.extend
                (step.baseRegionImage (source.val.wires dying).scope)).ids
              baseValue =
            step.baseWireImage sourceWire := by
        have proofExact :
            compiledSigsExact.symm =
              congrArg ConcreteElaboration.WireContext.sigs
                baseExtendedCompiledVisible.symm :=
          Subsingleton.elim _ _
        unfold baseValue
        rw [proofExact,
          origin_cast_context step.base.val
            baseExtendedCompiledVisible.symm compiledValue]
        exact compiledOrigin
      have generatedOrigin :
          ConcreteElaboration.WireContext.origin step.attachment.diagram
              generatedScope.frame.visible.ids generatedValue =
            step.attachment.hostWire (step.baseWireImage sourceWire) := by
        unfold generatedValue
        rw [origin_cast_context step.attachment.diagram
          generatedScopeVisible.symm,
          enclosingProjectionOrigin, baseOrigin]
      have projectedTransport :
          frameProjection value =
            transportCheckedVariable checkedExact.symm
              generatedScope.frame.visible checkedScope.frame.visible
              checkedGeneratedVisibleExact generatedValue := by
        unfold frameProjection generatedValue baseValue compiledValue
          InsertionCompilation.NaturalityInternal.equalityRenaming
        apply eq_of_heq
        have left :
            HEq (generatedCheckedSigs ▸
              (generatedVisibleExact.symm ▸
                InsertionCompilation.enclosingRenaming compiled
                  (step.baseRegionImage (source.val.wires dying).scope)
                  baseReceipt.outer
                  (compiledSigsExact.symm ▸
                    Internal.RelationJoinStep.baseRenamedVariable step
                      priorFrame.visible compiled.site.frame.visible
                      baseVisibleExact value)))
              generatedValue := by
          unfold generatedValue baseValue compiledValue
          exact cast_variable_heq generatedCheckedSigs _
        exact left.trans
          (transportCheckedVariable_heq checkedExact.symm
            generatedScope.frame.visible checkedScope.frame.visible
            checkedGeneratedVisibleExact generatedValue).symm
      rw [projectedTransport, transportCheckedVariable_origin,
        generatedOrigin, step.checkedWireImageExact]
    let projectedFrameParameters :
        Vars checkedScope.frame.visible.sigs parameterSigs :=
      Vars.rename frameProjection priorFrameParameters
    have projectedFrameParameterOrigins :
        ConcreteElaboration.variableOrigins step.checked.val
            checkedScope.frame.visible projectedFrameParameters =
          step.sourceParameters.map step.checkedWireImage := by
      unfold projectedFrameParameters
      exact
        variableOrigins_rename_mapped step.prior.val step.checked.val
          priorFrame.visible checkedScope.frame.visible frameProjection
          step.priorWireImage step.checkedWireImage
          (fun sourceWire {_} value sourceOrigin =>
            frameProjectionOrigin sourceWire value sourceOrigin)
          priorFrameParameters step.sourceParameters
          priorFrameParameterOrigins
    have projectedFrameParametersExact :
        projectedFrameParameters = checkedParameters :=
      variables_eq_of_origins step.checked.val checkedScope.frame.visible
        (siteCompilation_visible_nodup checkedScope)
        projectedFrameParameters checkedParameters
        (projectedFrameParameterOrigins.trans checkedParameterOrigins.symm)
    have erasureBaseEnvExact :
        transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorFrame.visible)
            compiled.site.frame.visible baseVisibleExact
            (congrArg ConcreteElaboration.WireContext.sigs
                erasureProvenance.targetVisible ▸ rawEnv) =
          compiledEnv := by
      unfold compiledEnv baseFixed rawEnv transportEnvironment
      apply eq_of_heq
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      exact (eqRec_heq _ _).symm
    have localAt :
        SingletonRemovalSemantics.LocalReplacementAt step.prior
          step.priorApplication priorFrame.visible rawFrame.visible
          erasureProvenance.targetVisible replacement
          (.atom head arguments) model.toPreModel definitionEnv rawEnv := by
      apply
        Internal.RelationJoinStep.erasureLocalReplacementAt step contentCompiled
          compiled model definitionEnv boundaryExact parameterValues
          priorFrame rawFrame erasureProvenance baseVisibleExact head
          arguments argumentOrigins rawEnv
      · dsimp only
        rw [erasureBaseEnvExact]
        rw [← priorFrameHeadExact]
        change compiledEnv _ compiledHead = _
        have compiledHeadCast :
            compiledSigsExact ▸ baseHead = compiledHead := by
          apply eq_of_heq
          have outer :
              HEq (compiledSigsExact ▸ baseHead) baseHead :=
            cast_variable_heq compiledSigsExact baseHead
          have inner : HEq baseHead compiledHead := by
            unfold baseHead
            exact cast_variable_heq compiledSigsExact.symm compiledHead
          exact outer.trans inner
        rw [← compiledHeadCast]
        unfold compiledEnv
        rw [cast_env_apply]
        change generatedFixed _
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseHead) = _
        have generatedHeadCast :
            generatedVisibleExact ▸ generatedHead =
              InsertionCompilation.enclosingRenaming compiled
                (step.baseRegionImage (source.val.wires dying).scope)
                baseReceipt.outer baseHead := by
          apply eq_of_heq
          have outer :
              HEq (generatedVisibleExact ▸ generatedHead) generatedHead :=
            cast_variable_heq generatedVisibleExact generatedHead
          have inner :
              HEq generatedHead
                (InsertionCompilation.enclosingRenaming compiled
                  (step.baseRegionImage (source.val.wires dying).scope)
                  baseReceipt.outer baseHead) := by
            unfold generatedHead
            exact
              cast_variable_heq generatedVisibleExact.symm
                (InsertionCompilation.enclosingRenaming compiled
                  (step.baseRegionImage (source.val.wires dying).scope)
                  baseReceipt.outer baseHead)
          exact outer.trans inner
        rw [← generatedHeadCast]
        unfold generatedFixed
        rw [cast_env_apply]
        change checkedEnv _ projectedFrameHead = _
        rw [projectedFrameHeadExact]
        exact checkedHeadValue
      · dsimp only
        rw [erasureBaseEnvExact, canonicalParameterExact]
        let compiledParameters :=
          Internal.RelationJoinStep.baseRenamedVariables step priorFrame.visible
            compiled.site.frame.visible baseVisibleExact
            priorFrameParameters
        let baseParameters : Vars
            ((baseReceipt.outer.extend
              (step.baseRegionImage (source.val.wires dying).scope)).sigs)
            parameterSigs :=
          compiledSigsExact.symm ▸ compiledParameters
        let insertedParameters :
            Vars
              (((InsertionCompilation.NaturalityInternal.hostContext
                  step.attachment baseReceipt.outer).extend
                (step.attachment.hostRegion
                  (step.baseRegionImage
                    (source.val.wires dying).scope))).sigs)
              parameterSigs :=
          Vars.rename
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer)
            baseParameters
        let generatedParameters :
            Vars generatedScope.frame.visible.sigs parameterSigs :=
          generatedVisibleExact.symm ▸ insertedParameters
        have compiledParameterOrigins :
            ConcreteElaboration.variableOrigins step.base.val
                compiled.site.frame.visible compiledParameters =
              step.sourceParameters.map step.baseWireImage := by
          unfold compiledParameters
          rw [Internal.RelationJoinStep.baseRenamedVariables_origins,
            priorFrameParameterOrigins, List.map_map]
          apply List.map_congr_left
          intro sourceWire _member
          exact
            SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
              step sourceWire
        have baseParameterOrigins :
            ConcreteElaboration.variableOrigins step.base.val
                (baseReceipt.outer.extend
                  (step.baseRegionImage (source.val.wires dying).scope))
                baseParameters =
              step.sourceParameters.map step.baseWireImage := by
          have proofExact :
              compiledSigsExact.symm =
                congrArg ConcreteElaboration.WireContext.sigs
                  baseExtendedCompiledVisible.symm :=
            Subsingleton.elim _ _
          unfold baseParameters
          rw [proofExact,
            variableOrigins_cast_context step.base.val
              baseExtendedCompiledVisible.symm compiledParameters]
          exact compiledParameterOrigins
        have insertedParameterOrigins :
            ConcreteElaboration.variableOrigins step.attachment.diagram
                ((InsertionCompilation.NaturalityInternal.hostContext
                    step.attachment baseReceipt.outer).extend
                  (step.attachment.hostRegion
                    (step.baseRegionImage (source.val.wires dying).scope)))
                insertedParameters =
              step.sourceParameters.map
                (fun sourceWire =>
                  step.attachment.hostWire
                    (step.baseWireImage sourceWire)) := by
          unfold insertedParameters
          exact
            variableOrigins_rename_mapped step.base.val
              step.attachment.diagram
              (baseReceipt.outer.extend
                (step.baseRegionImage (source.val.wires dying).scope))
              ((InsertionCompilation.NaturalityInternal.hostContext
                  step.attachment baseReceipt.outer).extend
                (step.attachment.hostRegion
                  (step.baseRegionImage (source.val.wires dying).scope)))
              (InsertionCompilation.enclosingRenaming compiled
                (step.baseRegionImage (source.val.wires dying).scope)
                baseReceipt.outer)
              step.baseWireImage
              (fun sourceWire =>
                step.attachment.hostWire (step.baseWireImage sourceWire))
              (fun sourceWire {_} value sourceOrigin => by
                rw [enclosingProjectionOrigin, sourceOrigin])
              baseParameters step.sourceParameters baseParameterOrigins
        have generatedParameterOrigins :
            ConcreteElaboration.variableOrigins step.attachment.diagram
                generatedScope.frame.visible generatedParameters =
              step.sourceParameters.map
                (fun sourceWire =>
                  step.attachment.hostWire
                    (step.baseWireImage sourceWire)) := by
          have proofExact :
              generatedVisibleExact.symm =
                congrArg ConcreteElaboration.WireContext.sigs
                  generatedScopeVisible.symm :=
            Subsingleton.elim _ _
          unfold generatedParameters
          rw [proofExact,
            variableOrigins_cast_context step.attachment.diagram
              generatedScopeVisible.symm insertedParameters]
          exact insertedParameterOrigins
        change Vars.denote compiledEnv compiledParameters = _
        have compiledParametersCast :
            compiledSigsExact ▸ baseParameters = compiledParameters := by
          apply eq_of_heq
          have outer :
              HEq (compiledSigsExact ▸ baseParameters) baseParameters :=
            cast_variables_heq compiledSigsExact baseParameters
          have inner : HEq baseParameters compiledParameters := by
            unfold baseParameters
            exact
              cast_variables_heq compiledSigsExact.symm
                compiledParameters
          exact outer.trans inner
        rw [← compiledParametersCast]
        unfold compiledEnv
        rw [cast_environment_variables_denote]
        change Vars.denote baseFixed baseParameters = _
        unfold baseFixed
        rw [← Vars.denote_rename]
        change Vars.denote generatedFixed insertedParameters = _
        have generatedParametersCast :
            generatedVisibleExact ▸ generatedParameters =
              insertedParameters := by
          apply eq_of_heq
          have outer :
              HEq (generatedVisibleExact ▸ generatedParameters)
                generatedParameters :=
            cast_variables_heq generatedVisibleExact generatedParameters
          have inner : HEq generatedParameters insertedParameters := by
            unfold generatedParameters
            exact
              cast_variables_heq generatedVisibleExact.symm
                insertedParameters
          exact outer.trans inner
        rw [← generatedParametersCast]
        unfold generatedFixed
        rw [cast_environment_variables_denote, ← Vars.denote_rename]
        have projectedParametersChainOrigins :
            ConcreteElaboration.variableOrigins step.checked.val
                checkedScope.frame.visible
                (Vars.rename
                  (InsertionCompilation.NaturalityInternal.equalityRenaming
                    generatedCheckedSigs)
                  generatedParameters) =
              step.sourceParameters.map step.checkedWireImage := by
          apply
            variableOrigins_rename_mapped step.attachment.diagram
              step.checked.val generatedScope.frame.visible
              checkedScope.frame.visible
              (InsertionCompilation.NaturalityInternal.equalityRenaming
                generatedCheckedSigs)
              (fun sourceWire =>
                step.attachment.hostWire (step.baseWireImage sourceWire))
              step.checkedWireImage
              (fun sourceWire {_} value sourceOrigin => by
                have equalityTransport :
                    InsertionCompilation.NaturalityInternal.equalityRenaming
                        generatedCheckedSigs value =
                      transportCheckedVariable checkedExact.symm
                        generatedScope.frame.visible
                        checkedScope.frame.visible
                        checkedGeneratedVisibleExact value := by
                  unfold
                    InsertionCompilation.NaturalityInternal.equalityRenaming
                  apply eq_of_heq
                  exact
                    (cast_variable_heq generatedCheckedSigs value).trans
                      (transportCheckedVariable_heq checkedExact.symm
                        generatedScope.frame.visible
                        checkedScope.frame.visible
                        checkedGeneratedVisibleExact value).symm
                change
                  ConcreteElaboration.WireContext.origin step.checked.val
                      checkedScope.frame.visible.ids
                      (InsertionCompilation.NaturalityInternal.equalityRenaming
                        generatedCheckedSigs value) =
                    step.checkedWireImage sourceWire
                rw [equalityTransport, transportCheckedVariable_origin,
                  sourceOrigin, step.checkedWireImageExact])
              generatedParameters step.sourceParameters
              generatedParameterOrigins
        have projectedParametersChain :
            Vars.rename
                (InsertionCompilation.NaturalityInternal.equalityRenaming
                  generatedCheckedSigs)
                generatedParameters =
              checkedParameters :=
          variables_eq_of_origins step.checked.val
            checkedScope.frame.visible
            (siteCompilation_visible_nodup checkedScope)
            (Vars.rename
              (InsertionCompilation.NaturalityInternal.equalityRenaming
                generatedCheckedSigs)
              generatedParameters)
            checkedParameters
            (projectedParametersChainOrigins.trans
              checkedParameterOrigins.symm)
        rw [projectedParametersChain]
    have priorFrameHolds :=
      (fixedLaw replacement rawEnv localAt).mp replacementFirst
    let priorFrameEnv : Env model.toPreModel priorFrame.visible.sigs :=
      Env.comp
        (congrArg ConcreteElaboration.WireContext.sigs
            erasureProvenance.targetVisible ▸ rawEnv)
        (SingletonRemovalSemantics.contextRenaming step.prior
          step.priorApplication priorFrame.visible)
    let projectedPriorFrameEnv :
        Env model.toPreModel priorScope.frame.visible.sigs :=
      congrArg ConcreteElaboration.WireContext.sigs
          priorScopeFrameVisible.symm ▸ priorFrameEnv
    have priorScopeBodyExact :
        congrArg ConcreteElaboration.WireContext.sigs
            priorScopeFrameVisible.symm ▸ priorFrame.siteBody =
          priorScope.frame.siteBody := by
      apply eq_of_heq
      have frameToSite : HEq priorFrame.siteBody
          step.priorSite.frame.siteBody :=
        (cast_region_heq
          (congrArg ConcreteElaboration.WireContext.sigs priorVisible)
          priorFrame.siteBody).symm.trans (heq_of_eq priorFrameBody)
      have scopeToSite :
          HEq priorScope.frame.siteBody step.priorSite.frame.siteBody := by
        exact regionFrame_siteBody_heq priorScopeSiteExact
      exact
        (cast_region_heq
          (congrArg ConcreteElaboration.WireContext.sigs
            priorScopeFrameVisible.symm)
          priorFrame.siteBody).trans
          (frameToSite.trans scopeToSite.symm)
    have projectedPriorFrameHolds :
        denoteRegion model.toPreModel definitionEnv projectedPriorFrameEnv
          priorScope.frame.siteBody := by
      have transported :=
        (denoteRegion_transport
          (congrArg ConcreteElaboration.WireContext.sigs
            priorScopeFrameVisible.symm)
          model.toPreModel definitionEnv priorFrameEnv
          priorFrame.siteBody).mp priorFrameHolds
      unfold projectedPriorFrameEnv
      rw [priorScopeBodyExact] at transported
      exact transported
    have compiledEnvApply :
        ∀ {sig : Sig} (value : Var priorFrame.visible.sigs sig),
          compiledEnv sig
              (Internal.RelationJoinStep.baseRenamedVariable step priorFrame.visible
                compiled.site.frame.visible baseVisibleExact value) =
            checkedEnv sig (frameProjection value) := by
      intro sig value
      let compiledValue :=
        Internal.RelationJoinStep.baseRenamedVariable step priorFrame.visible
          compiled.site.frame.visible baseVisibleExact value
      let baseValue := compiledSigsExact.symm ▸ compiledValue
      let generatedValue :=
        generatedVisibleExact.symm ▸
          InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseValue
      change compiledEnv sig compiledValue =
        checkedEnv sig (frameProjection value)
      have compiledValueCast :
          compiledSigsExact ▸ baseValue = compiledValue := by
        apply eq_of_heq
        exact
          (cast_variable_heq compiledSigsExact baseValue).trans
            (by
              unfold baseValue
              exact cast_variable_heq compiledSigsExact.symm compiledValue)
      rw [← compiledValueCast]
      unfold compiledEnv
      rw [cast_env_apply]
      change generatedFixed sig
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseValue) =
        checkedEnv sig (frameProjection value)
      have generatedValueCast :
          generatedVisibleExact ▸ generatedValue =
            InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer baseValue := by
        apply eq_of_heq
        exact
          (cast_variable_heq generatedVisibleExact generatedValue).trans
            (by
              unfold generatedValue
              exact cast_variable_heq generatedVisibleExact.symm _)
      rw [← generatedValueCast]
      unfold generatedFixed
      rw [cast_env_apply]
      rfl
    have priorFrameEnvExact :
        priorFrameEnv = Env.comp checkedEnv frameProjection := by
      funext sig value
      have rawApply :=
        transportEnvironment_apply step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication priorFrame.visible)
          compiled.site.frame.visible baseVisibleExact
          (congrArg ConcreteElaboration.WireContext.sigs
              erasureProvenance.targetVisible ▸ rawEnv)
          (SingletonRemovalSemantics.contextRenaming step.prior
            step.priorApplication priorFrame.visible value)
      unfold priorFrameEnv Env.comp
      rw [← rawApply, erasureBaseEnvExact]
      exact compiledEnvApply value
    have projectedFrameValueExact :
        ∀ {sig : Sig} (value : Var priorScope.frame.visible.sigs sig),
          frameProjection
              (transportVariable rfl priorScope.frame.visible
                priorFrame.visible priorScopeFrameVisible value) =
            projection value := by
      intro sig value
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          step.checked.val checkedScope.frame.visible.ids
      · exact siteCompilation_visible_nodup checkedScope
      · let frameValue :=
          transportVariable rfl priorScope.frame.visible priorFrame.visible
            priorScopeFrameVisible value
        let compiledValue :=
          Internal.RelationJoinStep.baseRenamedVariable step priorFrame.visible
            compiled.site.frame.visible baseVisibleExact frameValue
        let baseValue := compiledSigsExact.symm ▸ compiledValue
        let generatedValue :=
          generatedVisibleExact.symm ▸
            InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer baseValue
        have equalityTransport :
            InsertionCompilation.NaturalityInternal.equalityRenaming
                generatedCheckedSigs generatedValue =
              transportCheckedVariable checkedExact.symm
                generatedScope.frame.visible checkedScope.frame.visible
                checkedGeneratedVisibleExact generatedValue := by
          unfold InsertionCompilation.NaturalityInternal.equalityRenaming
          apply eq_of_heq
          exact
            (cast_variable_heq generatedCheckedSigs generatedValue).trans
              (transportCheckedVariable_heq checkedExact.symm
                generatedScope.frame.visible checkedScope.frame.visible
                checkedGeneratedVisibleExact generatedValue).symm
        change
          ConcreteElaboration.WireContext.origin step.checked.val
              checkedScope.frame.visible.ids
              (InsertionCompilation.NaturalityInternal.equalityRenaming
                generatedCheckedSigs generatedValue) =
            ConcreteElaboration.WireContext.origin step.checked.val
              checkedScope.frame.visible.ids (projection value)
        rw [equalityTransport, transportCheckedVariable_origin]
        unfold generatedValue
        rw [origin_cast_context step.attachment.diagram
          generatedScopeVisible.symm, enclosingProjectionOrigin]
        unfold baseValue
        have baseProofExact :
            compiledSigsExact.symm =
              congrArg ConcreteElaboration.WireContext.sigs
                baseExtendedCompiledVisible.symm :=
          Subsingleton.elim _ _
        rw [baseProofExact,
          origin_cast_context step.base.val
            baseExtendedCompiledVisible.symm compiledValue]
        unfold compiledValue Internal.RelationJoinStep.baseRenamedVariable
        rw [transportVariable_origin,
          SingletonRemovalSemantics.contextRenaming_action]
        unfold frameValue
        rw [transportVariable_origin]
        unfold projection
        rw [transportCheckedVariable_origin, transportVariable_origin,
          enclosingProjectionOrigin, transportVariable_origin,
          extendedContextRenaming_origin, transportVariable_origin]
        apply Fin.ext
        rfl
    have projectedPriorFrameEnvExact :
        projectedPriorFrameEnv = Env.comp checkedEnv projection := by
      funext sig value
      let frameValue :=
        transportVariable rfl priorScope.frame.visible priorFrame.visible
          priorScopeFrameVisible value
      have frameValueRoundtrip :
          congrArg ConcreteElaboration.WireContext.sigs
              priorScopeFrameVisible.symm ▸ frameValue =
            value := by
        apply eq_of_heq
        exact
          (cast_variable_heq
            (congrArg ConcreteElaboration.WireContext.sigs
              priorScopeFrameVisible.symm) frameValue).trans
            (by
              unfold frameValue transportVariable
              exact
                cast_variable_heq
                  (congrArg ConcreteElaboration.WireContext.sigs
                    priorScopeFrameVisible)
                  value)
      have castApply :=
        cast_env_apply
          (congrArg ConcreteElaboration.WireContext.sigs
            priorScopeFrameVisible.symm)
          priorFrameEnv frameValue
      rw [frameValueRoundtrip] at castApply
      change projectedPriorFrameEnv sig value =
        checkedEnv sig (projection value)
      unfold projectedPriorFrameEnv
      rw [castApply, priorFrameEnvExact]
      change checkedEnv sig (frameProjection frameValue) =
        checkedEnv sig (projection value)
      rw [projectedFrameValueExact]
    rw [← projectedPriorFrameEnvExact]
    exact projectedPriorFrameHolds
  · obtain ⟨erasureInner, insertionInner, strictLaw⟩ :=
      Internal.RelationJoinStep.strictDescendantBodyDenotation step contentCompiled
        compiled model definitionEnv erasureProvenance pairedErasure
        pairedInsertion coScoped (.atom head arguments)
        applicationCompiled
    obtain ⟨generatedCheckedSigs, generatedCheckedBody⟩ :=
      transportedSiteCompilation_body checkedExact.symm generatedScope
        checkedSiteExact
    have generatedScopeHolds :
        denoteRegion model.toPreModel definitionEnv
          (Env.comp checkedEnv
            (InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs))
          generatedScope.frame.siteBody := by
      apply
        (InsertionCompilation.NaturalityInternal.denoteRegion_castContext
          model.toPreModel definitionEnv generatedCheckedSigs checkedEnv
          generatedScope.frame.siteBody).mp
      rw [generatedCheckedBody]
      exact checkedHolds
    let generatedVisibleExact :=
      congrArg ConcreteElaboration.WireContext.sigs generatedScopeVisible
    let generatedFixed :
        Env model.toPreModel
          ((InsertionCompilation.NaturalityInternal.hostContext
              step.attachment baseReceipt.outer).extend
            (step.attachment.hostRegion
              (step.baseRegionImage
                (source.val.wires dying).scope))).sigs :=
      generatedVisibleExact ▸
        Env.comp checkedEnv
          (InsertionCompilation.NaturalityInternal.equalityRenaming
            generatedCheckedSigs)
    have canonicalTargetHolds :
        denoteRegion model.toPreModel definitionEnv generatedFixed
          (canonicalInner.targetInner.fill generatedFrame.siteBody) := by
      have transported :=
        (denoteRegion_transport generatedVisibleExact model.toPreModel
          definitionEnv
          (Env.comp checkedEnv
            (InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs))
          generatedScope.frame.siteBody).mp generatedScopeHolds
      unfold generatedFixed
      rw [generatedScopeBody] at transported
      exact transported
    have canonicalStrictTargetInner :
        canonicalInner.targetInner = insertionInner.targetInner := by
      apply
        bindContextFor_injective step.attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment baseReceipt.outer).ids
          (step.attachment.diagram.wiresAt
            (step.attachment.hostRegion
              (step.baseRegionImage (source.val.wires dying).scope)))
      exact
        canonicalInner.targetDecomposition.symm.trans
          insertionInner.targetDecomposition
    have insertionTargetHolds :
        denoteRegion model.toPreModel definitionEnv generatedFixed
          (insertionInner.targetInner.fill generatedFrame.siteBody) := by
      rw [← canonicalStrictTargetInner]
      exact canonicalTargetHolds
    have erasedSigsExact :
        (((SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorOuter).extend
            (SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage
                (source.val.wires dying).scope))).sigs) =
          (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs :=
      (transport_context_sigs step.base_generated.symm
        ((SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication priorOuter).extend
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage
              (source.val.wires dying).scope)))).symm.trans
        (congrArg ConcreteElaboration.WireContext.sigs
          baseExtendedContextExact)
    let erasedFixed :
        Env model.toPreModel
          (((SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication priorOuter).extend
              (SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage
                  (source.val.wires dying).scope))).sigs) :=
      erasedSigsExact.symm ▸
        Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer)
    have erasedFixedExact :
        HEq
          (Env.comp generatedFixed
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer))
          erasedFixed := by
      unfold erasedFixed
      exact
        (eqRec_heq _ _).symm
    let strictBaseVisibleExact :=
      RelationJoinStep.pairedInsertion_baseVisibleExact step
        contentCompiled compiled rawFrame erasureProvenance pairedInsertion
    let strictCanonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication priorFrame.visible)
        compiled.site.frame.visible strictBaseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let strictReplacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          erasureProvenance.targetVisible.symm ▸
        strictCanonicalReplacement
    have priorStrictNotSite :
        step.priorRegionImage (source.val.wires dying).scope ≠
          step.priorRegionImage step.sourceRegion := by
      intro same
      apply coScoped
      apply
        InsertionCompilation.NaturalityInternal.checked_encloses_antisymm
          definitions source.val source.property
      · apply
          (step.priorRegionImageEncloses
            (source.val.wires dying).scope step.sourceRegion).mp
        simpa [same] using
          step.prior.val.encloses_refl
            (step.priorRegionImage step.sourceRegion)
      · apply
          (step.priorRegionImageEncloses
            step.sourceRegion (source.val.wires dying).scope).mp
        simpa [same] using
          step.prior.val.encloses_refl
            (step.priorRegionImage (source.val.wires dying).scope)
    have priorFrameNodup : priorFrame.visible.ids.Nodup := by
      rw [priorVisible]
      exact siteCompilation_visible_nodup step.priorSite
    have rawFrameNodup : rawFrame.visible.ids.Nodup := by
      rw [erasureProvenance.targetVisible, List.nodup_iff_pairwise_ne]
      rw [List.nodup_iff_pairwise_ne] at priorFrameNodup
      exact priorFrameNodup.map
        (SingletonRemovalSemantics.targetWire step.prior
          step.priorApplication) (by
            intro left right different equality
            exact different
              (ConcreteDiagram.DenseErasure.eraseNodeWire_injective
                step.prior step.priorApplication equality))
    have erasureSourceInnerExact :
        erasureInner.sourceInner = priorInner := by
      apply
        bindContextFor_injective step.prior.val priorOuter.ids
          (step.prior.val.wiresAt
            (step.priorRegionImage (source.val.wires dying).scope))
      exact
        erasureInner.sourceDecomposition.symm.trans priorDecomposition
    let priorOuterHead :=
      transportVariable rfl priorScope.frame.visible
        (priorOuter.extend
          (step.priorRegionImage (source.val.wires dying).scope))
        priorScopeVisible priorHead
    have sourceLiftHeadExact :
        DiagramContext.liftOuter erasureInner.sourceInner priorOuterHead =
          head := by
      rw [erasureSourceInnerExact]
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          step.prior.val priorFrame.visible.ids priorFrameNodup
      rw [compileRegionFrame?_strict_inner_liftOuter_origin definitions
          step.prior.val (step.priorRegionImage step.sourceRegion) fuel
          (step.priorRegionImage (source.val.wires dying).scope)
          priorOuter priorFrame priorInner priorStrictNotSite
          priorGenerated priorDecomposition,
        show
          ConcreteElaboration.WireContext.origin step.prior.val
              (priorOuter.extend
                (step.priorRegionImage
                  (source.val.wires dying).scope)).ids priorOuterHead =
            ConcreteElaboration.WireContext.origin step.prior.val
              priorScope.frame.visible.ids priorHead by
                unfold priorOuterHead
                rw [transportVariable_origin]
                simp,
        (List.cons.inj priorHeadOrigin).1, headOrigin]
    have rawLiftHeadExact :
        DiagramContext.liftOuter erasureInner.targetInner
            (SingletonRemovalSemantics.extendedContextRenaming step.prior
              step.priorApplication priorOuter
              (step.priorRegionImage (source.val.wires dying).scope)
              priorOuterHead) =
          SingletonRemovalSemantics.erasureVisibleRenaming
            step.priorApplication priorFrame
            erasureProvenance.targetVisible head := by
      rw [← sourceLiftHeadExact]
      exact
        erasureInner.liftOuter_erasureVisibleRenaming
          step.priorApplication (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope) fuel
          priorOuter priorFrame rawFrame priorStrictNotSite priorGenerated
          (by simpa [step.priorNodeExact] using
            erasureProvenance.targetGenerated)
          erasureProvenance.targetVisible rawFrameNodup priorOuterHead
    have erasedFixedApply :
        ∀ {sig : Sig} (value : Var priorScope.frame.visible.sigs sig),
          erasedFixed sig
              (SingletonRemovalSemantics.extendedContextRenaming step.prior
                step.priorApplication priorOuter
                (step.priorRegionImage (source.val.wires dying).scope)
                (transportVariable rfl priorScope.frame.visible
                  (priorOuter.extend
                    (step.priorRegionImage
                      (source.val.wires dying).scope))
                  priorScopeVisible value)) =
            checkedEnv sig (projection value) := by
      intro sig value
      let rawHead :=
        SingletonRemovalSemantics.extendedContextRenaming step.prior
          step.priorApplication priorOuter
          (step.priorRegionImage (source.val.wires dying).scope)
          (transportVariable rfl priorScope.frame.visible
            (priorOuter.extend
              (step.priorRegionImage (source.val.wires dying).scope))
            priorScopeVisible value)
      let baseHead :=
        transportVariable step.base_generated.symm
          ((SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication priorOuter).extend
            (SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage
                (source.val.wires dying).scope)))
          (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope))
          baseExtendedContextExact rawHead
      have erasedHeadCast :
          erasedSigsExact.symm ▸ baseHead = rawHead := by
        apply eq_of_heq
        exact
          (cast_variable_heq erasedSigsExact.symm baseHead).trans
            (by
              unfold baseHead
              exact
                (transportVariable_heq step.base_generated.symm
                  ((SingletonRemovalSemantics.targetContext step.prior
                      step.priorApplication priorOuter).extend
                    (SingletonRemovalSemantics.targetRegion step.prior
                      step.priorApplication
                      (step.priorRegionImage
                        (source.val.wires dying).scope)))
                  (baseReceipt.outer.extend
                    (step.baseRegionImage
                      (source.val.wires dying).scope))
                  baseExtendedContextExact rawHead))
      change erasedFixed sig rawHead = _
      rw [← erasedHeadCast]
      unfold erasedFixed
      rw [cast_env_apply]
      let generatedHead :=
        transportVariable rfl
          ((InsertionCompilation.NaturalityInternal.hostContext
              step.attachment baseReceipt.outer).extend
            (step.attachment.hostRegion
              (step.baseRegionImage (source.val.wires dying).scope)))
          generatedScope.frame.visible generatedScopeVisible.symm
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseHead)
      have generatedHeadCast :
          generatedVisibleExact ▸ generatedHead =
            InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer baseHead := by
        apply eq_of_heq
        exact
          (cast_variable_heq generatedVisibleExact generatedHead).trans
            (by
              unfold generatedHead
              exact
                (transportVariable_heq rfl
                  ((InsertionCompilation.NaturalityInternal.hostContext
                      step.attachment baseReceipt.outer).extend
                    (step.attachment.hostRegion
                      (step.baseRegionImage
                        (source.val.wires dying).scope)))
                  generatedScope.frame.visible generatedScopeVisible.symm
                  _))
      change generatedFixed sig
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer baseHead) = _
      rw [← generatedHeadCast]
      unfold generatedFixed
      rw [cast_env_apply]
      have projectedHeadExact :
          InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs generatedHead =
            projection value := by
        change
          InsertionCompilation.NaturalityInternal.equalityRenaming
              generatedCheckedSigs generatedHead =
            transportCheckedVariable checkedExact.symm
              generatedScope.frame.visible checkedScope.frame.visible
              checkedGeneratedVisibleExact generatedHead
        unfold
          InsertionCompilation.NaturalityInternal.equalityRenaming
        apply eq_of_heq
        exact
          (cast_variable_heq generatedCheckedSigs generatedHead).trans
            (transportCheckedVariable_heq checkedExact.symm
              generatedScope.frame.visible checkedScope.frame.visible
              checkedGeneratedVisibleExact generatedHead).symm
      change checkedEnv sig
          (InsertionCompilation.NaturalityInternal.equalityRenaming
            generatedCheckedSigs generatedHead) = _
      rw [projectedHeadExact]
    have erasedFixedHeadValue :
        erasedFixed (.rel step.relationArgs)
            (SingletonRemovalSemantics.extendedContextRenaming step.prior
              step.priorApplication priorOuter
              (step.priorRegionImage (source.val.wires dying).scope)
              priorOuterHead) =
          WireQuantifierSemantics.contentRelation model definitionEnv
            contentCompiled boundaryExact parameterValues := by
      rw [show priorOuterHead =
          transportVariable rfl priorScope.frame.visible
            (priorOuter.extend
              (step.priorRegionImage (source.val.wires dying).scope))
            priorScopeVisible priorHead by rfl,
        erasedFixedApply, show projection priorHead = checkedHead by rfl]
      exact checkedHeadValue
    let priorOuterParameters :=
      transportVariables rfl priorScope.frame.visible
        (priorOuter.extend
          (step.priorRegionImage (source.val.wires dying).scope))
        priorScopeVisible priorParameters
    let rawOuterParameters :=
      Vars.rename
        (SingletonRemovalSemantics.extendedContextRenaming step.prior
          step.priorApplication priorOuter
          (step.priorRegionImage (source.val.wires dying).scope))
        priorOuterParameters
    have erasedFixedParameterValue :
        Vars.denote erasedFixed rawOuterParameters = parameterValues := by
      rw [← checkedParameterValues]
      have denoteErasedFixed :
          ∀ {args : List Sig}
            (values : Vars priorScope.frame.visible.sigs args),
            Vars.denote erasedFixed
                (Vars.rename
                  (SingletonRemovalSemantics.extendedContextRenaming
                    step.prior step.priorApplication priorOuter
                    (step.priorRegionImage
                      (source.val.wires dying).scope))
                  (transportVariables rfl priorScope.frame.visible
                    (priorOuter.extend
                      (step.priorRegionImage
                        (source.val.wires dying).scope))
                    priorScopeVisible values)) =
              Vars.denote checkedEnv (Vars.rename projection values) := by
        intro args values
        induction values with
        | nil => rfl
        | @cons sig args value values induction =>
            rw [transportVariables_cons]
            simp only [Vars.rename, Vars.denote_cons]
            rw [erasedFixedApply, induction]
      have exactValues :
          Vars.denote erasedFixed rawOuterParameters =
            Vars.denote checkedEnv checkedParameters := by
        unfold rawOuterParameters priorOuterParameters checkedParameters
        exact denoteErasedFixed priorParameters
      exact exactValues
    have priorOuterParameterOrigins :
        ConcreteElaboration.variableOrigins step.prior.val
            (priorOuter.extend
              (step.priorRegionImage (source.val.wires dying).scope))
            priorOuterParameters =
          step.sourceParameters.map step.priorWireImage := by
      unfold priorOuterParameters
      rw [transportVariables_origins]
      simpa using priorParameterOrigins
    let priorFrameParameters :=
      Vars.rename (DiagramContext.liftOuter erasureInner.sourceInner)
        priorOuterParameters
    have priorFrameParameterOrigins :
        ConcreteElaboration.variableOrigins step.prior.val
            priorFrame.visible priorFrameParameters =
          step.sourceParameters.map step.priorWireImage := by
      unfold priorFrameParameters
      apply
        variableOrigins_rename_mapped step.prior.val step.prior.val
          (priorOuter.extend
            (step.priorRegionImage (source.val.wires dying).scope))
          priorFrame.visible
          (DiagramContext.liftOuter erasureInner.sourceInner)
          step.priorWireImage step.priorWireImage
          (fun sourceWire {_} value sourceOrigin => by
            rw [compileRegionFrame?_strict_inner_liftOuter_origin definitions
              step.prior.val (step.priorRegionImage step.sourceRegion) fuel
              (step.priorRegionImage (source.val.wires dying).scope)
              priorOuter priorFrame erasureInner.sourceInner
              priorStrictNotSite priorGenerated
              erasureInner.sourceDecomposition,
              sourceOrigin])
          priorOuterParameters step.sourceParameters
          priorOuterParameterOrigins
    have canonicalParameterExact :
        parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
          baseRenamedVariables step priorFrame.visible
            compiled.site.frame.visible strictBaseVisibleExact
            priorFrameParameters :=
      Internal.RelationJoinStep.parameterVariables_exact step contentCompiled compiled
        boundaryExact priorFrame.visible strictBaseVisibleExact arguments
        argumentOrigins priorFrameParameters priorFrameParameterOrigins
    have rawFrameParametersExact :
        Vars.rename (DiagramContext.liftOuter erasureInner.targetInner)
            rawOuterParameters =
          Vars.rename
            (SingletonRemovalSemantics.erasureVisibleRenaming
              step.priorApplication priorFrame
              erasureProvenance.targetVisible)
            priorFrameParameters := by
      unfold rawOuterParameters priorFrameParameters
      have commutes :
          ∀ {args : List Sig}
            (values :
              Vars
                (priorOuter.extend
                  (step.priorRegionImage
                    (source.val.wires dying).scope)).sigs args),
            Vars.rename (DiagramContext.liftOuter erasureInner.targetInner)
                (Vars.rename
                  (SingletonRemovalSemantics.extendedContextRenaming
                    step.prior step.priorApplication priorOuter
                    (step.priorRegionImage
                      (source.val.wires dying).scope))
                  values) =
              Vars.rename
                (SingletonRemovalSemantics.erasureVisibleRenaming
                  step.priorApplication priorFrame
                  erasureProvenance.targetVisible)
                (Vars.rename
                  (DiagramContext.liftOuter erasureInner.sourceInner)
                  values) := by
        intro args values
        induction values with
        | nil => rfl
        | @cons sig args value values induction =>
            simp only [Vars.rename]
            rw [erasureInner.liftOuter_erasureVisibleRenaming
              step.priorApplication (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope) fuel
              priorOuter priorFrame rawFrame priorStrictNotSite priorGenerated
              (by simpa [step.priorNodeExact] using
                erasureProvenance.targetGenerated)
              erasureProvenance.targetVisible rawFrameNodup value,
              induction]
      exact commutes priorOuterParameters
    have strictResult :=
      strictLaw generatedFixed erasedFixed erasedFixedExact
        (by
          intro descendant preserves
          have descendantParameterValue :
              Vars.denote descendant
                  (Vars.rename
                    (SingletonRemovalSemantics.erasureVisibleRenaming
                      step.priorApplication priorFrame
                      erasureProvenance.targetVisible)
                    priorFrameParameters) =
                parameterValues := by
            rw [← rawFrameParametersExact, Vars.denote_rename, preserves]
            exact erasedFixedParameterValue
          apply
            Internal.RelationJoinStep.erasureLocalReplacementAt step contentCompiled
              compiled model definitionEnv boundaryExact parameterValues
              priorFrame rawFrame erasureProvenance strictBaseVisibleExact
              head arguments argumentOrigins descendant
          · dsimp only
            have preservedHead :=
              congrFun (congrFun preserves (.rel step.relationArgs))
                (SingletonRemovalSemantics.extendedContextRenaming step.prior
                  step.priorApplication priorOuter
                  (step.priorRegionImage (source.val.wires dying).scope)
                  priorOuterHead)
            change
              descendant (.rel step.relationArgs)
                  (DiagramContext.liftOuter erasureInner.targetInner
                    (SingletonRemovalSemantics.extendedContextRenaming
                      step.prior step.priorApplication priorOuter
                      (step.priorRegionImage
                        (source.val.wires dying).scope)
                      priorOuterHead)) =
                erasedFixed (.rel step.relationArgs)
                  (SingletonRemovalSemantics.extendedContextRenaming step.prior
                    step.priorApplication priorOuter
                    (step.priorRegionImage
                      (source.val.wires dying).scope)
                    priorOuterHead) at preservedHead
            rw [rawLiftHeadExact, erasedFixedHeadValue] at preservedHead
            have canonicalHeadValue :=
              cast_env_apply
                (congrArg ConcreteElaboration.WireContext.sigs
                  erasureProvenance.targetVisible)
                descendant
                (SingletonRemovalSemantics.erasureVisibleRenaming
                  step.priorApplication priorFrame
                  erasureProvenance.targetVisible head)
            have canonicalHeadRoundtrip :
                congrArg ConcreteElaboration.WireContext.sigs
                    erasureProvenance.targetVisible ▸
                  SingletonRemovalSemantics.erasureVisibleRenaming
                    step.priorApplication priorFrame
                    erasureProvenance.targetVisible head =
                SingletonRemovalSemantics.contextRenaming step.prior
                  step.priorApplication priorFrame.visible head := by
              exact
                cast_renaming_roundtrip
                  (congrArg ConcreteElaboration.WireContext.sigs
                    erasureProvenance.targetVisible)
                  (SingletonRemovalSemantics.contextRenaming step.prior
                    step.priorApplication priorFrame.visible) head
            rw [canonicalHeadRoundtrip, preservedHead] at canonicalHeadValue
            simpa [Internal.RelationJoinStep.baseRenamedVariable,
              transportEnvironment_apply,
              SingletonRemovalSemantics.erasureVisibleRenaming] using
              canonicalHeadValue
          · rw [canonicalParameterExact]
            dsimp only
            unfold Internal.RelationJoinStep.baseRenamedVariables
            rw [transportEnvironment_denote]
            have canonicalParameterRoundtrip :
                congrArg ConcreteElaboration.WireContext.sigs
                    erasureProvenance.targetVisible ▸
                  Vars.rename
                    (SingletonRemovalSemantics.erasureVisibleRenaming
                      step.priorApplication priorFrame
                      erasureProvenance.targetVisible)
                    priorFrameParameters =
                Vars.rename
                  (SingletonRemovalSemantics.contextRenaming step.prior
                    step.priorApplication priorFrame.visible)
                  priorFrameParameters := by
              apply eq_of_heq
              refine
                (cast_variables_heq
                  (congrArg ConcreteElaboration.WireContext.sigs
                    erasureProvenance.targetVisible)
                  (Vars.rename
                    (SingletonRemovalSemantics.erasureVisibleRenaming
                      step.priorApplication priorFrame
                      erasureProvenance.targetVisible)
                    priorFrameParameters)).trans ?_
              unfold SingletonRemovalSemantics.erasureVisibleRenaming
              exact
                cast_renaming_variables_heq
                  (congrArg ConcreteElaboration.WireContext.sigs
                    erasureProvenance.targetVisible.symm)
                  (SingletonRemovalSemantics.contextRenaming step.prior
                    step.priorApplication priorFrame.visible)
                  priorFrameParameters
            have canonicalParameterValue :=
              cast_environment_variables_denote
                (congrArg ConcreteElaboration.WireContext.sigs
                  erasureProvenance.targetVisible)
                descendant
                (Vars.rename
                  (SingletonRemovalSemantics.erasureVisibleRenaming
                    step.priorApplication priorFrame
                    erasureProvenance.targetVisible)
                  priorFrameParameters)
            rw [canonicalParameterRoundtrip, descendantParameterValue] at canonicalParameterValue
            exact canonicalParameterValue)
        insertionTargetHolds
    have strictSourceBodyExact :
        congrArg ConcreteElaboration.WireContext.sigs priorScopeVisible ▸
            priorScope.frame.siteBody =
          erasureInner.sourceInner.fill priorFrame.siteBody := by
      rw [erasureSourceInnerExact]
      exact priorScopeBody
    let strictSourceEnv :=
      Env.comp erasedFixed
        (SingletonRemovalSemantics.extendedContextRenaming step.prior
          step.priorApplication priorOuter
          (step.priorRegionImage (source.val.wires dying).scope))
    have strictSourceEnvExact :
        congrArg ConcreteElaboration.WireContext.sigs priorScopeVisible.symm ▸
            strictSourceEnv =
          Env.comp checkedEnv projection := by
      funext sig value
      let outerValue :=
        transportVariable rfl priorScope.frame.visible
          (priorOuter.extend
            (step.priorRegionImage (source.val.wires dying).scope))
          priorScopeVisible value
      have outerValueRoundtrip :
          congrArg ConcreteElaboration.WireContext.sigs
              priorScopeVisible.symm ▸ outerValue =
            value := by
        apply eq_of_heq
        exact
          (cast_variable_heq
            (congrArg ConcreteElaboration.WireContext.sigs
              priorScopeVisible.symm)
            outerValue).trans
            (transportVariable_heq rfl priorScope.frame.visible
              (priorOuter.extend
                (step.priorRegionImage (source.val.wires dying).scope))
              priorScopeVisible value)
      have castApply :=
        cast_env_apply
          (congrArg ConcreteElaboration.WireContext.sigs
            priorScopeVisible.symm)
          strictSourceEnv outerValue
      rw [outerValueRoundtrip] at castApply
      change
        (congrArg ConcreteElaboration.WireContext.sigs
              priorScopeVisible.symm ▸ strictSourceEnv)
            sig value =
          checkedEnv sig (projection value)
      rw [castApply]
      unfold strictSourceEnv Env.comp
      exact erasedFixedApply value
    have transportedBodyExact :
        congrArg ConcreteElaboration.WireContext.sigs priorScopeVisible.symm ▸
            erasureInner.sourceInner.fill priorFrame.siteBody =
          priorScope.frame.siteBody := by
      rw [← strictSourceBodyExact]
      apply eq_of_heq
      exact
        (cast_region_heq
          (congrArg ConcreteElaboration.WireContext.sigs
            priorScopeVisible.symm)
          (congrArg ConcreteElaboration.WireContext.sigs
              priorScopeVisible ▸ priorScope.frame.siteBody)).trans
          (cast_region_heq
            (congrArg ConcreteElaboration.WireContext.sigs
              priorScopeVisible)
            priorScope.frame.siteBody)
    have transported :=
      (denoteRegion_transport
        (congrArg ConcreteElaboration.WireContext.sigs
          priorScopeVisible.symm)
        model.toPreModel definitionEnv strictSourceEnv
        (erasureInner.sourceInner.fill priorFrame.siteBody)).mp strictResult
    rw [strictSourceEnvExact, transportedBodyExact] at transported
    exact transported


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
