import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinTraceSemantics
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalFinal
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinResult

/--
The executable ordered splice trace reaches a raw checked endpoint whose
canonical eager normalization denotes exactly the public join target.
-/
theorem trace_denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ steps : List (RelationJoinStep source wire content),
      RelationJoinSemanticTrace source wire content parameters result.args
          steps result.boundFinal result.boundRegionImage
            result.boundWireImage result.boundDying
            (result.boundRegionImage (source.val.wires wire).scope) ∧
        steps.map RelationJoinStep.application =
          result.applications ∧
        (denoteChecked pre definitionEnv result.checked ↔
          denoteChecked pre definitionEnv result.plainFinal) := by
  obtain ⟨steps, normalization, trace, applicationsExact,
      normalizationExact, targetExact⟩ :=
    result.trace_complete
  refine
    ⟨steps, trace, applicationsExact, ?_⟩
  rw [normalizationExact] at targetExact
  rw [← targetExact]
  exact
    ConcreteDiagram.normalizeIdentities_sound result.plainFinal pre
      definitionEnv

end RelationJoinResult

namespace RelationJoinSemantics

open Internal

private def relationJoinFinishMany
    (bound : List Sig) :
    Region definitions (bound ++ outer) → Region definitions outer :=
  match bound with
  | [] => fun body => body
  | sig :: rest => fun body =>
      relationJoinFinishMany rest
        (.mk (.cons (.bind sig body) .nil))

private theorem relationJoin_bindMany_fill
    (bound : List Sig)
    (inner :
      DiagramContext definitions hole (bound ++ outer))
    (body : Region definitions hole) :
    (DiagramContext.bindMany bound inner).fill body =
      relationJoinFinishMany bound (inner.fill body) := by
  induction bound generalizing outer with
  | nil => rfl
  | cons sig rest induction =>
      simpa [DiagramContext.bindMany, DiagramContext.fill,
        relationJoinFinishMany] using induction (.bind sig inner)

private theorem relationJoin_bindMany_cutDepth
    (bound : List Sig)
    (inner :
      DiagramContext definitions hole (bound ++ outer)) :
    (DiagramContext.bindMany bound inner).cutDepth = inner.cutDepth := by
  induction bound generalizing outer with
  | nil => rfl
  | cons sig rest induction =>
      simpa [DiagramContext.bindMany, DiagramContext.cutDepth] using
        induction (.bind sig inner)

private theorem relationJoin_stopsAboveBindMany_cutDepth
    {stopped :
      DiagramContext definitions stoppedHole outer}
    {full :
      DiagramContext definitions (bound ++ stoppedHole) outer}
    (decomposition : DiagramContext.StopsAboveBindMany bound stopped full) :
    full.cutDepth = stopped.cutDepth := by
  induction decomposition with
  | hole full exact =>
      subst full
      exact relationJoin_bindMany_cutDepth bound _
  | surround leading suffix inner induction =>
      simpa [DiagramContext.cutDepth] using induction
  | cut inner induction =>
      simpa [DiagramContext.cutDepth] using congrArg Nat.succ induction
  | bind inner induction =>
      simpa [DiagramContext.cutDepth] using induction

private theorem relationJoin_stopsAboveBindMany_fill_finishMany
    {stopped :
      DiagramContext definitions stoppedHole outer}
    {full :
      DiagramContext definitions (bound ++ stoppedHole) outer}
    (decomposition : DiagramContext.StopsAboveBindMany bound stopped full)
    (body : Region definitions (bound ++ stoppedHole)) :
    full.fill body =
      stopped.fill (relationJoinFinishMany bound body) := by
  induction decomposition with
  | hole full exact =>
      subst full
      exact relationJoin_bindMany_fill bound .hole body
  | surround leading suffix inner induction =>
      simpa [DiagramContext.fill] using
        congrArg (fun region => Region.surround leading region suffix)
          (induction body)
  | cut inner induction =>
      simpa [DiagramContext.fill] using
        congrArg (fun region => Region.mk (.cons (.cut region) .nil))
          (induction body)
  | bind inner induction =>
      simpa [DiagramContext.fill] using
        congrArg (fun region => Region.mk (.cons (.bind _ region) .nil))
          (induction body)

private theorem relationJoin_castContextFill
    {leftHole rightHole outer : List Sig}
    (same : leftHole = rightHole)
    (context : DiagramContext definitions leftHole outer)
    (body : Region definitions leftHole) :
    (same ▸ context).fill (same ▸ body) = context.fill body := by
  cases same
  rfl

private theorem relationJoin_castContextCutDepth
    {leftHole rightHole outer : List Sig}
    (same : leftHole = rightHole)
    (context : DiagramContext definitions leftHole outer) :
    (same ▸ context).cutDepth = context.cutDepth := by
  cases same
  rfl

private def relationJoinCastContextOuter
    (same : left = right)
    (context : DiagramContext definitions hole left) :
    DiagramContext definitions hole right :=
  same ▸ context

private theorem relationJoin_castHoleOuter_heq
    (same : left = right) :
    HEq
      (.hole : DiagramContext definitions right right)
      (relationJoinCastContextOuter same
        (.hole : DiagramContext definitions left left)) := by
  cases same
  rfl

private theorem relationJoin_castEnvBack_apply
    {left right : List Sig}
    (same : left = right)
    (env : Env pre right)
    {sig : Sig}
    (value : Var left sig) :
    (same.symm ▸ env) sig value = env sig (same ▸ value) := by
  cases same
  rfl

private theorem relationJoin_castEnvRoundtrip
    {left right : List Sig}
    (same : left = right)
    (env : Env pre right) :
    same ▸ (same.symm ▸ env) = env := by
  cases same
  rfl

private theorem relationJoin_castVarRoundtrip
    {left right : List Sig}
    (same : left = right)
    {sig : Sig}
    (value : Var right sig) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem relationJoin_denote_cast_context
    {left right : List Sig}
    (same : left = right)
    (env : Env pre left)
    (body : Region definitions left) :
    denoteRegion pre definitionEnv (same ▸ env) (same ▸ body) ↔
      denoteRegion pre definitionEnv env body := by
  cases same
  rfl

private theorem relationJoin_removedFrameValue
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext
        (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
          source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond :
      ExhaustedWireRemovalSemantics.ContextsCorrespond source removed
        targetContext sourceContext)
    (frameContext : ConcreteElaboration.WireContext source.val)
    (visibleExact : frameContext = sourceContext)
    (signatureExact : (source.val.wires removed).sig = sig)
    (pre : PreModel.{u})
    (relationValue : pre.Domain sig)
    (targetEnv : Env pre targetContext.sigs)
    (value : Var frameContext.sigs sig)
    (origin :
      ConcreteElaboration.WireContext.origin source.val frameContext.ids
          value =
        removed) :
    let specified :=
      (congrArg pre.Domain signatureExact).symm ▸ relationValue
    let sourceEnv :=
      ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget source
        removed targetContext sourceContext correspond pre specified
        targetEnv
    ((congrArg ConcreteElaboration.WireContext.sigs
        visibleExact).symm ▸ sourceEnv) _ value =
      relationValue := by
  cases visibleExact
  cases signatureExact
  exact
    ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget_removed
      source removed targetContext sourceContext correspond pre relationValue
      targetEnv value origin

private theorem relationJoin_aboveScope_fill_finishRegion
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    compiled.frame.context.fill compiled.frame.siteBody =
      canonical.above.fill
        (ConcreteElaboration.finishRegion base.val canonical.siteOuter site
          (congrArg ConcreteElaboration.WireContext.sigs
            canonical.visibleExact ▸ compiled.frame.siteBody)) := by
  let visibleSigs :=
    congrArg ConcreteElaboration.WireContext.sigs canonical.visibleExact
  let extendSigs :=
    ConcreteElaboration.WireContext.sigs_extend canonical.siteOuter site
  let holeExact := visibleSigs.trans extendSigs
  let castBody : Region definitions
      (((base.val.wiresAt site).map
          (fun wire => (base.val.wires wire).sig)) ++
        canonical.siteOuter.sigs) :=
    holeExact ▸ compiled.frame.siteBody
  have decomposed :=
    relationJoin_stopsAboveBindMany_fill_finishMany
      canonical.contextDecomposition castBody
  have proofExact :
      ((congrArg ConcreteElaboration.WireContext.sigs
          canonical.visibleExact).trans
        (ConcreteElaboration.WireContext.sigs_extend
          canonical.siteOuter site)) =
        holeExact :=
    Subsingleton.elim _ _
  rw [proofExact] at decomposed
  change
    (holeExact ▸ compiled.frame.context).fill
        (holeExact ▸ compiled.frame.siteBody) =
      _ at decomposed
  rw [relationJoin_castContextFill] at decomposed
  rw [decomposed]
  congr 1
  change
    relationJoinFinishMany
        ((base.val.wiresAt site).map
          (fun wire => (base.val.wires wire).sig))
        castBody =
      ConcreteElaboration.finishRegion base.val canonical.siteOuter site
        (visibleSigs ▸ compiled.frame.siteBody)
  calc
    relationJoinFinishMany
        ((base.val.wiresAt site).map
          (fun wire => (base.val.wires wire).sig))
        castBody =
      (DiagramContext.bindMany
        ((base.val.wiresAt site).map
          (fun wire => (base.val.wires wire).sig))
        (.hole : DiagramContext definitions
          (((base.val.wiresAt site).map
              (fun wire => (base.val.wires wire).sig)) ++
            canonical.siteOuter.sigs)
          (((base.val.wiresAt site).map
              (fun wire => (base.val.wires wire).sig)) ++
            canonical.siteOuter.sigs))).fill castBody :=
      (relationJoin_bindMany_fill _ .hole castBody).symm
    _ =
      (bindContextFor base.val canonical.siteOuter.ids
        (base.val.wiresAt site)
        (.hole :
          DiagramContext definitions
            (canonical.siteOuter.extend site).sigs
            (canonical.siteOuter.extend site).sigs)).fill
          (visibleSigs ▸ compiled.frame.siteBody) := by
      rw [bindContextFor_eq_bindMany]
      rw [relationJoin_bindMany_fill, relationJoin_bindMany_fill]
      congr
      · exact extendSigs.symm
      · exact relationJoin_castHoleOuter_heq extendSigs
      · exact
          (cast_region_heq holeExact compiled.frame.siteBody).trans
            (cast_region_heq visibleSigs compiled.frame.siteBody).symm
    _ = _ := by
      rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
      rfl

private theorem relationJoin_aboveScope_cutDepth_eq
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    compiled.frame.context.cutDepth = canonical.above.cutDepth := by
  let visibleSigs :=
    congrArg ConcreteElaboration.WireContext.sigs canonical.visibleExact
  let extendSigs :=
    ConcreteElaboration.WireContext.sigs_extend canonical.siteOuter site
  let holeExact := visibleSigs.trans extendSigs
  have decomposed :=
    relationJoin_stopsAboveBindMany_cutDepth
      canonical.contextDecomposition
  have proofExact :
      ((congrArg ConcreteElaboration.WireContext.sigs
          canonical.visibleExact).trans
        (ConcreteElaboration.WireContext.sigs_extend
          canonical.siteOuter site)) =
        holeExact :=
    Subsingleton.elim _ _
  rw [proofExact] at decomposed
  change
    (holeExact ▸ compiled.frame.context).cutDepth =
      canonical.above.cutDepth at decomposed
  exact
    (relationJoin_castContextCutDepth holeExact
      compiled.frame.context).symm.trans decomposed

private theorem relationJoin_castVisibleEnv_appendRightRaw
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site)
    (env : Env pre visible.sigs)
    {sig : Sig}
    (value : Var outer.sigs sig) :
    (congrArg ConcreteElaboration.WireContext.sigs same ▸ env)
        sig
        (ConcreteElaboration.appendRightVar base.val
          (base.val.wiresAt site) value) =
      env sig (Internal.embedOuterThroughSite visible outer same value) := by
  cases same
  rfl

private theorem relationJoin_castVisibleEnv_appendRight
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled)
    (env : Env pre compiled.frame.visible.sigs)
    {sig : Sig}
    (value : Var canonical.siteOuter.sigs sig) :
    (congrArg ConcreteElaboration.WireContext.sigs
          canonical.visibleExact ▸ env)
        sig
        (ConcreteElaboration.appendRightVar base.val
          (base.val.wiresAt site) value) =
      env sig (aboveScopeEmbedOuter canonical value) := by
  exact
    relationJoin_castVisibleEnv_appendRightRaw compiled.frame.visible
      canonical.siteOuter canonical.visibleExact env value

private theorem relationJoin_aligned_embedOuter
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (left right : SiteCompilation.AboveScopeDecomposition compiled)
    (aligned :
      SiteCompilation.AboveScopeDecomposition.Alignment left right)
    {sig : Sig}
    (value : Var left.siteOuter.sigs sig) :
    aboveScopeEmbedOuter left value =
      aboveScopeEmbedOuter right
        (congrArg ConcreteElaboration.WireContext.sigs
          aligned.siteOuterExact ▸ value) := by
  cases left with
  | mk leftOuter leftAbove leftVisible leftDecomposition =>
      cases right with
      | mk rightOuter rightAbove rightVisible rightDecomposition =>
          cases aligned with
          | mk outerExact aboveExact =>
              cases outerExact
              have proofExact : leftVisible = rightVisible :=
                Subsingleton.elim _ _
              cases proofExact
              rfl

private noncomputable def relationJoin_composeDeletion
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {bound : CheckedDiagram definitions}
    {removed : bound.val.WireId}
    {boundScope :
      SiteCompilation bound (bound.val.wires removed).scope}
    {targetWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound removed).WellFormed definitions}
    (first :
      RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
        sourceScope boundScope)
    (receipt :
      ExhaustedWireRemovalSemantics.FinalDeletionOuterReceipt.{u}
        bound removed targetWellFormed boundScope)
    (aligned :
      SiteCompilation.AboveScopeDecomposition.Alignment
        first.finalCanonical receipt.boundCanonical) :
    DiagramContext.ComposableSemanticZipper
      first.sourceCanonical.above receipt.reflected.targetAbove
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (ExhaustedWireRemovalSemantics.contextProjection bound removed
            (ConcreteElaboration.WireContext.empty
              (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                bound removed))
            (ConcreteElaboration.WireContext.empty bound.val)
            receipt.reflected.outerCorrespond
            receipt.reflected.outerRemovedAbsent))
      (fun (_pre : PreModel.{u}) env =>
        Env.comp
          ((congrArg ConcreteElaboration.WireContext.sigs
              aligned.siteOuterExact).symm ▸
            Env.comp env
              (ExhaustedWireRemovalSemantics.contextProjection
                bound removed receipt.reflected.targetSiteOuter
                receipt.reflected.sourceSiteOuter
                receipt.reflected.siteCorrespond
                receipt.reflected.siteRemovedAbsent))
          first.outerProjection) := by
  cases first with
  | mk sourceCanonical finalCanonical outerProjection scopeProjection
      firstComposable =>
      cases finalCanonical with
      | mk finalOuter finalAbove finalVisible finalDecomposition =>
          cases receipt with
          | mk plain reflected boundRootFill plainRootFill =>
              cases reflected with
              | mk outerCorrespond outerRemovedAbsent sourceOuter targetOuter
                  siteCorrespond siteRemovedAbsent sourceAbove targetAbove
                  sourceBody targetBody sourceVisible targetVisible
                  sourceNodup sourceBodyExact targetBodyExact
                  localBodyLaw sourceCutDepth sourceFill targetFill
                  sourceDecomposition composable =>
                    cases aligned with
                    | mk outerExact aboveExact =>
                        cases outerExact
                        cases aboveExact
                        exact
                          DiagramContext.ComposableSemanticZipper.compose
                            firstComposable composable

private theorem relationJoin_emptyEnv_unique
    {pre : PreModel.{u}}
    (env : Env pre []) :
    env = Env.empty := by
  funext sig value
  nomatch value

/--
The checked relation join denotes in the direction selected by the source
dying site's cut parity.  The replacement relation is evaluated at the final
retained parameter values.
-/
theorem _root_.VisualProof.ConcreteWireQuantifier.RelationJoinResult.denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (contentCompiled : OpenCompilation content)
    (sourceSite :
      SiteCompilation source (source.val.wires wire).scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (parameterScopes :
      ∀ position : Fin parameters.length,
        source.val.Encloses
          (source.val.wires (parameters.get position)).scope
          (source.val.wires wire).scope) :
    (sourceSite.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) ∧
    (sourceSite.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) := by
  have targetWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.boundFinal result.boundDying).WellFormed definitions := by
    rw [← result.final_deletion_exact]
    exact result.plainFinal.property
  let trace := result.semantic_trace
  obtain ⟨finalScope, aboveFold, sourceHead, finalHead,
      sourceParameters, finalParameters, sourceHeadOrigins,
      finalHeadOrigins, sourceParameterOrigins, finalParameterOrigins,
      projectionHead, projectionParameters, traceBodyLaw⟩ :=
    Internal.relationJoin_preBinderDenotation trace contentCompiled sourceSite model
      definitionEnv result.boundary_exact result.relation_signature
      (by rfl) parameterScopes
  obtain ⟨deletionReceipt⟩ :=
    ExhaustedWireRemovalSemantics.siteCompilation_reflect
      result.boundFinal result.boundDying targetWellFormed
      result.bound_dying_endpoints finalScope
  let alignment :=
    aboveFold.transport.finalCanonical.alignment
      deletionReceipt.boundCanonical
  let combined :=
    relationJoin_composeDeletion aboveFold.transport deletionReceipt
      alignment
  let sourceFinished :=
    ConcreteElaboration.finishRegion source.val
      aboveFold.transport.sourceCanonical.siteOuter
      (source.val.wires wire).scope
      (congrArg ConcreteElaboration.WireContext.sigs
        aboveFold.transport.sourceCanonical.visibleExact ▸
          sourceSite.frame.siteBody)
  let targetFinished :=
    ConcreteElaboration.finishRegion
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.boundFinal result.boundDying)
      deletionReceipt.reflected.targetSiteOuter
      (ExhaustedWireRemovalSemantics.targetRegion result.boundFinal
        result.boundDying
        (result.boundFinal.val.wires result.boundDying).scope)
      deletionReceipt.reflected.targetBody
  have composedParity :=
    combined.toSemanticZipper.targetToSource model.toPreModel definitionEnv
      sourceFinished targetFinished Env.empty (by
        intro targetOuterEnv _preservesOuter targetDenotes
        obtain ⟨targetValues, targetCore⟩ :=
          (ConcreteElaboration.denote_finishRegion definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              result.boundFinal result.boundDying)
            deletionReceipt.reflected.targetSiteOuter
            (ExhaustedWireRemovalSemantics.targetRegion result.boundFinal
              result.boundDying
              (result.boundFinal.val.wires result.boundDying).scope)
            model.toPreModel definitionEnv targetOuterEnv
            deletionReceipt.reflected.targetBody).mp targetDenotes
        let targetExtended :=
          ConcreteElaboration.extendEnvironment
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              result.boundFinal result.boundDying)
            deletionReceipt.reflected.targetSiteOuter
            (ExhaustedWireRemovalSemantics.targetRegion result.boundFinal
              result.boundDying
              (result.boundFinal.val.wires result.boundDying).scope)
            targetValues targetOuterEnv
        have finalHeadOrigin :
            ConcreteElaboration.WireContext.origin result.boundFinal.val
                finalScope.frame.visible.ids finalHead =
              result.boundDying := by
          change
            [ConcreteElaboration.WireContext.origin result.boundFinal.val
              finalScope.frame.visible.ids finalHead] =
                [result.boundDying] at finalHeadOrigins
          exact List.cons.inj finalHeadOrigins |>.1
        have finalDyingSignature :
            (result.boundFinal.val.wires result.boundDying).sig =
              .rel result.args := by
          rw [← finalHeadOrigin]
          exact
            ConcreteElaboration.WireContext.origin_signature
              result.boundFinal.val finalScope.frame.visible.ids finalHead
        obtain ⟨placeholder⟩ :=
          model.toPreModel.inhabited
            (result.boundFinal.val.wires result.boundDying).sig
        let extendedCorrespond :=
          ExhaustedWireRemovalSemantics.extend_contexts_correspond
            result.boundFinal result.boundDying
            deletionReceipt.reflected.siteCorrespond
            (result.boundFinal.val.wires result.boundDying).scope
        let visibleSigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            deletionReceipt.reflected.sourceVisibleExact
        let placeholderBoundEnv :=
          ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget
            result.boundFinal result.boundDying
            (deletionReceipt.reflected.targetSiteOuter.extend
              (ExhaustedWireRemovalSemantics.targetRegion result.boundFinal
                result.boundDying
                (result.boundFinal.val.wires result.boundDying).scope))
            (deletionReceipt.reflected.sourceSiteOuter.extend
              (result.boundFinal.val.wires result.boundDying).scope)
            extendedCorrespond model.toPreModel placeholder targetExtended
        let placeholderFrameEnv :
            Env model.toPreModel finalScope.frame.visible.sigs :=
          visibleSigs.symm ▸ placeholderBoundEnv
        let selectedRelation :=
          WireQuantifierSemantics.contentRelation model definitionEnv
            contentCompiled result.boundary_exact
            (Vars.denote placeholderFrameEnv finalParameters)
        let selected :
            model.toPreModel.Domain
              (result.boundFinal.val.wires result.boundDying).sig :=
          (congrArg model.toPreModel.Domain finalDyingSignature).symm ▸
            selectedRelation
        let selectedBoundEnv :=
          ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget
            result.boundFinal result.boundDying
            (deletionReceipt.reflected.targetSiteOuter.extend
              (ExhaustedWireRemovalSemantics.targetRegion result.boundFinal
                result.boundDying
                (result.boundFinal.val.wires result.boundDying).scope))
            (deletionReceipt.reflected.sourceSiteOuter.extend
              (result.boundFinal.val.wires result.boundDying).scope)
            extendedCorrespond model.toPreModel selected targetExtended
        let selectedFrameEnv :
            Env model.toPreModel finalScope.frame.visible.sigs :=
          visibleSigs.symm ▸ selectedBoundEnv
        have reflectedBody :=
          deletionReceipt.reflected.localBodyLaw model.toPreModel
            definitionEnv selected targetExtended targetCore
        have finalBody :
            denoteRegion model.toPreModel definitionEnv selectedFrameEnv
              finalScope.frame.siteBody := by
          have castedBody :
              denoteRegion model.toPreModel definitionEnv
                (visibleSigs ▸ selectedFrameEnv)
                (visibleSigs ▸ finalScope.frame.siteBody) := by
            rw [relationJoin_castEnvRoundtrip,
              deletionReceipt.reflected.sourceBodyExact]
            exact reflectedBody
          exact
            (relationJoin_denote_cast_context visibleSigs selectedFrameEnv
              finalScope.frame.siteBody).mp castedBody
        have finalHeadValue :
            selectedFrameEnv (.rel result.args) finalHead =
              selectedRelation := by
          simpa [selectedFrameEnv, selectedBoundEnv, selected] using
            (relationJoin_removedFrameValue result.boundFinal
              result.boundDying
              (deletionReceipt.reflected.targetSiteOuter.extend
                (ExhaustedWireRemovalSemantics.targetRegion
                  result.boundFinal result.boundDying
                  (result.boundFinal.val.wires
                    result.boundDying).scope))
              (deletionReceipt.reflected.sourceSiteOuter.extend
                (result.boundFinal.val.wires result.boundDying).scope)
              extendedCorrespond finalScope.frame.visible
              deletionReceipt.reflected.sourceVisibleExact
              finalDyingSignature model.toPreModel selectedRelation
              targetExtended finalHead finalHeadOrigin)
        let selectedCorrespond :=
          ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget_corresponds
              result.boundFinal
              result.boundDying
              (deletionReceipt.reflected.targetSiteOuter.extend
                (ExhaustedWireRemovalSemantics.targetRegion
                  result.boundFinal result.boundDying
                  (result.boundFinal.val.wires
                    result.boundDying).scope))
              (deletionReceipt.reflected.sourceSiteOuter.extend
                (result.boundFinal.val.wires result.boundDying).scope)
              extendedCorrespond
              deletionReceipt.reflected.sourceVisibleNodup
              model.toPreModel selected targetExtended
        let placeholderCorrespond :=
          ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget_corresponds
              result.boundFinal
              result.boundDying
              (deletionReceipt.reflected.targetSiteOuter.extend
                (ExhaustedWireRemovalSemantics.targetRegion
                  result.boundFinal result.boundDying
                  (result.boundFinal.val.wires
                    result.boundDying).scope))
              (deletionReceipt.reflected.sourceSiteOuter.extend
                (result.boundFinal.val.wires result.boundDying).scope)
              extendedCorrespond
              deletionReceipt.reflected.sourceVisibleNodup
              model.toPreModel placeholder targetExtended
        have finalParametersSurvive :
            ∀ mapped,
              mapped ∈
                  ConcreteElaboration.variableOrigins
                    result.boundFinal.val finalScope.frame.visible
                    finalParameters →
                mapped ≠ result.boundDying := by
          intro mapped member same
          rw [finalParameterOrigins] at member
          obtain ⟨parameter, parameterMember, mappedExact⟩ :=
            List.mem_map.mp member
          obtain ⟨position, rfl⟩ := List.get_of_mem parameterMember
          apply result.parameters_survive position
          apply result.boundWireImage_injective
          exact mappedExact.trans same
        have selectedPlaceholderAgree :
            ∀ {sig : Sig}
              (value : Var finalScope.frame.visible.sigs sig),
              ConcreteElaboration.WireContext.origin
                    result.boundFinal.val finalScope.frame.visible.ids
                    value ≠
                  result.boundDying →
                selectedFrameEnv sig value =
                  placeholderFrameEnv sig value := by
          intro sig value survives
          let extendedValue : Var
              (deletionReceipt.reflected.sourceSiteOuter.extend
                (result.boundFinal.val.wires
                  result.boundDying).scope).sigs sig :=
            visibleSigs ▸ value
          have extendedSurvives :
              ConcreteElaboration.WireContext.origin
                    result.boundFinal.val
                    (deletionReceipt.reflected.sourceSiteOuter.extend
                      (result.boundFinal.val.wires
                        result.boundDying).scope).ids
                    extendedValue ≠
                  result.boundDying := by
            intro removed
            apply survives
            exact
              (origin_cast_context result.boundFinal.val
                deletionReceipt.reflected.sourceVisibleExact value).symm.trans
                removed
          let targetValue :=
            ExhaustedWireRemovalSemantics.survivingProjection
              result.boundFinal result.boundDying
              (deletionReceipt.reflected.targetSiteOuter.extend
                (ExhaustedWireRemovalSemantics.targetRegion
                  result.boundFinal result.boundDying
                  (result.boundFinal.val.wires
                    result.boundDying).scope))
              (deletionReceipt.reflected.sourceSiteOuter.extend
                (result.boundFinal.val.wires result.boundDying).scope)
              extendedCorrespond extendedValue extendedSurvives
          have embedding :
              ExhaustedWireRemovalSemantics.contextEmbedding
                  result.boundFinal result.boundDying
                  (deletionReceipt.reflected.targetSiteOuter.extend
                    (ExhaustedWireRemovalSemantics.targetRegion
                      result.boundFinal result.boundDying
                      (result.boundFinal.val.wires
                        result.boundDying).scope))
                  (deletionReceipt.reflected.sourceSiteOuter.extend
                    (result.boundFinal.val.wires
                      result.boundDying).scope)
                  extendedCorrespond targetValue =
                extendedValue := by
            exact
              ExhaustedWireRemovalSemantics.contextEmbedding_survivingProjection
                  result.boundFinal
                  result.boundDying
                  (deletionReceipt.reflected.targetSiteOuter.extend
                    (ExhaustedWireRemovalSemantics.targetRegion
                      result.boundFinal result.boundDying
                      (result.boundFinal.val.wires
                        result.boundDying).scope))
                  (deletionReceipt.reflected.sourceSiteOuter.extend
                    (result.boundFinal.val.wires
                      result.boundDying).scope)
                  extendedCorrespond
                  deletionReceipt.reflected.sourceVisibleNodup extendedValue
                  extendedSurvives
          have selectedAtTarget :=
            congrFun (congrFun selectedCorrespond.surviving sig)
              targetValue
          have placeholderAtTarget :=
            congrFun (congrFun placeholderCorrespond.surviving sig)
              targetValue
          change
            selectedBoundEnv sig
                (ExhaustedWireRemovalSemantics.contextEmbedding
                  result.boundFinal result.boundDying
                  (deletionReceipt.reflected.targetSiteOuter.extend
                    (ExhaustedWireRemovalSemantics.targetRegion
                      result.boundFinal result.boundDying
                      (result.boundFinal.val.wires
                        result.boundDying).scope))
                  (deletionReceipt.reflected.sourceSiteOuter.extend
                    (result.boundFinal.val.wires
                      result.boundDying).scope)
                  extendedCorrespond targetValue) =
              targetExtended sig targetValue at selectedAtTarget
          change
            placeholderBoundEnv sig
                (ExhaustedWireRemovalSemantics.contextEmbedding
                  result.boundFinal result.boundDying
                  (deletionReceipt.reflected.targetSiteOuter.extend
                    (ExhaustedWireRemovalSemantics.targetRegion
                      result.boundFinal result.boundDying
                      (result.boundFinal.val.wires
                        result.boundDying).scope))
                  (deletionReceipt.reflected.sourceSiteOuter.extend
                    (result.boundFinal.val.wires
                      result.boundDying).scope)
                  extendedCorrespond targetValue) =
              targetExtended sig targetValue at placeholderAtTarget
          rw [embedding] at selectedAtTarget placeholderAtTarget
          change
            (visibleSigs.symm ▸ selectedBoundEnv) sig value =
              (visibleSigs.symm ▸ placeholderBoundEnv) sig value
          rw [relationJoin_castEnvBack_apply visibleSigs selectedBoundEnv
            value]
          rw [relationJoin_castEnvBack_apply visibleSigs
            placeholderBoundEnv value]
          exact selectedAtTarget.trans placeholderAtTarget.symm
        have parameterValues :
            Vars.denote selectedFrameEnv finalParameters =
              Vars.denote placeholderFrameEnv finalParameters := by
          exact
            Internal.vars_denote_eq_of_origins_ne result.boundFinal.val
              finalScope.frame.visible result.boundDying finalParameters
              selectedFrameEnv placeholderFrameEnv finalParametersSurvive
              selectedPlaceholderAgree
        have finalHeadLaw :
            selectedFrameEnv (.rel result.args) finalHead =
              WireQuantifierSemantics.contentRelation model definitionEnv
                contentCompiled result.boundary_exact
                (Vars.denote selectedFrameEnv finalParameters) := by
          rw [finalHeadValue, parameterValues]
        have sourceCore :=
          traceBodyLaw selectedFrameEnv finalHeadLaw finalBody
        have sourceSiteOuterNodup :
            deletionReceipt.reflected.sourceSiteOuter.ids.Nodup := by
          have parts := deletionReceipt.reflected.sourceVisibleNodup
          rw [ConcreteElaboration.WireContext.extend,
            List.nodup_append] at parts
          exact parts.2.1
        let deletionSiteProjection :
            WireRenaming deletionReceipt.reflected.sourceSiteOuter.sigs
              deletionReceipt.reflected.targetSiteOuter.sigs :=
          fun {_} value =>
            ExhaustedWireRemovalSemantics.contextProjection
              result.boundFinal result.boundDying
              deletionReceipt.reflected.targetSiteOuter
              deletionReceipt.reflected.sourceSiteOuter
              deletionReceipt.reflected.siteCorrespond
              deletionReceipt.reflected.siteRemovedAbsent value
        let boundOuterEnv :
            Env model.toPreModel
              deletionReceipt.reflected.sourceSiteOuter.sigs :=
          Env.comp targetOuterEnv deletionSiteProjection
        have boundOuterExact :
            ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget
                result.boundFinal result.boundDying
                deletionReceipt.reflected.targetSiteOuter
                deletionReceipt.reflected.sourceSiteOuter
                deletionReceipt.reflected.siteCorrespond model.toPreModel
                selected targetOuterEnv =
              boundOuterEnv := by
          exact
            ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget_eq_projection
                result.boundFinal result.boundDying
                deletionReceipt.reflected.targetSiteOuter
                deletionReceipt.reflected.sourceSiteOuter
                deletionReceipt.reflected.siteCorrespond
                sourceSiteOuterNodup
                deletionReceipt.reflected.siteRemovedAbsent
                model.toPreModel selected targetOuterEnv
        let boundValues :=
          ConcreteElaboration.valuesFromEnvironmentFor
            result.boundFinal.val
            deletionReceipt.reflected.sourceSiteOuter.ids
            (result.boundFinal.val.wiresAt
              (result.boundFinal.val.wires result.boundDying).scope)
            selectedBoundEnv
        have boundReconstructed :
            ConcreteElaboration.extendEnvironment result.boundFinal.val
                deletionReceipt.reflected.sourceSiteOuter
                (result.boundFinal.val.wires result.boundDying).scope
                boundValues boundOuterEnv =
              selectedBoundEnv := by
          have reconstructed :=
            ExhaustedWireRemovalSemantics.sourceEnvironmentFromTarget_extend_reconstruct
                result.boundFinal result.boundDying
                deletionReceipt.reflected.targetSiteOuter
                deletionReceipt.reflected.sourceSiteOuter
                deletionReceipt.reflected.siteCorrespond
                (result.boundFinal.val.wires result.boundDying).scope
                deletionReceipt.reflected.sourceVisibleNodup
                deletionReceipt.reflected.siteRemovedAbsent
                model.toPreModel selected targetValues targetOuterEnv
          rw [boundOuterExact] at reconstructed
          exact reconstructed
        have selectedFinalOuter :
            ∀ {sig : Sig}
              (value :
                Var deletionReceipt.reflected.sourceSiteOuter.sigs sig),
              selectedFrameEnv sig
                  (aboveScopeEmbedOuter deletionReceipt.boundCanonical
                    value) =
                boundOuterEnv sig value := by
          intro sig value
          rw [← relationJoin_castVisibleEnv_appendRight
            deletionReceipt.boundCanonical selectedFrameEnv value]
          change
            (visibleSigs ▸ (visibleSigs.symm ▸ selectedBoundEnv)) sig
                (ConcreteElaboration.appendRightVar result.boundFinal.val
                  (result.boundFinal.val.wiresAt
                    (result.boundFinal.val.wires
                      result.boundDying).scope) value) =
              boundOuterEnv sig value
          rw [relationJoin_castEnvRoundtrip]
          rw [← boundReconstructed]
          exact
            ConcreteElaboration.extendEnvironment_appendRightVar
              result.boundFinal.val
              deletionReceipt.reflected.sourceSiteOuter
              (result.boundFinal.val.wires result.boundDying).scope
              boundValues boundOuterEnv value
        let sourceVisibleSigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            aboveFold.transport.sourceCanonical.visibleExact
        let sourceVisibleEnv :=
          Env.comp selectedFrameEnv
            aboveFold.scopeProjection.visibleProjection
        let sourceExtendedEnv :
            Env model.toPreModel
              (aboveFold.transport.sourceCanonical.siteOuter.extend
                (source.val.wires wire).scope).sigs :=
          sourceVisibleSigs ▸ sourceVisibleEnv
        have sourceExtendedCore :
            denoteRegion model.toPreModel definitionEnv sourceExtendedEnv
              (sourceVisibleSigs ▸ sourceSite.frame.siteBody) := by
          exact
            (relationJoin_denote_cast_context sourceVisibleSigs
              sourceVisibleEnv sourceSite.frame.siteBody).mpr sourceCore
        let alignedBoundOuterEnv :
            Env model.toPreModel
              aboveFold.transport.finalCanonical.siteOuter.sigs :=
          (congrArg ConcreteElaboration.WireContext.sigs
            alignment.siteOuterExact).symm ▸ boundOuterEnv
        let sourceOuterEnv :
            Env model.toPreModel
              aboveFold.transport.sourceCanonical.siteOuter.sigs :=
          Env.comp alignedBoundOuterEnv aboveFold.transport.outerProjection
        let sourceValues :=
          ConcreteElaboration.valuesFromEnvironmentFor source.val
            aboveFold.transport.sourceCanonical.siteOuter.ids
            (source.val.wiresAt (source.val.wires wire).scope)
            sourceExtendedEnv
        have sourceReconstructed :
            ConcreteElaboration.extendEnvironment source.val
                aboveFold.transport.sourceCanonical.siteOuter
                (source.val.wires wire).scope sourceValues sourceOuterEnv =
              sourceExtendedEnv := by
          apply ConcreteElaboration.extendEnvironmentFor_from
          intro sig value
          change
            (sourceVisibleSigs ▸ sourceVisibleEnv) sig
                (ConcreteElaboration.appendRightVar source.val
                  (source.val.wiresAt
                    (source.val.wires wire).scope) value) =
              sourceOuterEnv sig value
          rw [relationJoin_castVisibleEnv_appendRight
            aboveFold.transport.sourceCanonical sourceVisibleEnv value]
          change
            selectedFrameEnv sig
                (aboveFold.scopeProjection.visibleProjection
                  (aboveScopeEmbedOuter
                    aboveFold.transport.sourceCanonical value)) =
              sourceOuterEnv sig value
          rw [aboveFold.scopeProjection.visibleExtendsOuter]
          rw [relationJoin_aligned_embedOuter
            aboveFold.transport.finalCanonical
            deletionReceipt.boundCanonical alignment]
          rw [selectedFinalOuter]
          change
            boundOuterEnv sig
                (congrArg ConcreteElaboration.WireContext.sigs
                  alignment.siteOuterExact ▸
                    aboveFold.transport.outerProjection value) =
              ((congrArg ConcreteElaboration.WireContext.sigs
                  alignment.siteOuterExact).symm ▸ boundOuterEnv)
                sig (aboveFold.transport.outerProjection value)
          exact
            (relationJoin_castEnvBack_apply
              (congrArg ConcreteElaboration.WireContext.sigs
                alignment.siteOuterExact)
              boundOuterEnv
              (aboveFold.transport.outerProjection value)).symm
        change
          denoteRegion model.toPreModel definitionEnv sourceOuterEnv
            sourceFinished
        apply
          (ConcreteElaboration.denote_finishRegion definitions source.val
            aboveFold.transport.sourceCanonical.siteOuter
            (source.val.wires wire).scope model.toPreModel definitionEnv
            sourceOuterEnv
            (sourceVisibleSigs ▸ sourceSite.frame.siteBody)).mpr
        refine ⟨sourceValues, ?_⟩
        rw [sourceReconstructed]
        exact sourceExtendedCore)
  have sourceCutDepth :=
    relationJoin_aboveScope_cutDepth_eq
      aboveFold.transport.sourceCanonical
  have sourceRoot :
      aboveFold.transport.sourceCanonical.above.fill sourceFinished =
        sourceSite.checked := by
    rw [← relationJoin_aboveScope_fill_finishRegion
      aboveFold.transport.sourceCanonical]
    exact sourceSite.frame_fills_checked
  have targetRoot :
      deletionReceipt.reflected.targetAbove.fill targetFinished =
        deletionReceipt.plain.checked := by
    exact deletionReceipt.plainRootFill.symm
  have deletedExact :
      ExhaustedWireRemovalSemantics.deletedCheckedDiagram
          result.boundFinal result.boundDying targetWellFormed =
        result.plainFinal := by
    apply Subtype.ext
    exact result.final_deletion_exact.symm
  obtain ⟨_steps, _trace, _applications, targetPlain⟩ :=
    result.trace_denotes model.toPreModel definitionEnv
  constructor
  · intro even targetDenotes
    have plainDenotes :
        denoteChecked model.toPreModel definitionEnv result.plainFinal :=
      targetPlain.mp targetDenotes
    have targetRegion :
        denoteRegion model.toPreModel definitionEnv Env.empty
          deletionReceipt.plain.checked := by
      change
        denoteRegion model.toPreModel definitionEnv Env.empty
          (elaborate
            (ExhaustedWireRemovalSemantics.deletedCheckedDiagram
              result.boundFinal result.boundDying targetWellFormed))
      rw [deletedExact, ← elaborate_denotes_checked]
      exact plainDenotes
    have targetFilled :
        denoteRegion model.toPreModel definitionEnv Env.empty
          (deletionReceipt.reflected.targetAbove.fill targetFinished) := by
      rw [targetRoot]
      exact targetRegion
    have evenAbove :
        aboveFold.transport.sourceCanonical.above.cutDepth % 2 = 0 := by
      rw [← sourceCutDepth]
      exact even
    have sourceFilled := composedParity.1 evenAbove targetFilled
    have sourceFilledEmpty :
        denoteRegion model.toPreModel definitionEnv Env.empty
          sourceSite.checked := by
      rw [sourceRoot] at sourceFilled
      simpa only [relationJoin_emptyEnv_unique] using sourceFilled
    rw [elaborate_denotes_checked]
    exact sourceFilledEmpty
  · intro odd sourceDenotes
    have sourceRegion :
        denoteRegion model.toPreModel definitionEnv Env.empty
          sourceSite.checked := by
      rw [elaborate_denotes_checked] at sourceDenotes
      exact sourceDenotes
    have sourceFilled :
        denoteRegion model.toPreModel definitionEnv
          (Env.comp Env.empty
            (ExhaustedWireRemovalSemantics.contextProjection
              result.boundFinal result.boundDying
              (ConcreteElaboration.WireContext.empty
                (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                  result.boundFinal result.boundDying))
              (ConcreteElaboration.WireContext.empty result.boundFinal.val)
              deletionReceipt.reflected.outerCorrespond
              deletionReceipt.reflected.outerRemovedAbsent))
          (aboveFold.transport.sourceCanonical.above.fill
            sourceFinished) := by
      rw [sourceRoot]
      simpa only [relationJoin_emptyEnv_unique] using sourceRegion
    have oddAbove :
        aboveFold.transport.sourceCanonical.above.cutDepth % 2 = 1 := by
      rw [← sourceCutDepth]
      exact odd
    have targetFilled := composedParity.2 oddAbove sourceFilled
    rw [targetRoot] at targetFilled
    have plainDenotes :
        denoteChecked model.toPreModel definitionEnv result.plainFinal := by
      rw [elaborate_denotes_checked]
      change
        denoteRegion model.toPreModel definitionEnv Env.empty
          (elaborate result.plainFinal)
      rw [← deletedExact]
      exact targetFilled
    exact targetPlain.mpr plainDenotes


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
