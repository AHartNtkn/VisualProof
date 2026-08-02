import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinStepSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

private theorem spliceRaw_succeeds_of_wellFormed
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wellFormed : attachment.diagram.WellFormed definitions) :
    ∃ result, spliceRaw attachment = .ok result := by
  unfold spliceRaw
  split
  · rename_i error rejected
    have complete :=
      ConcreteDiagram.checkWellFormed_complete wellFormed
    rw [rejected] at complete
    contradiction
  · exact ⟨_, rfl⟩

namespace RelationJoinStep

/--
Recover the unique structural insertion receipt owned by one accepted
relation-join step. This is the sole compilation-recovery authority for both
one-step and trace semantics.
-/
theorem insertionCompilation
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content) :
    ∃ compiled :
        InsertionCompilation contentCompiled step.attachment,
      compileInsertion? contentCompiled step.attachment = some compiled := by
  have generatedWellFormed :
      step.attachment.diagram.WellFormed definitions := by
    rw [← step.checked_generated]
    exact step.checked.property
  obtain ⟨spliceResult, spliceAccepted⟩ :=
    spliceRaw_succeeds_of_wellFormed step.attachment generatedWellFormed
  exact
    compileInsertion_complete_of_raw_splice contentCompiled step.attachment
      spliceResult spliceAccepted

end RelationJoinStep

namespace RelationJoinSemantics

open Internal

def RelationJoinSemanticTrace.ScopeProjection.identity
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    RelationJoinSemanticTrace.ScopeProjection canonical canonical
      (fun {_} value => value) where
  visibleProjection := fun {_} value => value
  visibleExtendsOuter := fun _value => rfl

def RelationJoinSemanticTrace.ScopeProjection.compose
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {middle : CheckedDiagram definitions}
    {middleSite : middle.val.RegionId}
    {middleScope : SiteCompilation middle middleSite}
    {target : CheckedDiagram definitions}
    {targetSite : target.val.RegionId}
    {targetScope : SiteCompilation target targetSite}
    {sourceCanonical :
      SiteCompilation.AboveScopeDecomposition sourceScope}
    {middleCanonical :
      SiteCompilation.AboveScopeDecomposition middleScope}
    {targetCanonical :
      SiteCompilation.AboveScopeDecomposition targetScope}
    {firstOuter :
      WireRenaming sourceCanonical.siteOuter.sigs
        middleCanonical.siteOuter.sigs}
    {secondOuter :
      WireRenaming middleCanonical.siteOuter.sigs
        targetCanonical.siteOuter.sigs}
    (first :
      RelationJoinSemanticTrace.ScopeProjection
        sourceCanonical middleCanonical firstOuter)
    (second :
      RelationJoinSemanticTrace.ScopeProjection
        middleCanonical targetCanonical secondOuter) :
    RelationJoinSemanticTrace.ScopeProjection
      sourceCanonical targetCanonical
      (fun {_} value => secondOuter (firstOuter value)) where
  visibleProjection :=
    fun {_} value =>
      second.visibleProjection (first.visibleProjection value)
  visibleExtendsOuter := by
    intro sig value
    rw [first.visibleExtendsOuter, second.visibleExtendsOuter]

private theorem vars_rename_identity
    (variables : Vars context args) :
    Vars.rename (fun {_} value => value) variables = variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      change
        Vars.cons head
            (Vars.rename (fun {_} value => value) tail) =
          Vars.cons head tail
      rw [induction]

private theorem vars_rename_compose
    (first : WireRenaming sourceContext middleContext)
    (second : WireRenaming middleContext targetContext)
    (variables : Vars sourceContext args) :
    Vars.rename second (Vars.rename first variables) =
      Vars.rename (fun {_} value => second (first value)) variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      change
        Vars.cons (second (first head))
            (Vars.rename second (Vars.rename first tail)) =
          Vars.cons (second (first head))
            (Vars.rename (fun {_} value => second (first value)) tail)
      rw [induction]

theorem Internal.vars_denote_eq_of_origins_ne
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (removed : diagram.WireId)
    (variables : Vars context.sigs args)
    (left right : Env pre context.sigs)
    (survives :
      ∀ wire,
        wire ∈ ConcreteElaboration.variableOrigins diagram context
          variables →
        wire ≠ removed)
    (agree :
      ∀ {sig : Sig} (value : Var context.sigs sig),
        ConcreteElaboration.WireContext.origin diagram context.ids value ≠
            removed →
          left sig value = right sig value) :
    Vars.denote left variables = Vars.denote right variables := by
  induction variables with
  | nil => rfl
  | @cons sig rest head tail induction =>
      simp only [ConcreteElaboration.variableOrigins, List.mem_cons] at survives
      simp only [Vars.denote_cons]
      rw [agree head
        (survives
          (ConcreteElaboration.WireContext.origin diagram context.ids head)
          (by simp))]
      exact congrArg (fun value => (_, value))
        (induction (fun wire member => survives wire (by simp [member])))

/-- The trace scope is exactly the final image of the dying wire's scope. -/
theorem RelationJoinSemanticTrace.finalDyingScope
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope) :
    (final.val.wires finalDying).scope = finalScope := by
  induction trace with
  | nil => rfl
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      exact step.checked_dying_scope

/-- The canonical endpoints, projection, and structural derivation of a fold. -/
structure RelationJoinSemanticTrace.AboveDyingScopeTransport
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    (sourceScope : SiteCompilation source sourceSite)
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    (finalScope : SiteCompilation final finalSite) : Type (u + 1) where
  sourceCanonical :
    SiteCompilation.AboveScopeDecomposition sourceScope
  finalCanonical :
    SiteCompilation.AboveScopeDecomposition finalScope
  outerProjection :
    WireRenaming sourceCanonical.siteOuter.sigs
      finalCanonical.siteOuter.sigs
  scopeProjection :
    RelationJoinSemanticTrace.ScopeProjection
      sourceCanonical finalCanonical outerProjection
  composable :
    DiagramContext.ComposableSemanticZipper
      sourceCanonical.above finalCanonical.above
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env outerProjection)

/--
The structural part of the sole relation trace. Nil is an indexed identity;
every nonempty trace carries one constructor-preserving source-to-final
derivation between canonical above-scope decompositions.
-/
inductive RelationJoinSemanticTrace.AboveDyingScopeFold
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    (sourceScope : SiteCompilation source sourceSite) :
    {final : CheckedDiagram definitions} →
    {finalSite : final.val.RegionId} →
    SiteCompilation final finalSite →
    Type (u + 1)
  | identity
      {final : CheckedDiagram definitions}
      {finalSite : final.val.RegionId}
      (finalScope : SiteCompilation final finalSite)
      (same : HEq finalScope sourceScope) :
      (transport :
        RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
          sourceScope finalScope) →
      AboveDyingScopeFold sourceScope finalScope
  | nonempty
      {final : CheckedDiagram definitions}
      {finalSite : final.val.RegionId}
      {finalScope : SiteCompilation final finalSite}
      (transport :
        RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
          sourceScope finalScope) :
      AboveDyingScopeFold sourceScope finalScope

def RelationJoinSemanticTrace.AboveDyingScopeFold.transport
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope finalScope) :
    RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
      sourceScope finalScope :=
  match fold with
  | .identity _ _ transport => transport
  | .nonempty transport => transport

def RelationJoinSemanticTrace.AboveDyingScopeFold.scopeProjection
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope finalScope) :
    RelationJoinSemanticTrace.ScopeProjection
      fold.transport.sourceCanonical fold.transport.finalCanonical
      fold.transport.outerProjection :=
  fold.transport.scopeProjection

private noncomputable def
    RelationJoinSemanticTrace.AboveDyingScopeTransport.compose
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {middle : CheckedDiagram definitions}
    {middleSite : middle.val.RegionId}
    {middleScope : SiteCompilation middle middleSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (first :
      RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
        sourceScope middleScope)
    (nextCanonical :
      SiteCompilation.AboveScopeDecomposition middleScope)
    (finalCanonical :
      SiteCompilation.AboveScopeDecomposition finalScope)
    (nextOuterProjection :
      WireRenaming nextCanonical.siteOuter.sigs
        finalCanonical.siteOuter.sigs)
    (nextProjection :
      RelationJoinSemanticTrace.ScopeProjection
        nextCanonical finalCanonical nextOuterProjection)
    (nextComposable :
      DiagramContext.ComposableSemanticZipper
        nextCanonical.above finalCanonical.above
        (fun (_pre : PreModel.{u}) env => env)
        (fun (_pre : PreModel.{u}) env =>
          Env.comp env nextOuterProjection))
    (aligned :
      SiteCompilation.AboveScopeDecomposition.Alignment
        first.finalCanonical nextCanonical) :
    RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
      sourceScope finalScope := by
  cases first with
  | mk sourceCanonical middleCanonical firstOuterProjection firstProjection
      firstComposable =>
    cases middleCanonical with
  | mk middleOuter middleAbove middleVisible middleDecomposition =>
      cases nextCanonical with
      | mk nextOuter nextAbove nextVisible nextDecomposition =>
          cases aligned with
          | mk outerExact aboveExact =>
              cases outerExact
              cases aboveExact
              let scopeProjection :=
                firstProjection.compose nextProjection
              exact
                {
                  sourceCanonical := sourceCanonical
                  finalCanonical := finalCanonical
                  outerProjection :=
                    fun {_} value =>
                      nextOuterProjection (firstOuterProjection value)
                  scopeProjection := scopeProjection
                  composable :=
                    DiagramContext.ComposableSemanticZipper.compose
                      firstComposable nextComposable
                }

private theorem
    RelationJoinSemanticTrace.AboveDyingScopeTransport.compose_visibleProjection
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {middle : CheckedDiagram definitions}
    {middleSite : middle.val.RegionId}
    {middleScope : SiteCompilation middle middleSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (first :
      RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
        sourceScope middleScope)
    (nextCanonical :
      SiteCompilation.AboveScopeDecomposition middleScope)
    (finalCanonical :
      SiteCompilation.AboveScopeDecomposition finalScope)
    (nextOuterProjection :
      WireRenaming nextCanonical.siteOuter.sigs
        finalCanonical.siteOuter.sigs)
    (nextProjection :
      RelationJoinSemanticTrace.ScopeProjection
        nextCanonical finalCanonical nextOuterProjection)
    (nextComposable :
      DiagramContext.ComposableSemanticZipper
        nextCanonical.above finalCanonical.above
        (fun (_pre : PreModel.{u}) env => env)
        (fun (_pre : PreModel.{u}) env =>
          Env.comp env nextOuterProjection))
    (aligned :
      SiteCompilation.AboveScopeDecomposition.Alignment
        first.finalCanonical nextCanonical)
    {sig : Sig}
    (value : Var sourceScope.frame.visible.sigs sig) :
    (first.compose nextCanonical finalCanonical nextOuterProjection
        nextProjection nextComposable aligned).scopeProjection.visibleProjection
          value =
      nextProjection.visibleProjection
        (first.scopeProjection.visibleProjection value) := by
  cases first with
  | mk sourceCanonical middleCanonical firstOuterProjection firstProjection
      firstComposable =>
    cases middleCanonical with
    | mk middleOuter middleAbove middleVisible middleDecomposition =>
      cases nextCanonical with
      | mk nextOuter nextAbove nextVisible nextDecomposition =>
          cases aligned with
          | mk outerExact aboveExact =>
              cases outerExact
              cases aboveExact
              rfl

noncomputable def RelationJoinSemanticTrace.AboveDyingScopeFold.snoc
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {sourceScope :
      SiteCompilation source (source.val.wires dying).scope}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope priorScope)
    (stepReceipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope)
    (stepProjection :
      RelationJoinSemanticTrace.ScopeProjection
        stepReceipt.priorCanonical stepReceipt.checkedCanonical
        stepReceipt.siteProjection) :
    RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
      sourceScope checkedScope := by
  exact
    .nonempty
      (fold.transport.compose stepReceipt.priorCanonical
        stepReceipt.checkedCanonical stepReceipt.siteProjection
        stepProjection stepReceipt.composable
        (fold.transport.finalCanonical.alignment
          stepReceipt.priorCanonical))

theorem RelationJoinSemanticTrace.AboveDyingScopeFold.snoc_visibleProjection
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {sourceScope :
      SiteCompilation source (source.val.wires dying).scope}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope priorScope)
    (stepReceipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope)
    (stepProjection :
      RelationJoinSemanticTrace.ScopeProjection
        stepReceipt.priorCanonical stepReceipt.checkedCanonical
        stepReceipt.siteProjection)
    {sig : Sig}
    (value : Var sourceScope.frame.visible.sigs sig) :
    (fold.snoc stepReceipt stepProjection).scopeProjection.visibleProjection
        value =
      stepProjection.visibleProjection
        (fold.scopeProjection.visibleProjection value) := by
  unfold RelationJoinSemanticTrace.AboveDyingScopeFold.snoc
    RelationJoinSemanticTrace.AboveDyingScopeFold.scopeProjection
    RelationJoinSemanticTrace.AboveDyingScopeFold.transport
  exact
    fold.transport.compose_visibleProjection stepReceipt.priorCanonical
      stepReceipt.checkedCanonical stepReceipt.siteProjection
      stepProjection stepReceipt.composable
      (fold.transport.finalCanonical.alignment
        stepReceipt.priorCanonical) value

/--
Fold the sole accepted relation-join trace at the dying scope before its
binders close. Every step uses the same semantic content relation and the same
ordered parameter tuple.
-/
theorem RelationJoinSemanticTrace.preBinderDenotationAtTraceScope
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {parameterSigs : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope)
    (contentCompiled : OpenCompilation content)
    (sourceScope :
      SiteCompilation source (source.val.wires dying).scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (boundaryExact :
      checkedBoundarySigs content =
        args ++ parameterSigs)
    (relationSignature :
      (source.val.wires dying).sig = .rel args)
    (parameterSignatureExact :
      parameters.map (fun wire => (source.val.wires wire).sig) =
        parameterSigs)
    (parameterScopes :
      ∀ position : Fin parameters.length,
        source.val.Encloses
          (source.val.wires (parameters.get position)).scope
          (source.val.wires dying).scope) :
    ∃ (finalScopeCompiled :
        SiteCompilation final finalScope)
      (aboveFold :
        RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
          sourceScope finalScopeCompiled)
      (sourceHead :
        Var sourceScope.frame.visible.sigs (.rel args))
      (finalHead :
        Var finalScopeCompiled.frame.visible.sigs (.rel args))
      (sourceParameters :
        Vars sourceScope.frame.visible.sigs
          parameterSigs)
      (finalParameters :
        Vars finalScopeCompiled.frame.visible.sigs
          parameterSigs),
      ConcreteElaboration.variableOrigins source.val
          sourceScope.frame.visible (.cons sourceHead .nil) =
        [dying] ∧
      ConcreteElaboration.variableOrigins final.val
          finalScopeCompiled.frame.visible (.cons finalHead .nil) =
        [finalDying] ∧
      ConcreteElaboration.variableOrigins source.val
          sourceScope.frame.visible sourceParameters =
        parameters ∧
      ConcreteElaboration.variableOrigins final.val
          finalScopeCompiled.frame.visible finalParameters =
        parameters.map finalWireImage ∧
      aboveFold.scopeProjection.visibleProjection
          (sig := .rel args) sourceHead =
        finalHead ∧
      Vars.rename aboveFold.scopeProjection.visibleProjection
          sourceParameters =
        finalParameters ∧
      ∀ finalEnv :
          Env model.toPreModel finalScopeCompiled.frame.visible.sigs,
        finalEnv (.rel args) finalHead =
            WireQuantifierSemantics.contentRelation model definitionEnv
              contentCompiled boundaryExact
                (Vars.denote finalEnv finalParameters) →
          denoteRegion model.toPreModel definitionEnv finalEnv
              finalScopeCompiled.frame.siteBody →
            denoteRegion model.toPreModel definitionEnv
              (Env.comp finalEnv
                aboveFold.scopeProjection.visibleProjection)
              sourceScope.frame.siteBody := by
  induction trace with
  | nil =>
      have headMember :
          dying ∈ sourceScope.frame.visible.ids :=
        sourceScope.visible_of_encloses dying
          (source.val.encloses_refl _)
      let sourceHead :
          Var sourceScope.frame.visible.sigs (.rel args) :=
        InsertionCompilation.NaturalityInternal.castVar relationSignature
          (variableOfMember source.val sourceScope.frame.visible.ids dying
            headMember)
      have sourceHeadOrigin :
          ConcreteElaboration.variableOrigins source.val
              sourceScope.frame.visible (.cons sourceHead .nil) =
            [dying] := by
        change
          [ConcreteElaboration.WireContext.origin source.val
            sourceScope.frame.visible.ids sourceHead] =
          [dying]
        congr 1
        unfold sourceHead
        exact
          (InsertionCompilation.NaturalityInternal.origin_castVar
            source.val sourceScope.frame.visible.ids relationSignature
            (variableOfMember source.val sourceScope.frame.visible.ids dying
              headMember)).trans
            (variableOfMember_origin source.val
              sourceScope.frame.visible.ids dying headMember)
      have parameterMembers :
          ∀ wire, wire ∈ parameters →
            wire ∈ sourceScope.frame.visible.ids := by
        intro wire member
        obtain ⟨position, rfl⟩ := List.get_of_mem member
        apply sourceScope.visible_of_encloses
        exact parameterScopes position
      let nativeParameters :=
        variablesOfMembers source.val sourceScope.frame.visible
          parameters parameterMembers
      let sourceParameters :
          Vars sourceScope.frame.visible.sigs
            parameterSigs :=
        parameterSignatureExact ▸ nativeParameters
      have sourceParameterOrigins :
          ConcreteElaboration.variableOrigins source.val
              sourceScope.frame.visible sourceParameters =
            parameters := by
        unfold sourceParameters
        rw [variableOrigins_cast]
        exact
          variablesOfMembers_origins source.val sourceScope.frame.visible
            parameters parameterMembers
      obtain ⟨sourceCanonical⟩ :=
        sourceScope.aboveScopeDecomposition
      let identityTransport :
          RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
            sourceScope sourceScope :=
        {
          sourceCanonical := sourceCanonical
          finalCanonical := sourceCanonical
          outerProjection := fun {_} value => value
          scopeProjection :=
            RelationJoinSemanticTrace.ScopeProjection.identity
              sourceCanonical
          composable :=
            DiagramContext.ComposableSemanticZipper.identity
              sourceCanonical.above
        }
      let aboveFold :
          RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
            sourceScope sourceScope :=
        .identity sourceScope HEq.rfl identityTransport
      have projectionParameters :
          Vars.rename aboveFold.scopeProjection.visibleProjection
              sourceParameters =
            sourceParameters := by
        change
          Vars.rename (fun {_} value => value) sourceParameters =
            sourceParameters
        simpa only using
          vars_rename_identity sourceParameters
      refine
        ⟨sourceScope, aboveFold, sourceHead, sourceHead,
          sourceParameters, sourceParameters, sourceHeadOrigin,
          sourceHeadOrigin, sourceParameterOrigins, ?_, ?_,
          projectionParameters, ?_⟩
      · simpa using sourceParameterOrigins
      · rfl
      · intro finalEnv _headValue finalHolds
        change
          denoteRegion model.toPreModel definitionEnv
              (Env.comp finalEnv (fun {_} value => value))
              sourceScope.frame.siteBody
        simpa [Env.comp] using finalHolds
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      cases priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      obtain ⟨priorCanonicalScope, priorAboveFold,
          sourceHead, priorCanonicalHead, sourceParameters,
          priorCanonicalParameters, sourceHeadOrigin,
          priorCanonicalHeadOrigin, sourceParameterOrigins,
          priorCanonicalParameterOrigins, priorHeadExact,
          priorParametersExact, priorLaw⟩ :=
        induction
      obtain ⟨compiled, _compiledGenerated⟩ :=
        step.insertionCompilation contentCompiled
      obtain ⟨priorStepScope, checkedScope, stepAboveReceipt,
          stepScopeProjection,
          priorStepHead, checkedHead, priorStepParameters,
          checkedParameters, priorStepHeadOrigin, checkedHeadOrigin,
          priorStepParameterOrigins, checkedParameterOrigins,
          stepHeadExact, stepParametersExact, stepLaw⟩ :=
      Internal.RelationJoinStep.preBinderDenotation step contentCompiled compiled
          model definitionEnv boundaryExact parameterScopes
      have priorScopeExact :
          priorCanonicalScope = priorStepScope :=
        SiteCompilation.unique priorCanonicalScope priorStepScope
      cases priorScopeExact
      let finalAboveFold :=
        priorAboveFold.snoc stepAboveReceipt stepScopeProjection
      have priorHeadsExact :
          priorCanonicalHead = priorStepHead := by
        apply
          InsertionCompilation.NaturalityInternal.origin_injective
            step.prior.val priorCanonicalScope.frame.visible.ids
        · exact siteCompilation_visible_nodup priorCanonicalScope
        · exact
            (List.cons.inj priorCanonicalHeadOrigin).1.trans
              (List.cons.inj priorStepHeadOrigin).1.symm
      have priorParameterVariablesExact :
          priorCanonicalParameters = priorStepParameters := by
        apply
          variables_eq_of_origins step.prior.val
            priorCanonicalScope.frame.visible
            (siteCompilation_visible_nodup priorCanonicalScope)
        exact
          priorCanonicalParameterOrigins.trans
            priorStepParameterOrigins.symm
      have finalProjectionExact :
          ∀ {sig : Sig}
            (value : Var sourceScope.frame.visible.sigs sig),
            finalAboveFold.scopeProjection.visibleProjection value =
              stepScopeProjection.visibleProjection
                (priorAboveFold.scopeProjection.visibleProjection value) := by
        intro sig value
        exact
          priorAboveFold.snoc_visibleProjection stepAboveReceipt
            stepScopeProjection value
      have finalProjectionRenamingExact :
          (fun {sig : Sig}
              (value : Var sourceScope.frame.visible.sigs sig) =>
            finalAboveFold.scopeProjection.visibleProjection value :
            WireRenaming sourceScope.frame.visible.sigs
              checkedScope.frame.visible.sigs) =
            (fun {sig : Sig}
                (value : Var sourceScope.frame.visible.sigs sig) =>
              stepScopeProjection.visibleProjection
                (priorAboveFold.scopeProjection.visibleProjection value) :
              WireRenaming sourceScope.frame.visible.sigs
                checkedScope.frame.visible.sigs) := by
        funext sig value
        exact finalProjectionExact value
      have projectionHeadExact :
          finalAboveFold.scopeProjection.visibleProjection sourceHead =
            checkedHead := by
        rw [finalProjectionExact]
        rw [priorHeadExact, priorHeadsExact, stepHeadExact]
      have projectionParametersExact :
          Vars.rename finalAboveFold.scopeProjection.visibleProjection
              sourceParameters =
            checkedParameters := by
        change
          Vars.rename
              (fun {sig : Sig}
                (value : Var sourceScope.frame.visible.sigs sig) =>
                  finalAboveFold.scopeProjection.visibleProjection value)
              sourceParameters =
            checkedParameters
        rw [finalProjectionRenamingExact]
        rw [← stepParametersExact, ← priorParameterVariablesExact,
          ← priorParametersExact]
        exact
          (vars_rename_compose
            priorAboveFold.scopeProjection.visibleProjection
            stepScopeProjection.visibleProjection sourceParameters).symm
      refine
        ⟨checkedScope, finalAboveFold, sourceHead, checkedHead,
          sourceParameters, checkedParameters, sourceHeadOrigin,
          checkedHeadOrigin, sourceParameterOrigins,
          checkedParameterOrigins, projectionHeadExact,
          projectionParametersExact, ?_⟩
      intro checkedEnv checkedHeadValue checkedBody
      have priorParameterValuesExact :
          Vars.denote
              (Env.comp checkedEnv
                stepScopeProjection.visibleProjection)
              priorCanonicalParameters =
            Vars.denote checkedEnv checkedParameters := by
        rw [← Vars.denote_rename, priorParameterVariablesExact,
          stepParametersExact]
      have priorHeadValue :
          (Env.comp checkedEnv stepScopeProjection.visibleProjection)
              (.rel step.relationArgs)
              priorCanonicalHead =
            WireQuantifierSemantics.contentRelation model definitionEnv
              contentCompiled boundaryExact
                (Vars.denote
                  (Env.comp checkedEnv
                    stepScopeProjection.visibleProjection)
                  priorCanonicalParameters) := by
        rw [priorParameterValuesExact]
        change
          checkedEnv (.rel step.relationArgs)
              (stepScopeProjection.visibleProjection
                priorCanonicalHead) =
            WireQuantifierSemantics.contentRelation model definitionEnv
              contentCompiled boundaryExact
                (Vars.denote checkedEnv checkedParameters)
        rw [priorHeadsExact, stepHeadExact]
        exact checkedHeadValue
      have priorBody :
          denoteRegion model.toPreModel definitionEnv
              (Env.comp checkedEnv
                stepScopeProjection.visibleProjection)
              priorCanonicalScope.frame.siteBody :=
        stepLaw checkedEnv checkedHeadValue checkedBody
      have sourceBody :=
        priorLaw
          (Env.comp checkedEnv
            stepScopeProjection.visibleProjection) priorHeadValue
          priorBody
      change
        denoteRegion model.toPreModel definitionEnv
          (Env.comp checkedEnv
            (fun {sig : Sig}
              (value : Var sourceScope.frame.visible.sigs sig) =>
                finalAboveFold.scopeProjection.visibleProjection value))
          sourceScope.frame.siteBody
      rw [finalProjectionRenamingExact]
      simpa [Env.comp] using sourceBody

/--
Expose the folded trace at the canonical final dying-wire scope, eliminating
the parallel mapped-scope index before deletion composes with the trace.
-/
theorem Internal.relationJoin_preBinderDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args parameterSigs : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope)
    (contentCompiled : OpenCompilation content)
    (sourceScope :
      SiteCompilation source (source.val.wires dying).scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (relationSignature :
      (source.val.wires dying).sig = .rel args)
    (parameterSignatureExact :
      parameters.map (fun wire => (source.val.wires wire).sig) =
        parameterSigs)
    (parameterScopes :
      ∀ position : Fin parameters.length,
        source.val.Encloses
          (source.val.wires (parameters.get position)).scope
          (source.val.wires dying).scope) :
    ∃ (finalScopeCompiled :
        SiteCompilation final (final.val.wires finalDying).scope)
      (aboveFold :
        RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
          sourceScope finalScopeCompiled)
      (sourceHead :
        Var sourceScope.frame.visible.sigs (.rel args))
      (finalHead :
        Var finalScopeCompiled.frame.visible.sigs (.rel args))
      (sourceParameters :
        Vars sourceScope.frame.visible.sigs parameterSigs)
      (finalParameters :
        Vars finalScopeCompiled.frame.visible.sigs parameterSigs),
      ConcreteElaboration.variableOrigins source.val
          sourceScope.frame.visible (.cons sourceHead .nil) =
        [dying] ∧
      ConcreteElaboration.variableOrigins final.val
          finalScopeCompiled.frame.visible (.cons finalHead .nil) =
        [finalDying] ∧
      ConcreteElaboration.variableOrigins source.val
          sourceScope.frame.visible sourceParameters =
        parameters ∧
      ConcreteElaboration.variableOrigins final.val
          finalScopeCompiled.frame.visible finalParameters =
        parameters.map finalWireImage ∧
      aboveFold.scopeProjection.visibleProjection
          (sig := .rel args) sourceHead =
        finalHead ∧
      Vars.rename aboveFold.scopeProjection.visibleProjection
          sourceParameters =
        finalParameters ∧
      ∀ finalEnv :
          Env model.toPreModel finalScopeCompiled.frame.visible.sigs,
        finalEnv (.rel args) finalHead =
            WireQuantifierSemantics.contentRelation model definitionEnv
              contentCompiled boundaryExact
                (Vars.denote finalEnv finalParameters) →
          denoteRegion model.toPreModel definitionEnv finalEnv
              finalScopeCompiled.frame.siteBody →
            denoteRegion model.toPreModel definitionEnv
              (Env.comp finalEnv
                aboveFold.scopeProjection.visibleProjection)
              sourceScope.frame.siteBody := by
  have scopeExact :=
    RelationJoinSemantics.RelationJoinSemanticTrace.finalDyingScope trace
  cases scopeExact
  exact
    RelationJoinSemanticTrace.preBinderDenotationAtTraceScope trace
      contentCompiled sourceScope model definitionEnv boundaryExact
      relationSignature parameterSignatureExact parameterScopes


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
