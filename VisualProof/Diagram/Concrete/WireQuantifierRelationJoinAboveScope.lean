import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinErasureSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

open Internal

private def RelationJoinStep.pairedSiblingComposableZipper
    {priorOuter baseOuter checkedOuter priorHole checkedHole : List Sig}
    (priorToBase : WireRenaming priorOuter baseOuter)
    (baseToChecked : WireRenaming baseOuter checkedOuter)
    (priorLeading : ItemSeq definitions priorOuter)
    (baseLeading : ItemSeq definitions baseOuter)
    (checkedLeading : ItemSeq definitions checkedOuter)
    (priorSuffix : ItemSeq definitions priorOuter)
    (baseSuffix : ItemSeq definitions baseOuter)
    (checkedSuffix : ItemSeq definitions checkedOuter)
    (priorInner :
      DiagramContext definitions priorHole priorOuter)
    (checkedInner :
      DiagramContext definitions checkedHole checkedOuter)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre checkedHole → Env pre priorHole)
    (nested :
      DiagramContext.ComposableSemanticZipper priorInner checkedInner
        (fun pre env =>
          Env.comp env
            (fun {_} value => baseToChecked (priorToBase value)))
        holeMap)
    (leadingPriorBase :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre baseOuter),
        denoteItemSeq pre definitionEnv env baseLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env priorToBase) priorLeading)
    (leadingBaseChecked :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre checkedOuter),
        denoteItemSeq pre definitionEnv env checkedLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env baseToChecked) baseLeading)
    (suffixPriorBase :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre baseOuter),
        denoteItemSeq pre definitionEnv env baseSuffix ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env priorToBase) priorSuffix)
    (suffixBaseChecked :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre checkedOuter),
        denoteItemSeq pre definitionEnv env checkedSuffix ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env baseToChecked) baseSuffix) :
    DiagramContext.ComposableSemanticZipper
      (.surround priorLeading (.cut priorInner) priorSuffix)
      (.surround checkedLeading (.cut checkedInner) checkedSuffix)
      (fun pre env =>
        Env.comp env
          (fun {_} value => baseToChecked (priorToBase value)))
      holeMap := by
  have leading :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre checkedOuter),
        denoteItemSeq pre definitionEnv env checkedLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (fun {_} value => baseToChecked (priorToBase value)))
            priorLeading := by
    intro pre definitionEnv env
    exact
      (leadingBaseChecked pre definitionEnv env).trans
        (leadingPriorBase pre definitionEnv
          (Env.comp env baseToChecked))
  have suffix :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre checkedOuter),
        denoteItemSeq pre definitionEnv env checkedSuffix ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (fun {_} value => baseToChecked (priorToBase value)))
            priorSuffix := by
    intro pre definitionEnv env
    exact
      (suffixBaseChecked pre definitionEnv env).trans
        (suffixPriorBase pre definitionEnv
          (Env.comp env baseToChecked))
  exact
    DiagramContext.ComposableSemanticZipper.surround
      (DiagramContext.ComposableSemanticZipper.cut nested)
      priorLeading priorSuffix checkedLeading checkedSuffix leading suffix

/--
The internal result of the simultaneous relation prefix fold before the
checked-diagram equality is transported.  Its source-to-target zipper is built
directly; the erased diagram is only the shared environment at which the two
ordinary sibling laws meet.
-/
structure Internal.RelationJoinStep.PairedAboveScopeReflection
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        source removed).WellFormed definitions)
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {site :
      (singletonErasureBase source removed candidateWellFormed).val.RegionId}
    {attachment :
      ConcreteSpliceAttachment
        (singletonErasureBase source removed candidateWellFormed)
        site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (scope : source.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceOuter))) where
  sourceSiteOuter : ConcreteElaboration.WireContext source.val
  sourceAbove :
    DiagramContext definitions sourceSiteOuter.sigs sourceOuter.sigs
  targetAbove :
    DiagramContext definitions
      (InsertionCompilation.NaturalityInternal.hostContext attachment
        (SingletonRemovalSemantics.targetContext source removed
          sourceSiteOuter)).sigs
      (InsertionCompilation.NaturalityInternal.hostContext attachment
        (SingletonRemovalSemantics.targetContext source removed
          sourceOuter)).sigs
  sourceBody :
    Region definitions (sourceSiteOuter.extend scope).sigs
  targetBody :
    Region definitions
      ((InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceSiteOuter)).extend
        (attachment.hostRegion
          (SingletonRemovalSemantics.targetRegion source removed
            scope))).sigs
  sourceStopped :
    RegionFrame definitions source.val sourceOuter
  targetStopped :
    RegionFrame definitions attachment.diagram
      (InsertionCompilation.NaturalityInternal.hostContext attachment
        (SingletonRemovalSemantics.targetContext source removed
          sourceOuter))
  sourceStoppedVisible :
    sourceStopped.visible = sourceSiteOuter.extend scope
  targetStoppedVisible :
    targetStopped.visible =
      (InsertionCompilation.NaturalityInternal.hostContext attachment
        (SingletonRemovalSemantics.targetContext source removed
          sourceSiteOuter)).extend
        (attachment.hostRegion
          (SingletonRemovalSemantics.targetRegion source removed scope))
  sourceDecomposition :
    DiagramContext.StopsAboveBindMany
      ((source.val.wiresAt scope).map
        (fun wire => (source.val.wires wire).sig))
      sourceAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            sourceStoppedVisible).trans
          (ConcreteElaboration.WireContext.sigs_extend
            sourceSiteOuter scope)) ▸
        sourceStopped.context)
  targetDecomposition :
    DiagramContext.StopsAboveBindMany
      ((attachment.diagram.wiresAt
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed
              scope))).map
        (fun wire => (attachment.diagram.wires wire).sig))
      targetAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            targetStoppedVisible).trans
          (ConcreteElaboration.WireContext.sigs_extend
            (InsertionCompilation.NaturalityInternal.hostContext attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceSiteOuter))
            (attachment.hostRegion
              (SingletonRemovalSemantics.targetRegion source removed
                scope)))) ▸
        targetStopped.context)
  sourceStoppedBody :
    congrArg ConcreteElaboration.WireContext.sigs sourceStoppedVisible ▸
        sourceStopped.siteBody =
      sourceBody
  targetStoppedBody :
    congrArg ConcreteElaboration.WireContext.sigs targetStoppedVisible ▸
        targetStopped.siteBody =
      targetBody
  sourceFill :
    sourceFrame.context.fill sourceFrame.siteBody =
      sourceAbove.fill
        (ConcreteElaboration.finishRegion source.val sourceSiteOuter scope
          sourceBody)
  targetFill :
    targetFrame.context.fill targetFrame.siteBody =
      targetAbove.fill
        (ConcreteElaboration.finishRegion attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            (SingletonRemovalSemantics.targetContext source removed
              sourceSiteOuter))
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed scope))
          targetBody)
  composable :
    DiagramContext.ComposableSemanticZipper.{u} sourceAbove targetAbove
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (fun {_} value =>
            InsertionCompilation.NaturalityInternal.hostContextRenaming
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)
              (SingletonRemovalSemantics.contextRenaming source removed
                sourceOuter value)))
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (fun {_} value =>
            InsertionCompilation.NaturalityInternal.hostContextRenaming
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceSiteOuter)
                (SingletonRemovalSemantics.contextRenaming source removed
                sourceSiteOuter value)))

/--
Stop both provenances at their shared current region.  This deliberately takes
the source half of the erasure stop and the target half of the insertion stop;
the erased current frame is only the equality that makes those two stops the
same structural boundary.
-/
theorem Internal.RelationJoinStep.pairedStopAboveCurrent
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        source removed).WellFormed definitions)
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment :
      ConcreteSpliceAttachment
        (singletonErasureBase source removed candidateWellFormed)
        (SingletonRemovalSemantics.targetRegion source removed
          (source.val.nodes removed).region)
        fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {region : source.val.RegionId}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {baseFrame :
      RegionFrame definitions
        (singletonErasureBase source removed candidateWellFormed).val
        (SingletonRemovalSemantics.targetContext source removed sourceOuter)}
    {insertionBaseFrame :
      RegionFrame definitions
        (singletonErasureBase source removed candidateWellFormed).val
        (SingletonRemovalSemantics.targetContext source removed sourceOuter)}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceOuter))}
    {siteOuter :
      ConcreteElaboration.WireContext
        (singletonErasureBase source removed candidateWellFormed).val}
    (erasure :
      SingletonRemovalSemantics.ErasureFrameProvenance source removed
        (source.val.nodes removed).region fuel sourceOuter region sourceFrame
        baseFrame)
    (insertion :
      InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance
        compiled fuel
        (SingletonRemovalSemantics.targetContext source removed sourceOuter)
        siteOuter
        (SingletonRemovalSemantics.targetRegion source removed region)
        insertionBaseFrame targetFrame)
    (baseFrameExact : insertionBaseFrame = baseFrame) :
    ∃ receipt :
        RelationJoinStep.PairedAboveScopeReflection.{u} source removed
          candidateWellFormed compiled region sourceOuter sourceFrame
          targetFrame,
      compileRegionFrame? definitions source.val region fuel region
          sourceOuter =
        some receipt.sourceStopped ∧
      compileRegionFrame? definitions attachment.diagram
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed region))
          (fuel + fragment.val.diagram.regionCount)
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed region))
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            (SingletonRemovalSemantics.targetContext source removed
              sourceOuter)) =
        some receipt.targetStopped := by
  subst insertionBaseFrame
  cases erasure with
  | site childFuel sourceOuter sourceBody baseBody sourceAbove
      sourceBodyCompiled baseBodyCompiled =>
      refine
        InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance.rec
          (base := singletonErasureBase source removed candidateWellFormed)
          (site :=
            SingletonRemovalSemantics.targetRegion source removed
              (source.val.nodes removed).region)
          (fragment := fragment) (fragmentCompiled := fragmentCompiled)
          (attachment := attachment) (compiled := compiled)
          (motive := fun insertionTotalFuel insertionOuter _ insertionRegion
              insertionBase insertionTarget _ =>
            insertionTotalFuel = childFuel + 1 →
            insertionOuter =
                SingletonRemovalSemantics.targetContext source removed
                  sourceOuter →
            insertionRegion =
                SingletonRemovalSemantics.targetRegion source removed
                  (source.val.nodes removed).region →
            HEq insertionBase
              (show
                RegionFrame definitions
                  (singletonErasureBase source removed
                    candidateWellFormed).val
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)
                from
                { visible :=
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter).extend
                    (SingletonRemovalSemantics.targetRegion source removed
                      (source.val.nodes removed).region)
                  siteBody := baseBody
                  context :=
                    bindContextFor
                      (singletonErasureBase source removed
                        candidateWellFormed).val
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter).ids
                      ((singletonErasureBase source removed
                        candidateWellFormed).val.wiresAt
                        (SingletonRemovalSemantics.targetRegion source removed
                          (source.val.nodes removed).region))
                      .hole }) →
            HEq insertionTarget targetFrame →
            ∃ receipt :
                RelationJoinStep.PairedAboveScopeReflection.{u} source
                  removed candidateWellFormed compiled
                  (source.val.nodes removed).region sourceOuter
                  { visible :=
                      sourceOuter.extend (source.val.nodes removed).region
                    siteBody := sourceBody
                    context :=
                      bindContextFor source.val sourceOuter.ids
                        (source.val.wiresAt
                          (source.val.nodes removed).region) .hole }
                  targetFrame,
              compileRegionFrame? definitions source.val
                    (source.val.nodes removed).region (childFuel + 1)
                    (source.val.nodes removed).region sourceOuter =
                some receipt.sourceStopped ∧
              compileRegionFrame? definitions attachment.diagram
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        (source.val.nodes removed).region))
                    (childFuel + 1 + fragment.val.diagram.regionCount)
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        (source.val.nodes removed).region))
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)) =
                some receipt.targetStopped)
          ?_ ?_ insertion rfl rfl rfl HEq.rfl HEq.rfl
      · intro insertionFuel insertionOuter insertionBaseBody targetBody
          baseAbove siteVisible insertionBaseBodyCompiled targetBodyCompiled
        intro fuelExact outerExact regionExact insertionBaseExact targetExact
        subst insertionOuter
        have insertionFuelExact : insertionFuel = childFuel := by omega
        subst insertionFuel
        cases targetExact
        cases insertionBaseExact
        cases regionExact
        refine
          ⟨{
            sourceSiteOuter := sourceOuter
            sourceAbove := .hole
            targetAbove := .hole
            sourceBody := sourceBody
            targetBody := targetBody
            sourceStopped :=
              { visible :=
                  sourceOuter.extend
                    (source.val.nodes removed).region
                siteBody := sourceBody
                context :=
                  bindContextFor source.val sourceOuter.ids
                    (source.val.wiresAt
                      (source.val.nodes removed).region) .hole }
            targetStopped :=
              { visible :=
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).extend
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        (source.val.nodes removed).region))
                siteBody := targetBody
                context :=
                  bindContextFor attachment.diagram
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).ids
                    (attachment.diagram.wiresAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          (source.val.nodes removed).region)))
                    .hole }
            sourceStoppedVisible := rfl
            targetStoppedVisible := rfl
            sourceDecomposition :=
              bindContextFor_hole_stopsAboveBindMany source.val sourceOuter
                (source.val.nodes removed).region
            targetDecomposition :=
              bindContextFor_hole_stopsAboveBindMany attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    (source.val.nodes removed).region))
            sourceStoppedBody := rfl
            targetStoppedBody := rfl
            sourceFill := ?_
            targetFill := ?_
            composable := ?_
          }, ?_, ?_⟩
        · change
            (bindContextFor source.val sourceOuter.ids
                (source.val.wiresAt
                  (source.val.nodes removed).region) .hole).fill
                  sourceBody =
              ConcreteElaboration.finishRegion source.val sourceOuter
                (source.val.nodes removed).region sourceBody
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          rfl
        · change
            (bindContextFor attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      (source.val.nodes removed).region)))
                .hole).fill targetBody =
              ConcreteElaboration.finishRegion attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    (source.val.nodes removed).region))
                targetBody
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          rfl
        · simpa using
            (DiagramContext.ComposableSemanticZipper.hole
              (definitions := definitions)
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (fun {_} value =>
                    InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceOuter)
                        (SingletonRemovalSemantics.contextRenaming source
                          removed sourceOuter value))))
        · simp [compileRegionFrame?, sourceBodyCompiled]
        · exact insertion.targetGenerated
      · intro insertionFuel insertionOuter insertionSiteOuter
          insertionRegion insertionSelected insertionNotSite insertionAbove
          insertionBaseNodes targetNodes insertionBaseNested targetNested
          insertionBaseAround targetAround insertionBaseNodesCompiled
          targetNodesCompiled insertionSelectedFound
          insertionBaseNestedCompiled siblings childrenNodup otherOutside
          allChildrenAbove nested induction
        intro fuelExact outerExact regionExact insertionBaseExact targetExact
        subst insertionOuter
        cases regionExact
        exact False.elim (insertionNotSite rfl)
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes baseNodes sourceNested sourceAround baseNested baseAround
      sourceNodesCompiled baseNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled baseAroundCompiled
      erasureSiblings erasureNested =>
      refine
        InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance.rec
          (base := singletonErasureBase source removed candidateWellFormed)
          (site :=
            SingletonRemovalSemantics.targetRegion source removed
              (source.val.nodes removed).region)
          (fragment := fragment) (fragmentCompiled := fragmentCompiled)
          (attachment := attachment) (compiled := compiled)
          (motive := fun insertionTotalFuel insertionOuter _ insertionRegion
              insertionBase insertionTarget _ =>
            insertionTotalFuel = childFuel + 1 →
            insertionOuter =
                SingletonRemovalSemantics.targetContext source removed
                  sourceOuter →
            insertionRegion =
                SingletonRemovalSemantics.targetRegion source removed region →
            HEq insertionBase
              (show
                RegionFrame definitions
                  (singletonErasureBase source removed
                    candidateWellFormed).val
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)
                from
                { visible :=
                    (SingletonRemovalSemantics.erasureRebaseRegionFrame
                      (SingletonRemovalSemantics.targetContext_extend source
                        removed sourceOuter region)
                      baseAround).visible
                  siteBody :=
                    (SingletonRemovalSemantics.erasureRebaseRegionFrame
                      (SingletonRemovalSemantics.targetContext_extend source
                        removed sourceOuter region)
                      baseAround).siteBody
                  context :=
                    bindContextFor
                      (singletonErasureBase source removed
                        candidateWellFormed).val
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter).ids
                      ((singletonErasureBase source removed
                        candidateWellFormed).val.wiresAt
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))
                      (SingletonRemovalSemantics.erasureRebaseRegionFrame
                        (SingletonRemovalSemantics.targetContext_extend source
                          removed sourceOuter region)
                        baseAround).context }) →
            HEq insertionTarget targetFrame →
            ∃ receipt :
                RelationJoinStep.PairedAboveScopeReflection.{u} source
                  removed candidateWellFormed compiled region sourceOuter
                  { visible := sourceAround.visible
                    siteBody := sourceAround.siteBody
                    context :=
                      bindContextFor source.val sourceOuter.ids
                        (source.val.wiresAt region) sourceAround.context }
                  targetFrame,
              compileRegionFrame? definitions source.val region
                    (childFuel + 1) region sourceOuter =
                some receipt.sourceStopped ∧
              compileRegionFrame? definitions attachment.diagram
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))
                    (childFuel + 1 + fragment.val.diagram.regionCount)
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)) =
                some receipt.targetStopped)
          ?_ ?_ insertion rfl rfl rfl HEq.rfl HEq.rfl
      · intro insertionFuel insertionOuter insertionBaseBody targetBody
          insertionAbove siteVisible insertionBaseBodyCompiled
          targetBodyCompiled
        intro fuelExact outerExact regionExact insertionBaseExact targetExact
        subst insertionOuter
        have impossible :
            (source.val.nodes removed).region = region :=
          SingletonRemovalSemantics.targetRegion_injective source removed
            regionExact
        exact False.elim (notSite impossible.symm)
      · intro insertionFuel baseOuter insertionSiteOuter baseRegion
          baseSelected baseNotSite baseAbove insertionBaseNodes targetNodes
          insertionBaseNested targetNested insertionBaseAround targetAround
          insertionBaseNodesCompiled targetNodesCompiled baseSelectedFound
          insertionBaseNestedCompiled insertionSiblings childrenNodup
          otherOutside allChildrenAbove insertionNested induction
        intro fuelExact outerExact regionExact insertionBaseExact targetExact
        subst baseOuter
        cases regionExact
        cases targetExact
        have insertionFuelExact : insertionFuel = childFuel := by omega
        subst insertionFuel
        let contextExact :=
          InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
            compiled
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)
              (SingletonRemovalSemantics.targetRegion source removed region)
              baseNotSite
        let rebasedTarget :=
          InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            contextExact targetAround
        refine
          ⟨{
            sourceSiteOuter := sourceOuter
            sourceAbove := .hole
            targetAbove := .hole
            sourceBody :=
              sourceAround.context.fill sourceAround.siteBody
            targetBody :=
              rebasedTarget.context.fill rebasedTarget.siteBody
            sourceStopped :=
              { visible := sourceOuter.extend region
                siteBody :=
                  sourceAround.context.fill sourceAround.siteBody
                context :=
                  bindContextFor source.val sourceOuter.ids
                    (source.val.wiresAt region) .hole }
            targetStopped :=
              { visible :=
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).extend
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))
                siteBody :=
                  rebasedTarget.context.fill rebasedTarget.siteBody
                context :=
                  bindContextFor attachment.diagram
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).ids
                    (attachment.diagram.wiresAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)))
                    .hole }
            sourceStoppedVisible := rfl
            targetStoppedVisible := rfl
            sourceDecomposition :=
              bindContextFor_hole_stopsAboveBindMany source.val sourceOuter
                region
            targetDecomposition :=
              bindContextFor_hole_stopsAboveBindMany attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    region))
            sourceStoppedBody := rfl
            targetStoppedBody := rfl
            sourceFill := ?_
            targetFill := ?_
            composable := ?_
          }, ?_, ?_⟩
        · change
            (bindContextFor source.val sourceOuter.ids
                (source.val.wiresAt region)
                sourceAround.context).fill sourceAround.siteBody =
              ConcreteElaboration.finishRegion source.val sourceOuter region
                (sourceAround.context.fill sourceAround.siteBody)
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          rfl
        · change
            (bindContextFor attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)))
                rebasedTarget.context).fill rebasedTarget.siteBody =
              ConcreteElaboration.finishRegion attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    region))
                (rebasedTarget.context.fill rebasedTarget.siteBody)
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          rfl
        · simpa using
            (DiagramContext.ComposableSemanticZipper.hole
              (definitions := definitions)
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (fun {_} value =>
                    InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceOuter)
                        (SingletonRemovalSemantics.contextRenaming source
                          removed sourceOuter value))))
        · have sourceBodyGenerated :=
            RelationJoinStep.compileRegionBody_of_frameBranch
              sourceNodesCompiled sourceNestedCompiled sourceAroundCompiled
          simp [compileRegionFrame?, sourceBodyGenerated]
        · obtain ⟨rawTargetNodes, rawTargetNested, rawTargetAround,
              rawTargetNodesCompiled, rawTargetNestedCompiled,
              rawTargetAroundCompiled, _rawVisible, rawTargetNodesExact,
              rawTargetNestedExact, rawTargetAroundExact⟩ :=
            InsertionCompilation.NaturalityInternal.compileFrameBranch_cast_context
              attachment.diagram contextExact
              (attachment.hostRegion
                (SingletonRemovalSemantics.targetRegion source removed
                  (source.val.nodes removed).region))
              (childFuel + fragment.val.diagram.regionCount)
              (attachment.hostRegion baseSelected)
              (((singletonErasureBase source removed
                candidateWellFormed).val.nodesAt
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)).map
                attachment.hostNode)
              (((singletonErasureBase source removed
                candidateWellFormed).val.childrenOf
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)).map
                attachment.hostRegion)
              targetNodesCompiled insertionNested.targetGenerated
              insertionSiblings.targetGenerated
          subst rawTargetNodes
          subst rawTargetNested
          subst rawTargetAround
          have rawTargetNodesCompiled' :
              ConcreteElaboration.compileNodes? definitions
                  attachment.diagram
                  ((InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).extend
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)))
                  (attachment.diagram.nodesAt
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))) =
                some
                  (InsertionCompilation.NaturalityInternal.rebaseItemSeq
                    contextExact targetNodes) := by
            rw [
              InsertionCompilation.NaturalityInternal.hostNodes_offsite
                compiled
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)
                  baseNotSite]
            exact rawTargetNodesCompiled
          have rawTargetAroundCompiled' :
              compileSiblingFrame? definitions attachment.diagram
                  (childFuel + fragment.val.diagram.regionCount)
                  ((InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).extend
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)))
                  (attachment.hostRegion baseSelected)
                  (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
                    contextExact targetNested)
                  (InsertionCompilation.NaturalityInternal.rebaseItemSeq
                    contextExact targetNodes)
                  (attachment.diagram.childrenOf
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))) =
                some
                  (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
                    contextExact targetAround) := by
            rw [
              InsertionCompilation.NaturalityInternal.hostChildren_offsite
                compiled
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)
                  baseNotSite]
            exact rawTargetAroundCompiled
          have targetBodyGenerated :=
            RelationJoinStep.compileRegionBody_of_frameBranch
              rawTargetNodesCompiled' rawTargetNestedCompiled
              rawTargetAroundCompiled'
          have targetFuelExact :
              childFuel + 1 + fragment.val.diagram.regionCount =
                childFuel + fragment.val.diagram.regionCount + 1 := by
            omega
          rw [targetFuelExact]
          simp [compileRegionFrame?, targetBodyGenerated, rebasedTarget]

/--
Replay the two exact sibling provenances simultaneously.  Outside children
extend the two pointwise laws separately; at the selected child the laws are
composed only in the transported erased environment.
-/
theorem Internal.RelationJoinStep.pairedSiblingAboveScope
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        source removed).WellFormed definitions)
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {site :
      (singletonErasureBase source removed candidateWellFormed).val.RegionId}
    {attachment :
      ConcreteSpliceAttachment
        (singletonErasureBase source removed candidateWellFormed)
        site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (fuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (selected scope : source.val.RegionId)
    {sourceNested :
      RegionFrame definitions source.val sourceContext}
    {baseNested :
      RegionFrame definitions
        (singletonErasureBase source removed candidateWellFormed).val
        (SingletonRemovalSemantics.targetContext source removed
          sourceContext)}
    {targetNested :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceContext))}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {baseLeading :
      ItemSeq definitions
        (SingletonRemovalSemantics.targetContext source removed
          sourceContext).sigs}
    {insertionBaseLeading :
      ItemSeq definitions
        (SingletonRemovalSemantics.targetContext source removed
          sourceContext).sigs}
    {targetLeading :
      ItemSeq definitions
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceContext)).sigs}
    {children : List source.val.RegionId}
    {baseChildren :
      List (singletonErasureBase source removed
        candidateWellFormed).val.RegionId}
    {sourceFrame :
      RegionFrame definitions source.val sourceContext}
    {baseFrame :
      RegionFrame definitions
        (singletonErasureBase source removed candidateWellFormed).val
        (SingletonRemovalSemantics.targetContext source removed
          sourceContext)}
    {insertionBaseFrame :
      RegionFrame definitions
        (singletonErasureBase source removed candidateWellFormed).val
        (SingletonRemovalSemantics.targetContext source removed
          sourceContext)}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceContext))}
    (erasure :
      SingletonRemovalSemantics.ErasureSiblingProvenance source removed fuel
        sourceContext selected sourceNested baseNested sourceLeading
        baseLeading children sourceFrame baseFrame)
    (insertion :
      InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance
        compiled fuel (fuel + fragment.val.diagram.regionCount)
        (SingletonRemovalSemantics.targetContext source removed sourceContext)
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          (SingletonRemovalSemantics.targetContext source removed
            sourceContext))
        (SingletonRemovalSemantics.targetRegion source removed selected)
        baseNested targetNested insertionBaseLeading targetLeading
        baseChildren insertionBaseFrame targetFrame)
    (baseLeadingExact : insertionBaseLeading = baseLeading)
    (baseChildrenExact :
      baseChildren =
        children.map
          (SingletonRemovalSemantics.targetRegion source removed))
    (childrenNodup : children.Nodup)
    (selectedMember : selected ∈ children)
    (allSourceAbove :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove source.val sourceContext child)
    (sourceOutside :
      ∀ child, child ∈ children → child ≠ selected →
        ¬source.val.Encloses child (source.val.nodes removed).region)
    (baseOutside :
      ∀ child, child ∈ children → child ≠ selected →
        ¬(singletonErasureBase source removed candidateWellFormed).val.Encloses
          (SingletonRemovalSemantics.targetRegion source removed child)
          site)
    (allTargetAbove :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            (SingletonRemovalSemantics.targetContext source removed
              sourceContext))
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed child)))
    (nested :
      RelationJoinStep.PairedAboveScopeReflection.{u} source removed
        candidateWellFormed compiled scope sourceContext sourceNested
        targetNested)
    (leadingPriorBase :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env :
          Env pre
            (SingletonRemovalSemantics.targetContext source removed
              sourceContext).sigs),
        denoteItemSeq pre definitionEnv env baseLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (SingletonRemovalSemantics.contextRenaming source removed
                sourceContext))
            sourceLeading)
    (leadingBaseTarget :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env :
          Env pre
            (InsertionCompilation.NaturalityInternal.hostContext attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceContext)).sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (InsertionCompilation.NaturalityInternal.hostContextRenaming
                attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceContext)))
                  insertionBaseLeading) :
    ∃ receipt :
        RelationJoinStep.PairedAboveScopeReflection.{u} source removed
          candidateWellFormed compiled scope sourceContext sourceFrame
          targetFrame,
      compileSiblingFrame? definitions source.val fuel sourceContext
          selected nested.sourceStopped sourceLeading children =
        some receipt.sourceStopped ∧
      compileSiblingFrame? definitions attachment.diagram
          (fuel + fragment.val.diagram.regionCount)
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            (SingletonRemovalSemantics.targetContext source removed
              sourceContext))
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed selected))
          nested.targetStopped targetLeading
          (children.map
            (fun child =>
              attachment.hostRegion
                (SingletonRemovalSemantics.targetRegion source removed
                  child))) =
        some receipt.targetStopped := by
  induction erasure generalizing insertionBaseLeading baseChildren
      insertionBaseFrame targetLeading targetFrame with
  | selected sourceLeading baseLeading tail sourceSuffix baseSuffix
      sourceSuffixCompiled baseSuffixCompiled =>
      refine
        InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance.rec
          (base :=
            singletonErasureBase source removed candidateWellFormed)
          (site := site) (fragment := fragment)
          (fragmentCompiled := fragmentCompiled)
          (attachment := attachment) (compiled := compiled)
          (sourceFuel := fuel)
          (targetFuel := fuel + fragment.val.diagram.regionCount)
          (sourceContext :=
            SingletonRemovalSemantics.targetContext source removed
              sourceContext)
          (targetContext :=
            InsertionCompilation.NaturalityInternal.hostContext attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceContext))
          (selected :=
            SingletonRemovalSemantics.targetRegion source removed selected)
          (sourceNested := baseNested) (targetNested := targetNested)
          (motive := fun insertionBaseLeading targetLeading baseChildren
              insertionBaseFrame targetFrame _ =>
            insertionBaseLeading = baseLeading →
            baseChildren =
              (selected :: tail).map
                (SingletonRemovalSemantics.targetRegion source removed) →
            (∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext)).sigs),
              denoteItemSeq pre definitionEnv env targetLeading ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                  (InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceContext)))
                  insertionBaseLeading) →
            ∃ receipt :
                RelationJoinStep.PairedAboveScopeReflection.{u} source
                  removed candidateWellFormed compiled scope sourceContext
                  { visible := sourceNested.visible
                    siteBody := sourceNested.siteBody
                    context :=
                      .surround sourceLeading (.cut sourceNested.context)
                        sourceSuffix }
                  targetFrame,
              compileSiblingFrame? definitions source.val fuel sourceContext
                  selected nested.sourceStopped sourceLeading
                  (selected :: tail) =
                some receipt.sourceStopped ∧
              compileSiblingFrame? definitions attachment.diagram
                  (fuel + fragment.val.diagram.regionCount)
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext))
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      selected))
                  nested.targetStopped targetLeading
                  ((selected :: tail).map
                    (fun child =>
                      attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          child))) =
                some receipt.targetStopped)
          ?_ ?_ insertion baseLeadingExact baseChildrenExact
          leadingBaseTarget
      · intro insertionBaseLeading targetLeading insertionTail
          insertionBaseSuffix targetSuffix suffix
        intro baseLeadingExact baseChildrenExact leadingBaseTarget
        subst insertionBaseLeading
        have tailExact :
            insertionTail =
              tail.map
                (SingletonRemovalSemantics.targetRegion source removed) :=
          (List.cons.inj (by
            simpa only [List.map_cons] using baseChildrenExact)).2
        subst insertionTail
        have baseSuffixExact : insertionBaseSuffix = baseSuffix :=
          Option.some.inj
            (suffix.sourceGenerated.symm.trans baseSuffixCompiled)
        subst insertionBaseSuffix
        have suffixPriorBase :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceContext).sigs),
              denoteItemSeq pre definitionEnv env baseSuffix ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                    (SingletonRemovalSemantics.contextRenaming source
                      removed sourceContext))
                  sourceSuffix := by
          intro pre definitionEnv env
          exact
            SingletonRemovalSemantics.compiledChildren_equiv source
              (ConcreteDiagram.DenseErasure.eraseNodeCandidate
                source removed)
              (ConcreteElaboration.compileRegion? definitions source.val
                fuel)
              (ConcreteElaboration.compileRegion? definitions
                (ConcreteDiagram.DenseErasure.eraseNodeCandidate
                  source removed) fuel)
              sourceContext
              (SingletonRemovalSemantics.targetContext source removed
                sourceContext)
              (SingletonRemovalSemantics.contextRenaming source removed
                sourceContext)
              (SingletonRemovalSemantics.targetRegion source removed)
              tail sourceSuffixCompiled baseSuffixCompiled pre
              definitionEnv env
              (by
                intro child member sourceBody baseBody sourceCompiled
                  baseCompiled
                exact
                  SingletonRemovalSemantics.compileRegion_equiv_outside
                    source removed candidateWellFormed fuel sourceContext
                    child (allSourceAbove child (by simp [member]))
                    (sourceOutside child (by simp [member]) (by
                      intro same
                      subst child
                      exact (List.nodup_cons.mp childrenNodup).1 member))
                    sourceCompiled baseCompiled pre definitionEnv env)
        have suffixBaseTarget :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext)).sigs),
              denoteItemSeq pre definitionEnv env targetSuffix ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                    (InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceContext)))
                  baseSuffix := by
          intro pre definitionEnv env
          exact
            suffix.denotationNatural
              (InsertionCompilation.NaturalityInternal.hostContextRenaming
                attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceContext))
              (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin
                attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceContext))
              pre definitionEnv env
        refine
          ⟨{
            sourceSiteOuter := nested.sourceSiteOuter
            sourceAbove :=
              .surround sourceLeading (.cut nested.sourceAbove)
                sourceSuffix
            targetAbove :=
              .surround targetLeading (.cut nested.targetAbove)
                targetSuffix
            sourceBody := nested.sourceBody
            targetBody := nested.targetBody
            sourceStopped :=
              { visible := nested.sourceStopped.visible
                siteBody := nested.sourceStopped.siteBody
                context :=
                  .surround sourceLeading
                    (.cut nested.sourceStopped.context) sourceSuffix }
            targetStopped :=
              { visible := nested.targetStopped.visible
                siteBody := nested.targetStopped.siteBody
                context :=
                  .surround targetLeading
                    (.cut nested.targetStopped.context) targetSuffix }
            sourceStoppedVisible := nested.sourceStoppedVisible
            targetStoppedVisible := nested.targetStoppedVisible
            sourceDecomposition :=
              DiagramContext.StopsAboveBindMany.surroundCut_cast
                ((congrArg ConcreteElaboration.WireContext.sigs
                    nested.sourceStoppedVisible).trans
                  (ConcreteElaboration.WireContext.sigs_extend
                    nested.sourceSiteOuter scope))
                sourceLeading sourceSuffix nested.sourceStopped.context
                nested.sourceAbove nested.sourceDecomposition
            targetDecomposition :=
              DiagramContext.StopsAboveBindMany.surroundCut_cast
                ((congrArg ConcreteElaboration.WireContext.sigs
                    nested.targetStoppedVisible).trans
                  (ConcreteElaboration.WireContext.sigs_extend
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        nested.sourceSiteOuter))
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        scope))))
                targetLeading targetSuffix nested.targetStopped.context
                nested.targetAbove nested.targetDecomposition
            sourceStoppedBody := nested.sourceStoppedBody
            targetStoppedBody := nested.targetStoppedBody
            sourceFill := ?_
            targetFill := ?_
            composable :=
              RelationJoinStep.pairedSiblingComposableZipper
                (SingletonRemovalSemantics.contextRenaming source removed
                  sourceContext)
                (InsertionCompilation.NaturalityInternal.hostContextRenaming
                  attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext))
                sourceLeading baseLeading targetLeading sourceSuffix
                baseSuffix targetSuffix nested.sourceAbove
                nested.targetAbove
                (fun (_pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming
                        attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed nested.sourceSiteOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed nested.sourceSiteOuter value)))
                nested.composable leadingPriorBase leadingBaseTarget
                suffixPriorBase suffixBaseTarget
          }, ?_, ?_⟩
        · simpa only [DiagramContext.fill] using
            congrArg
              (fun body =>
                Region.surround sourceLeading
                  (.mk (.cons (.cut body) .nil)) sourceSuffix)
              nested.sourceFill
        · simpa only [DiagramContext.fill] using
            congrArg
              (fun body =>
                Region.surround targetLeading
                  (.mk (.cons (.cut body) .nil)) targetSuffix)
              nested.targetFill
        · simp [compileSiblingFrame?, sourceSuffixCompiled]
        · have targetChildrenExact :
              (tail.map
                    (SingletonRemovalSemantics.targetRegion source removed)).map
                  attachment.hostRegion =
                tail.map
                  (fun child =>
                    attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        child)) := by
            exact
              RelationJoinStep.map_map_exact tail
                (SingletonRemovalSemantics.targetRegion source removed)
                attachment.hostRegion
          have targetSuffixGenerated :
              ConcreteElaboration.compileChildrenWith? definitions
                  attachment.diagram
                  (ConcreteElaboration.compileRegion? definitions
                    attachment.diagram
                    (fuel + fragment.val.diagram.regionCount))
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext))
                  (tail.map
                    (fun child =>
                      attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          child))) =
                some targetSuffix := by
            exact targetChildrenExact ▸ suffix.targetGenerated
          simp only [List.map_cons]
          unfold compileSiblingFrame?
          split
          · rw [targetSuffixGenerated]
            rfl
          · rename_i different
            exact (different rfl).elim
      · intro insertionBaseLeading targetLeading insertionChild
          insertionTail different insertionBaseBody targetBody
          insertionBaseBodyCompiled targetBodyCompiled
          _insertionSourceFrame _insertionTargetFrame insertionRest
          _induction
        intro _baseLeadingExact baseChildrenExact _leadingBaseTarget
        have headExact :
            insertionChild =
              SingletonRemovalSemantics.targetRegion source removed
                selected :=
          (List.cons.inj (by
            simpa only [List.map_cons] using baseChildrenExact)).1
        exact (different headExact).elim
  | outside sourceLeading baseLeading child tail different sourceBody
      baseBody sourceBodyCompiled baseBodyCompiled rest induction =>
      refine
        InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance.rec
          (base :=
            singletonErasureBase source removed candidateWellFormed)
          (site := site) (fragment := fragment)
          (fragmentCompiled := fragmentCompiled)
          (attachment := attachment) (compiled := compiled)
          (sourceFuel := fuel)
          (targetFuel := fuel + fragment.val.diagram.regionCount)
          (sourceContext :=
            SingletonRemovalSemantics.targetContext source removed
              sourceContext)
          (targetContext :=
            InsertionCompilation.NaturalityInternal.hostContext attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceContext))
          (selected :=
            SingletonRemovalSemantics.targetRegion source removed selected)
          (sourceNested := baseNested) (targetNested := targetNested)
          (motive := fun insertionBaseLeading targetLeading baseChildren
              insertionBaseFrame targetFrame _ =>
            insertionBaseLeading = baseLeading →
            baseChildren =
              (child :: tail).map
                (SingletonRemovalSemantics.targetRegion source removed) →
            (∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext)).sigs),
              denoteItemSeq pre definitionEnv env targetLeading ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                  (InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceContext)))
                  insertionBaseLeading) →
            ∃ receipt :
                RelationJoinStep.PairedAboveScopeReflection.{u} source
                  removed candidateWellFormed compiled scope sourceContext
                  _ targetFrame,
              compileSiblingFrame? definitions source.val fuel sourceContext
                  selected nested.sourceStopped sourceLeading
                  (child :: tail) =
                some receipt.sourceStopped ∧
              compileSiblingFrame? definitions attachment.diagram
                  (fuel + fragment.val.diagram.regionCount)
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext))
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      selected))
                  nested.targetStopped targetLeading
                  ((child :: tail).map
                    (fun candidate =>
                      attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          candidate))) =
                some receipt.targetStopped)
          ?_ ?_ insertion baseLeadingExact baseChildrenExact
          leadingBaseTarget
      · intro insertionBaseLeading targetLeading insertionTail
          insertionBaseSuffix targetSuffix suffix
        intro _baseLeadingExact baseChildrenExact _leadingBaseTarget
        have headExact :
            SingletonRemovalSemantics.targetRegion source removed selected =
              SingletonRemovalSemantics.targetRegion source removed child :=
          (List.cons.inj (by
            simpa only [List.map_cons] using baseChildrenExact)).1
        exact
          (different
            (SingletonRemovalSemantics.targetRegion_injective source
              removed headExact.symm)).elim
      · intro insertionBaseLeading targetLeading insertionChild
          insertionTail baseDifferent insertionBaseBody
          targetBody insertionBaseBodyCompiled targetBodyCompiled
          insertionSourceFrame insertionTargetFrame insertionRest
          _insertionInduction
        intro baseLeadingExact baseChildrenExact leadingBaseTarget
        subst insertionBaseLeading
        have headExact :
            insertionChild =
              SingletonRemovalSemantics.targetRegion source removed child :=
          (List.cons.inj (by
            simpa only [List.map_cons] using baseChildrenExact)).1
        have tailExact :
            insertionTail =
              tail.map
                (SingletonRemovalSemantics.targetRegion source removed) :=
          (List.cons.inj (by
            simpa only [List.map_cons] using baseChildrenExact)).2
        subst insertionChild
        subst insertionTail
        have baseBodyExact : insertionBaseBody = baseBody :=
          Option.some.inj
            (insertionBaseBodyCompiled.symm.trans baseBodyCompiled)
        subst insertionBaseBody
        have sourceBodyLaw :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceContext).sigs),
              denoteRegion pre definitionEnv env baseBody ↔
                denoteRegion pre definitionEnv
                  (Env.comp env
                    (SingletonRemovalSemantics.contextRenaming source
                      removed sourceContext))
                  sourceBody :=
          SingletonRemovalSemantics.compileRegion_equiv_outside source
            removed candidateWellFormed fuel sourceContext child
            (allSourceAbove child (by simp))
            (sourceOutside child (by simp) different)
            sourceBodyCompiled baseBodyCompiled
        have targetBodyLaw :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceContext)).sigs),
              denoteRegion pre definitionEnv env targetBody ↔
                denoteRegion pre definitionEnv
                  (Env.comp env
                    (InsertionCompilation.NaturalityInternal.hostContextRenaming
                      attachment
                        (SingletonRemovalSemantics.targetContext source
                          removed sourceContext)))
                  baseBody :=
          InsertionCompilation.NaturalityInternal.hostRegion_denotation_natural_outside
            compiled fuel
              (fuel + fragment.val.diagram.regionCount)
              (SingletonRemovalSemantics.targetRegion source removed child)
              (baseOutside child (by simp) different)
              (SingletonRemovalSemantics.targetContext source removed
                sourceContext)
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceContext))
              (InsertionCompilation.NaturalityInternal.hostContextRenaming
                attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceContext))
              (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin
                attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceContext))
              (allTargetAbove child (by simp))
              baseBodyCompiled targetBodyCompiled
        obtain ⟨receipt, sourceRestGenerated, targetRestGenerated⟩ :=
          induction
            (insertion := insertionRest)
            (baseLeadingExact := rfl)
            (baseChildrenExact := rfl)
            (childrenNodup := (List.nodup_cons.mp childrenNodup).2)
            (selectedMember :=
              List.mem_of_ne_of_mem (Ne.symm different) selectedMember)
            (allSourceAbove := fun candidate member =>
              allSourceAbove candidate (by simp [member]))
            (sourceOutside := fun candidate member candidateDifferent =>
              sourceOutside candidate (by simp [member])
                candidateDifferent)
            (baseOutside := fun candidate member candidateDifferent =>
              baseOutside candidate (by simp [member])
                candidateDifferent)
            (allTargetAbove := fun candidate member =>
              allTargetAbove candidate (by simp [member]))
            (leadingPriorBase := by
              intro pre definitionEnv env
              simp only [denoteItemSeq_append, denoteItemSeq_cons,
                denoteItemSeq_nil, and_true, cut_denotes_negation]
              exact and_congr (leadingPriorBase pre definitionEnv env)
                (not_congr
                  (sourceBodyLaw pre definitionEnv env)))
            (leadingBaseTarget := by
              intro pre definitionEnv env
              simp only [denoteItemSeq_append, denoteItemSeq_cons,
                denoteItemSeq_nil, and_true, cut_denotes_negation]
              exact and_congr (leadingBaseTarget pre definitionEnv env)
                (not_congr
                  (targetBodyLaw pre definitionEnv env)))
        refine ⟨receipt, ?_, ?_⟩
        · simp [compileSiblingFrame?, different, sourceBodyCompiled,
            sourceRestGenerated]
        · have hostDifferent :
              attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      child) ≠
                attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      selected) :=
            fun same =>
              baseDifferent
                (InsertionCompilation.NaturalityInternal.hostRegion_injective
                  attachment same)
          simp only [List.map_cons]
          unfold compileSiblingFrame?
          split
          · rename_i same
            exact (hostDifferent same).elim
          · rw [targetBodyCompiled]
            exact targetRestGenerated

end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
