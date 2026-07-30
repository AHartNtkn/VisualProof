import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalCompiler
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrameSupport

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace ExhaustedWireRemovalSemantics

open Internal

private theorem bindContextFor_cutDepth_eq
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner :
      DiagramContext definitions holeCtx
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig)) :
    (bindContextFor diagram outerIds localIds inner).cutDepth =
      inner.cutDepth := by
  induction localIds with
  | nil => rfl
  | cons _ tail induction =>
      simpa [bindContextFor, DiagramContext.cutDepth] using
        induction (.bind _ inner)

/--
One paired compiler frame with its contexts stopped strictly above the deleted
wire's scope. The two complete local `finishRegion` expressions are the hole
bodies; the zipper never crosses their unequal binder blocks.
-/
structure AboveScopeReflection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions (Target source removed) targetOuter) where
  outerCorrespond :
    ContextsCorrespond source removed targetOuter sourceOuter
  outerRemovedAbsent : removed ∉ sourceOuter.ids
  sourceSiteOuter : ConcreteElaboration.WireContext source.val
  targetSiteOuter :
    ConcreteElaboration.WireContext (Target source removed)
  siteCorrespond :
    ContextsCorrespond source removed targetSiteOuter sourceSiteOuter
  siteRemovedAbsent : removed ∉ sourceSiteOuter.ids
  sourceAbove :
    DiagramContext definitions sourceSiteOuter.sigs sourceOuter.sigs
  targetAbove :
    DiagramContext definitions targetSiteOuter.sigs targetOuter.sigs
  sourceBody :
    Region definitions
      (sourceSiteOuter.extend (source.val.wires removed).scope).sigs
  targetBody :
    Region definitions
      (targetSiteOuter.extend
        (targetRegion source removed
          (source.val.wires removed).scope)).sigs
  sourceVisibleExact :
    sourceFrame.visible =
      sourceSiteOuter.extend (source.val.wires removed).scope
  targetVisibleExact :
    targetFrame.visible =
      targetSiteOuter.extend
        (targetRegion source removed
          (source.val.wires removed).scope)
  sourceVisibleNodup :
    (sourceSiteOuter.extend (source.val.wires removed).scope).ids.Nodup
  sourceBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs sourceVisibleExact ▸
        sourceFrame.siteBody =
      sourceBody
  targetBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs targetVisibleExact ▸
        targetFrame.siteBody =
      targetBody
  localBodyLaw :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (specified : pre.Domain (source.val.wires removed).sig)
      (targetEnv :
        Env pre
          (targetSiteOuter.extend
            (targetRegion source removed
              (source.val.wires removed).scope)).sigs),
      denoteRegion pre definitionEnv targetEnv targetBody →
        denoteRegion pre definitionEnv
          (sourceEnvironmentFromTarget source removed
            (targetSiteOuter.extend
              (targetRegion source removed
                (source.val.wires removed).scope))
            (sourceSiteOuter.extend
              (source.val.wires removed).scope)
            (extend_contexts_correspond source removed siteCorrespond
              (source.val.wires removed).scope)
            pre specified targetEnv)
          sourceBody
  sourceCutDepthExact :
    sourceFrame.context.cutDepth = sourceAbove.cutDepth
  sourceFill :
    sourceFrame.context.fill sourceFrame.siteBody =
      sourceAbove.fill
        (ConcreteElaboration.finishRegion source.val sourceSiteOuter
          (source.val.wires removed).scope sourceBody)
  targetFill :
    targetFrame.context.fill targetFrame.siteBody =
      targetAbove.fill
        (ConcreteElaboration.finishRegion (Target source removed)
          targetSiteOuter
          (targetRegion source removed
            (source.val.wires removed).scope) targetBody)
  sourceDecomposition :
    DiagramContext.StopsAboveBindMany
      ((source.val.wiresAt (source.val.wires removed).scope).map
        (fun wire => (source.val.wires wire).sig))
      sourceAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
          sourceVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend sourceSiteOuter
            (source.val.wires removed).scope)) ▸ sourceFrame.context)
  composable :
    DiagramContext.ComposableSemanticZipper.{u} sourceAbove targetAbove
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (contextProjection source removed targetOuter sourceOuter
            outerCorrespond outerRemovedAbsent))
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (contextProjection source removed targetSiteOuter sourceSiteOuter
            siteCorrespond siteRemovedAbsent))

private theorem enclosing_children_unique
    (source : CheckedDiagram definitions)
    (region left right site : source.val.RegionId)
    (leftMember : left ∈ source.val.childrenOf region)
    (rightMember : right ∈ source.val.childrenOf region)
    (leftSite : source.val.Encloses left site)
    (rightSite : source.val.Encloses right site) :
    left = right := by
  have leftData :=
    ConcreteElaboration.mem_childrenOf source.val region left leftMember
  have rightData :=
    ConcreteElaboration.mem_childrenOf source.val region right rightMember
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists source.val left site).mp leftSite
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists source.val right site).mp
      rightSite
  obtain ⟨rootSteps, rootClimb⟩ := checked_reaches_root source region
  have leftRegion :
      source.val.climb (leftSteps.val + 1) site = some region := by
    rw [climb_add source.val leftSteps.val 1 site, leftClimb]
    simp [ConcreteDiagram.climb, leftData]
  have rightRegion :
      source.val.climb (rightSteps.val + 1) site = some region := by
    rw [climb_add source.val rightSteps.val 1 site, rightClimb]
    simp [ConcreteDiagram.climb, rightData]
  have leftRoot :
      source.val.climb ((leftSteps.val + 1) + rootSteps.val) site =
        some source.val.root := by
    rw [climb_add source.val (leftSteps.val + 1) rootSteps.val site,
      leftRegion]
    exact rootClimb
  have rightRoot :
      source.val.climb ((rightSteps.val + 1) + rootSteps.val) site =
        some source.val.root := by
    rw [climb_add source.val (rightSteps.val + 1) rootSteps.val site,
      rightRegion]
    exact rootClimb
  have sameLength :=
    climb_to_root_unique definitions source.val source.property
      leftRoot rightRoot
  have stepsExact : leftSteps.val = rightSteps.val := by omega
  rw [stepsExact] at leftClimb
  exact Option.some.inj (leftClimb.symm.trans rightClimb)

private theorem compileSiblingFrame_reflect_outer
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (fuel : Nat)
    (targetOuter :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetOuter sourceOuter)
    (removedAbsent : removed ∉ sourceOuter.ids)
    (sourceNested : RegionFrame definitions source.val sourceOuter)
    (targetNested :
      RegionFrame definitions (Target source removed) targetOuter)
    (nested :
      AboveScopeReflection.{u} source removed sourceOuter targetOuter
        sourceNested targetNested)
    (targetPathChild : (Target source removed).RegionId)
    (targetLeading : ItemSeq definitions targetOuter.sigs) :
    ∀ (targetChildren : List (Target source removed).RegionId)
      (_targetChildrenNodup : targetChildren.Nodup)
      (sourceLeading : ItemSeq definitions sourceOuter.sigs)
      {sourceFrame : RegionFrame definitions source.val sourceOuter},
      compileSiblingFrame? definitions source.val fuel sourceOuter
          (sourceRegion source removed targetPathChild) sourceNested
          sourceLeading
          (targetChildren.map (sourceRegion source removed)) =
        some sourceFrame →
      (∀ child, child ∈ targetChildren →
        ConcreteElaboration.ContextAbove source.val sourceOuter
          (sourceRegion source removed child)) →
      (∀ child, child ∈ targetChildren → child ≠ targetPathChild →
        ¬source.val.Encloses (sourceRegion source removed child)
          (source.val.wires removed).scope) →
      (∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetOuter.sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
            (contextProjection source removed targetOuter sourceOuter
                correspond removedAbsent))
            sourceLeading) →
      ∃ targetFrame :
          RegionFrame definitions (Target source removed) targetOuter,
        compileSiblingFrame? definitions (Target source removed) fuel
            targetOuter targetPathChild targetNested targetLeading
            targetChildren =
          some targetFrame ∧
        Nonempty
          (AboveScopeReflection.{u} source removed sourceOuter targetOuter
            sourceFrame targetFrame) := by
  intro targetChildren
  induction targetChildren generalizing targetLeading with
  | nil =>
      intro _targetChildrenNodup sourceLeading sourceFrame sourceCompiled
        allAbove outsideOther leadingLaw
      simp [compileSiblingFrame?] at sourceCompiled
  | cons targetChild tail induction =>
      intro _targetChildrenNodup sourceLeading sourceFrame sourceCompiled
        allAbove outsideOther leadingLaw
      have targetChildNotTail : targetChild ∉ tail :=
        (List.nodup_cons.mp _targetChildrenNodup).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp _targetChildrenNodup).2
      by_cases same : targetChild = targetPathChild
      · have sourceSame :
            sourceRegion source removed targetChild =
              sourceRegion source removed targetPathChild :=
          congrArg (sourceRegion source removed) same
        cases sourceSuffixEquation :
            ConcreteElaboration.compileChildrenWith? definitions source.val
              (ConcreteElaboration.compileRegion? definitions source.val
                fuel)
              sourceOuter (tail.map (sourceRegion source removed)) with
        | none =>
            simp [compileSiblingFrame?, sourceSame,
              sourceSuffixEquation] at sourceCompiled
        | some sourceSuffix =>
            obtain ⟨targetSuffix, targetSuffixCompiled, targetSuffixLaw⟩ :=
              compileChildren_reflect_of.{u} source removed targetOuter
                sourceOuter
                (ConcreteElaboration.compileRegion? definitions source.val
                  fuel)
                (ConcreteElaboration.compileRegion? definitions
                  (Target source removed) fuel)
                correspond tail sourceSuffixEquation (by
                  intro child member sourceBody sourceBodyCompiled
                  obtain ⟨targetBody, targetBodyCompiled, targetBodyLaw⟩ :=
                    compileRegion_reflect.{u} source removed
                      targetWellFormed removedEndpoints fuel targetOuter
                      sourceOuter correspond
                      (sourceRegion source removed child)
                      (allAbove child
                        (List.mem_cons_of_mem targetChild member))
                      sourceBodyCompiled
                  refine ⟨targetBody, ?_, targetBodyLaw⟩
                  simpa only [targetRegion_sourceRegion] using
                    targetBodyCompiled)
            let sourceGenerated :
                RegionFrame definitions source.val sourceOuter :=
              { visible := sourceNested.visible
                siteBody := sourceNested.siteBody
                context :=
                  .surround sourceLeading (.cut sourceNested.context)
                    sourceSuffix }
            have sourceExact : sourceFrame = sourceGenerated := by
              apply Option.some.inj
              simpa [compileSiblingFrame?, sourceSame, sourceSuffixEquation,
                sourceGenerated] using sourceCompiled.symm
            subst sourceFrame
            let targetFrame :
                RegionFrame definitions (Target source removed) targetOuter :=
              { visible := targetNested.visible
                siteBody := targetNested.siteBody
                context :=
                  .surround targetLeading (.cut targetNested.context)
                    targetSuffix }
            refine ⟨targetFrame, ?_, ⟨?_⟩⟩
            · simp [compileSiblingFrame?, same, targetSuffixCompiled,
                targetFrame]
            · refine
                { outerCorrespond := correspond
                  outerRemovedAbsent := removedAbsent
                  sourceSiteOuter := nested.sourceSiteOuter
                  targetSiteOuter := nested.targetSiteOuter
                  siteCorrespond := nested.siteCorrespond
                  siteRemovedAbsent := nested.siteRemovedAbsent
                  sourceAbove :=
                    .surround sourceLeading (.cut nested.sourceAbove)
                      sourceSuffix
                  targetAbove :=
                    .surround targetLeading (.cut nested.targetAbove)
                      targetSuffix
                  sourceBody := nested.sourceBody
                  targetBody := nested.targetBody
                  sourceVisibleExact := nested.sourceVisibleExact
                  targetVisibleExact := nested.targetVisibleExact
                  sourceVisibleNodup := nested.sourceVisibleNodup
                  sourceBodyExact := nested.sourceBodyExact
                  targetBodyExact := nested.targetBodyExact
                  localBodyLaw := nested.localBodyLaw
                  sourceCutDepthExact := by
                    simpa [sourceGenerated, DiagramContext.cutDepth] using
                      congrArg Nat.succ nested.sourceCutDepthExact
                  sourceFill := ?_
                  targetFill := ?_
                  sourceDecomposition :=
                    DiagramContext.StopsAboveBindMany.surroundCut_cast
                      ((congrArg ConcreteElaboration.WireContext.sigs
                          nested.sourceVisibleExact).trans
                        (ConcreteElaboration.WireContext.sigs_extend
                          nested.sourceSiteOuter
                          (source.val.wires removed).scope))
                      sourceLeading sourceSuffix sourceNested.context
                      nested.sourceAbove nested.sourceDecomposition
                  composable :=
                    DiagramContext.ComposableSemanticZipper.surround
                      (DiagramContext.ComposableSemanticZipper.cut
                        nested.composable)
                      sourceLeading sourceSuffix targetLeading targetSuffix
                      leadingLaw
                      (targetSuffixLaw removedAbsent
                        (fun child member =>
                          outsideOther child
                            (List.mem_cons_of_mem targetChild member)
                            (by
                              intro childSame
                              apply targetChildNotTail
                              simpa [same, childSame] using member))) }
              · simpa [sourceGenerated, DiagramContext.fill] using
                  congrArg
                    (fun body =>
                      Region.surround sourceLeading
                        (.mk (.cons (.cut body) .nil))
                        sourceSuffix)
                    nested.sourceFill
              · simpa [targetFrame, DiagramContext.fill] using
                  congrArg
                    (fun body =>
                      Region.surround targetLeading
                        (.mk (.cons (.cut body) .nil))
                        targetSuffix)
                    nested.targetFill
      · have sourceDifferent :
            sourceRegion source removed targetChild ≠
              sourceRegion source removed targetPathChild := by
          intro sourceSame
          apply same
          have mapped :=
            congrArg (targetRegion source removed) sourceSame
          simpa only [targetRegion_sourceRegion] using mapped
        cases sourceBodyEquation :
            ConcreteElaboration.compileRegion? definitions source.val fuel
              (sourceRegion source removed targetChild) sourceOuter with
        | none =>
            simp [compileSiblingFrame?, sourceDifferent,
              sourceBodyEquation] at sourceCompiled
        | some sourceBody =>
            have sourceTailCompiled :
                compileSiblingFrame? definitions source.val fuel sourceOuter
                    (sourceRegion source removed targetPathChild)
                    sourceNested
                    (sourceLeading.append (.cons (.cut sourceBody) .nil))
                    (tail.map (sourceRegion source removed)) =
                  some sourceFrame := by
              simpa [compileSiblingFrame?, sourceDifferent,
                sourceBodyEquation] using sourceCompiled
            obtain ⟨targetBody, targetBodyCompiled, targetBodyLaw⟩ :=
              compileRegion_reflect.{u} source removed targetWellFormed
                removedEndpoints fuel targetOuter sourceOuter correspond
                (sourceRegion source removed targetChild)
                (allAbove targetChild (by simp)) sourceBodyEquation
            have targetBodyCompiled' :
                ConcreteElaboration.compileRegion? definitions
                    (Target source removed) fuel targetChild targetOuter =
                  some targetBody := by
              simpa only [targetRegion_sourceRegion] using targetBodyCompiled
            obtain ⟨targetFrame, targetFrameCompiled, ⟨reflected⟩⟩ :=
              induction
                (targetLeading.append (.cons (.cut targetBody) .nil))
                tailNodup
                (sourceLeading.append (.cons (.cut sourceBody) .nil))
                sourceTailCompiled
                (by
                  intro child member
                  exact allAbove child
                    (List.mem_cons_of_mem targetChild member))
                (by
                  intro child member different
                  exact outsideOther child
                    (List.mem_cons_of_mem targetChild member) different)
                (by
                  intro pre definitionEnv env
                  simp only [denoteItemSeq_append, denoteItemSeq_cons,
                    denoteItemSeq_nil, and_true, cut_denotes_negation]
                  exact and_congr (leadingLaw pre definitionEnv env)
                    (not_congr
                      (targetBodyLaw removedAbsent
                        (outsideOther targetChild (by simp) same)
                        pre definitionEnv env)))
            refine ⟨targetFrame, ?_, ⟨reflected⟩⟩
            simpa [compileSiblingFrame?, same, targetBodyCompiled'] using
              targetFrameCompiled

/--
Reflect the enclosure-selected frame path while retaining a semantic zipper
strictly above the dying scope. Ordinary sibling bodies are delegated to the
single ordinary-region traversal in the semantics module.
-/
theorem Internal.compileRegionFrame_reflect_outer
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = []) :
    ∀ (fuel : Nat)
      (region : source.val.RegionId)
      (targetOuter :
        ConcreteElaboration.WireContext (Target source removed))
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (_correspond : ContextsCorrespond source removed
        targetOuter sourceOuter)
      (_removedAbsent : removed ∉ sourceOuter.ids)
      (_above :
        ConcreteElaboration.ContextAbove source.val sourceOuter region)
      {sourceFrame : RegionFrame definitions source.val sourceOuter},
      compileRegionFrame? definitions source.val
          (source.val.wires removed).scope fuel region sourceOuter =
        some sourceFrame →
      ∃ targetFrame :
          RegionFrame definitions (Target source removed) targetOuter,
        compileRegionFrame? definitions (Target source removed)
            (targetRegion source removed
              (source.val.wires removed).scope)
            fuel (targetRegion source removed region) targetOuter =
          some targetFrame ∧
        Nonempty
          (AboveScopeReflection.{u} source removed sourceOuter targetOuter
            sourceFrame targetFrame) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region targetOuter sourceOuter _correspond _removedAbsent _above
        sourceFrame sourceCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ fuel induction =>
      intro region targetOuter sourceOuter _correspond _removedAbsent _above
        sourceFrame sourceCompiled
      let correspond := _correspond
      let removedAbsent := _removedAbsent
      let above := _above
      by_cases atSite : region = (source.val.wires removed).scope
      · subst region
        cases sourceBodyEquation :
            compileRegionBody? definitions source.val fuel
              (source.val.wires removed).scope sourceOuter with
        | none =>
            simp [compileRegionFrame?, sourceBodyEquation] at sourceCompiled
        | some sourceBody =>
            let sourceGenerated :
                RegionFrame definitions source.val sourceOuter :=
              { visible :=
                  sourceOuter.extend (source.val.wires removed).scope
                siteBody := sourceBody
                context :=
                  bindContextFor source.val sourceOuter.ids
                    (source.val.wiresAt
                      (source.val.wires removed).scope) .hole }
            have sourceExact : sourceFrame = sourceGenerated := by
              apply Option.some.inj
              simpa [compileRegionFrame?, sourceBodyEquation,
                sourceGenerated] using sourceCompiled.symm
            subst sourceFrame
            obtain ⟨targetBody, targetBodyCompiled⟩ :=
              compileRegionBody_reflect source removed targetWellFormed
                removedEndpoints fuel targetOuter sourceOuter correspond
                (source.val.wires removed).scope above sourceBodyEquation
            let targetGenerated :
                RegionFrame definitions (Target source removed)
                  targetOuter :=
              { visible :=
                  targetOuter.extend
                    (targetRegion source removed
                      (source.val.wires removed).scope)
                siteBody := targetBody
                context :=
                  bindContextFor (Target source removed) targetOuter.ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed
                        (source.val.wires removed).scope)) .hole }
            refine ⟨targetGenerated, ?_, ⟨?_⟩⟩
            · simp [compileRegionFrame?, targetBodyCompiled,
                targetGenerated]
            · refine
                { outerCorrespond := correspond
                  outerRemovedAbsent := removedAbsent
                  sourceSiteOuter := sourceOuter
                  targetSiteOuter := targetOuter
                  siteCorrespond := correspond
                  siteRemovedAbsent := removedAbsent
                  sourceAbove := .hole
                  targetAbove := .hole
                  sourceBody := sourceBody
                  targetBody := targetBody
                  sourceVisibleExact := rfl
                  targetVisibleExact := rfl
                  sourceVisibleNodup :=
                    ConcreteElaboration.extend_nodup definitions source.val
                      source.property sourceOuter
                      (source.val.wires removed).scope above
                  sourceBodyExact := rfl
                  targetBodyExact := rfl
                  localBodyLaw := by
                    intro pre definitionEnv specified targetEnv
                      targetDenotes
                    apply
                      (compileRegionBody_corresponding_denotation
                        source removed targetWellFormed removedEndpoints fuel
                        targetOuter sourceOuter correspond
                        (source.val.wires removed).scope rfl above sourceBody
                        targetBody sourceBodyEquation targetBodyCompiled pre
                        definitionEnv specified targetEnv
                        (sourceEnvironmentFromTarget source removed
                          (targetOuter.extend
                            (targetRegion source removed
                              (source.val.wires removed).scope))
                          (sourceOuter.extend
                            (source.val.wires removed).scope)
                          (extend_contexts_correspond source removed
                            correspond (source.val.wires removed).scope)
                          pre specified targetEnv)
                        (sourceEnvironmentFromTarget_corresponds source
                          removed
                          (targetOuter.extend
                            (targetRegion source removed
                              (source.val.wires removed).scope))
                          (sourceOuter.extend
                            (source.val.wires removed).scope)
                          (extend_contexts_correspond source removed
                            correspond (source.val.wires removed).scope)
                          (ConcreteElaboration.extend_nodup definitions
                            source.val source.property sourceOuter
                            (source.val.wires removed).scope above)
                          pre specified targetEnv)).mp
                    exact targetDenotes
                  sourceCutDepthExact := by
                    exact
                      bindContextFor_cutDepth_eq source.val sourceOuter.ids
                        (source.val.wiresAt
                          (source.val.wires removed).scope) .hole
                  sourceFill := ?_
                  targetFill := ?_
                  sourceDecomposition :=
                    bindContextFor_hole_stopsAboveBindMany source.val
                      sourceOuter (source.val.wires removed).scope
                  composable :=
                    DiagramContext.ComposableSemanticZipper.hole
                      (fun (_pre : PreModel.{u}) env =>
                        Env.comp env
                          (contextProjection source removed targetOuter
                            sourceOuter correspond removedAbsent)) }
              · simpa [sourceGenerated, DiagramContext.fill] using
                  (bindContextFor_fill source.val sourceOuter.ids
                    (source.val.wiresAt
                      (source.val.wires removed).scope) .hole sourceBody
                    |>.trans
                      (finishBodyFor_eq_finishRegion source.val sourceOuter
                        (source.val.wires removed).scope sourceBody))
              · simpa [targetGenerated, DiagramContext.fill] using
                  (bindContextFor_fill (Target source removed)
                    targetOuter.ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed
                        (source.val.wires removed).scope))
                    .hole targetBody
                    |>.trans
                      (finishBodyFor_eq_finishRegion
                        (Target source removed) targetOuter
                        (targetRegion source removed
                          (source.val.wires removed).scope) targetBody))
      · cases sourceNodesEquation :
            ConcreteElaboration.compileNodes? definitions source.val
              (sourceOuter.extend region) (source.val.nodesAt region) with
        | none =>
            simp [compileRegionFrame?, atSite, sourceNodesEquation]
              at sourceCompiled
        | some sourceNodes =>
            cases sourceChildEquation :
                (source.val.childrenOf region).find? (fun candidate =>
                  decide (source.val.Encloses candidate
                    (source.val.wires removed).scope)) with
            | none =>
                simp [compileRegionFrame?, atSite, sourceNodesEquation,
                  sourceChildEquation] at sourceCompiled
            | some sourceChild =>
                cases sourceNestedEquation :
                    compileRegionFrame? definitions source.val
                      (source.val.wires removed).scope fuel sourceChild
                      (sourceOuter.extend region) with
                | none =>
                    simp [compileRegionFrame?, atSite, sourceNodesEquation,
                      sourceChildEquation, sourceNestedEquation]
                      at sourceCompiled
                | some sourceNested =>
                    cases sourceAroundEquation :
                        compileSiblingFrame? definitions source.val fuel
                          (sourceOuter.extend region) sourceChild
                          sourceNested sourceNodes
                          (source.val.childrenOf region) with
                    | none =>
                        simp [compileRegionFrame?, atSite,
                          sourceNodesEquation, sourceChildEquation,
                          sourceNestedEquation, sourceAroundEquation]
                          at sourceCompiled
                    | some sourceAround =>
                        let sourceGenerated :
                            RegionFrame definitions source.val sourceOuter :=
                          { visible := sourceAround.visible
                            siteBody := sourceAround.siteBody
                            context :=
                              bindContextFor source.val sourceOuter.ids
                                (source.val.wiresAt region)
                                sourceAround.context }
                        have sourceExact :
                            sourceFrame = sourceGenerated := by
                          apply Option.some.inj
                          simpa [compileRegionFrame?, atSite,
                            sourceNodesEquation, sourceChildEquation,
                            sourceNestedEquation, sourceAroundEquation,
                            sourceGenerated] using sourceCompiled.symm
                        subst sourceFrame
                        have sourceMember :
                            sourceChild ∈ source.val.childrenOf region :=
                          List.mem_of_find?_eq_some sourceChildEquation
                        have selectedEncloses :
                            source.val.Encloses sourceChild
                              (source.val.wires removed).scope :=
                          of_decide_eq_true
                            (List.find?_some
                              (p := fun candidate =>
                                decide (source.val.Encloses candidate
                                  (source.val.wires removed).scope))
                              sourceChildEquation)
                        have sourceExtendedAbove :
                            ConcreteElaboration.ContextAbove source.val
                              (sourceOuter.extend region) sourceChild :=
                          ConcreteElaboration.extend_above_child definitions
                            source.val source.property sourceOuter region
                            sourceChild above
                            (ConcreteElaboration.mem_childrenOf source.val
                              region sourceChild sourceMember)
                        let targetExtended :=
                          targetOuter.extend
                            (targetRegion source removed region)
                        let sourceExtended := sourceOuter.extend region
                        have extendedCorrespond :
                            ContextsCorrespond source removed targetExtended
                              sourceExtended :=
                          extend_contexts_correspond source removed correspond
                            region
                        have extendedAbsent :
                            removed ∉ sourceExtended.ids :=
                          removed_absent_extend source removed sourceOuter
                            region removedAbsent atSite
                        obtain ⟨targetNested, targetNestedCompiled,
                            ⟨nestedReflection⟩⟩ :=
                          induction sourceChild targetExtended sourceExtended
                            extendedCorrespond extendedAbsent
                            sourceExtendedAbove sourceNestedEquation
                        have targetChildEquation :
                            ((Target source removed).childrenOf
                                (targetRegion source removed region)).find?
                                (fun candidate =>
                                  decide ((Target source removed).Encloses
                                    candidate
                                    (targetRegion source removed
                                      (source.val.wires removed).scope))) =
                              some
                                (targetRegion source removed sourceChild) := by
                          rw [target_childrenOf,
                            target_find_enclosing source removed
                              (source.val.wires removed).scope
                              (source.val.childrenOf region),
                            sourceChildEquation]
                          rfl
                        have sourceAroundMapped :
                            compileSiblingFrame? definitions source.val fuel
                                sourceExtended
                                (sourceRegion source removed
                                  (targetRegion source removed sourceChild))
                                sourceNested sourceNodes
                                (((Target source removed).childrenOf
                                  (targetRegion source removed region)).map
                                  (sourceRegion source removed)) =
                              some sourceAround := by
                          simpa only [sourceRegion_targetRegion,
                            childrenOf_sources] using sourceAroundEquation
                        have targetChildrenNodup :
                            ((Target source removed).childrenOf
                              (targetRegion source removed region)).Nodup := by
                          unfold ConcreteDiagram.childrenOf
                            ConcreteDiagram.regionsList
                          exact
                            (Data.Finite.allFin_nodup
                              (Target source removed).regionCount).filter _
                        have sourceExtendedNodup :
                            sourceExtended.ids.Nodup :=
                          ConcreteElaboration.extend_nodup definitions
                            source.val source.property sourceOuter region above
                        obtain ⟨targetNodes, targetNodesCompiled,
                            sourceNodesExact⟩ :=
                          compileRegionNodes_reflect source removed
                            targetWellFormed removedEndpoints targetExtended
                            sourceExtended extendedCorrespond
                            sourceExtendedNodup region sourceNodesEquation
                        have allAbove :
                            ∀ child,
                              child ∈
                                  (Target source removed).childrenOf
                                    (targetRegion source removed region) →
                                ConcreteElaboration.ContextAbove source.val
                                  sourceExtended
                                  (sourceRegion source removed child) := by
                          intro child member
                          have sourceChildMember :
                              sourceRegion source removed child ∈
                                source.val.childrenOf region := by
                            rw [← childrenOf_sources source removed region]
                            exact List.mem_map.mpr ⟨child, member, rfl⟩
                          exact
                            ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceOuter region
                              (sourceRegion source removed child) above
                              (ConcreteElaboration.mem_childrenOf source.val
                                region (sourceRegion source removed child)
                                sourceChildMember)
                        have outsideOther :
                            ∀ child,
                              child ∈
                                  (Target source removed).childrenOf
                                    (targetRegion source removed region) →
                                child ≠
                                    targetRegion source removed sourceChild →
                                  ¬source.val.Encloses
                                    (sourceRegion source removed child)
                                    (source.val.wires removed).scope := by
                          intro child member different childSite
                          have sourceChildMember :
                              sourceRegion source removed child ∈
                                source.val.childrenOf region := by
                            rw [← childrenOf_sources source removed region]
                            exact List.mem_map.mpr ⟨child, member, rfl⟩
                          have sameSource :=
                            enclosing_children_unique source region
                              (sourceRegion source removed child) sourceChild
                              (source.val.wires removed).scope
                              sourceChildMember sourceMember childSite
                              selectedEncloses
                          apply different
                          have mapped :=
                            congrArg (targetRegion source removed) sameSource
                          simpa only [targetRegion_sourceRegion] using mapped
                        have leadingLaw :
                            ∀ (pre : PreModel.{u})
                              (definitionEnv :
                                DefinitionEnv pre definitions)
                              (env : Env pre targetExtended.sigs),
                              denoteItemSeq pre definitionEnv env
                                  targetNodes ↔
                                denoteItemSeq pre definitionEnv
                                  (Env.comp env
                                    (contextProjection source removed
                                      targetExtended sourceExtended
                                      extendedCorrespond extendedAbsent))
                                  sourceNodes := by
                          intro pre definitionEnv env
                          rw [sourceNodesExact, denoteItemSeq_renameWires,
                            contextProjection_embedding_environment source
                              removed targetExtended sourceExtended
                              extendedCorrespond sourceExtendedNodup
                              extendedAbsent pre env]
                        obtain ⟨targetAround, targetAroundCompiled,
                            ⟨aroundReflection⟩⟩ :=
                          compileSiblingFrame_reflect_outer source removed
                            targetWellFormed removedEndpoints fuel
                            targetExtended sourceExtended extendedCorrespond
                            extendedAbsent sourceNested targetNested
                            nestedReflection
                            (targetRegion source removed sourceChild)
                            targetNodes
                            ((Target source removed).childrenOf
                              (targetRegion source removed region))
                            targetChildrenNodup sourceNodes
                            sourceAroundMapped allAbove outsideOther
                            leadingLaw
                        let targetGenerated :
                            RegionFrame definitions (Target source removed)
                              targetOuter :=
                          { visible := targetAround.visible
                            siteBody := targetAround.siteBody
                            context :=
                              bindContextFor (Target source removed)
                                targetOuter.ids
                                ((Target source removed).wiresAt
                                  (targetRegion source removed region))
                                targetAround.context }
                        have targetNotSite :
                            targetRegion source removed region ≠
                              targetRegion source removed
                                (source.val.wires removed).scope :=
                          fun same =>
                            atSite
                              (targetRegion_injective source removed same)
                        refine ⟨targetGenerated, ?_, ⟨?_⟩⟩
                        · simp only [compileRegionFrame?, targetNotSite,
                            ↓reduceDIte]
                          rw [targetNodesCompiled, targetChildEquation]
                          change
                            (compileRegionFrame? definitions
                                (Target source removed)
                                (targetRegion source removed
                                  (source.val.wires removed).scope)
                                fuel
                                (targetRegion source removed sourceChild)
                                (targetOuter.extend
                                  (targetRegion source removed region))).bind
                              (fun nested =>
                                (compileSiblingFrame? definitions
                                    (Target source removed) fuel
                                    (targetOuter.extend
                                      (targetRegion source removed region))
                                    (targetRegion source removed sourceChild)
                                    nested targetNodes
                                    ((Target source removed).childrenOf
                                      (targetRegion source removed
                                        region))).bind
                                  (fun around =>
                                    some
                                      { visible := around.visible
                                        siteBody := around.siteBody
                                        context :=
                                          bindContextFor
                                            (Target source removed)
                                            targetOuter.ids
                                            ((Target source removed).wiresAt
                                              (targetRegion source removed
                                                region))
                                            around.context })) =
                              some targetGenerated
                          rw [show
                            compileRegionFrame? definitions
                                (Target source removed)
                                (targetRegion source removed
                                  (source.val.wires removed).scope)
                                fuel
                                (targetRegion source removed sourceChild)
                                (targetOuter.extend
                                  (targetRegion source removed region)) =
                              some targetNested by
                                simpa [targetExtended] using
                                  targetNestedCompiled]
                          change
                            (compileSiblingFrame? definitions
                                (Target source removed) fuel
                                (targetOuter.extend
                                  (targetRegion source removed region))
                                (targetRegion source removed sourceChild)
                                targetNested targetNodes
                                ((Target source removed).childrenOf
                                  (targetRegion source removed region))).bind
                              (fun around =>
                                some
                                  { visible := around.visible
                                    siteBody := around.siteBody
                                    context :=
                                      bindContextFor
                                        (Target source removed)
                                        targetOuter.ids
                                        ((Target source removed).wiresAt
                                          (targetRegion source removed
                                            region))
                                        around.context }) =
                              some targetGenerated
                          rw [show
                            compileSiblingFrame? definitions
                                (Target source removed) fuel
                                (targetOuter.extend
                                  (targetRegion source removed region))
                                (targetRegion source removed sourceChild)
                                targetNested targetNodes
                                ((Target source removed).childrenOf
                                  (targetRegion source removed region)) =
                              some targetAround by
                                simpa [targetExtended] using
                                  targetAroundCompiled]
                          rfl
                        · refine
                            { outerCorrespond := correspond
                              outerRemovedAbsent := removedAbsent
                              sourceSiteOuter :=
                                aroundReflection.sourceSiteOuter
                              targetSiteOuter :=
                                aroundReflection.targetSiteOuter
                              siteCorrespond :=
                                aroundReflection.siteCorrespond
                              siteRemovedAbsent :=
                                aroundReflection.siteRemovedAbsent
                              sourceAbove :=
                                bindContextFor source.val sourceOuter.ids
                                  (source.val.wiresAt region)
                                  aroundReflection.sourceAbove
                              targetAbove :=
                                bindContextFor (Target source removed)
                                  targetOuter.ids
                                  ((Target source removed).wiresAt
                                    (targetRegion source removed region))
                                  aroundReflection.targetAbove
                              sourceBody := aroundReflection.sourceBody
                              targetBody := aroundReflection.targetBody
                              sourceVisibleExact :=
                                aroundReflection.sourceVisibleExact
                              targetVisibleExact :=
                                aroundReflection.targetVisibleExact
                              sourceVisibleNodup :=
                                aroundReflection.sourceVisibleNodup
                              sourceBodyExact :=
                                aroundReflection.sourceBodyExact
                              targetBodyExact :=
                                aroundReflection.targetBodyExact
                              localBodyLaw :=
                                aroundReflection.localBodyLaw
                              sourceCutDepthExact := by
                                change
                                  (bindContextFor source.val
                                      sourceOuter.ids
                                      (source.val.wiresAt region)
                                      sourceAround.context).cutDepth =
                                    (bindContextFor source.val
                                      sourceOuter.ids
                                      (source.val.wiresAt region)
                                      aroundReflection.sourceAbove).cutDepth
                                rw [bindContextFor_cutDepth_eq,
                                  bindContextFor_cutDepth_eq]
                                exact
                                  aroundReflection.sourceCutDepthExact
                              sourceFill := ?_
                              targetFill := ?_
                              sourceDecomposition :=
                                DiagramContext.StopsAboveBindMany.bindContextFor_cast
                                  ((congrArg
                                      ConcreteElaboration.WireContext.sigs
                                      aroundReflection.sourceVisibleExact).trans
                                    (ConcreteElaboration.WireContext.sigs_extend
                                      aroundReflection.sourceSiteOuter
                                      (source.val.wires removed).scope))
                                  source.val sourceOuter.ids
                                  (source.val.wiresAt region)
                                  sourceAround.context
                                  aroundReflection.sourceAbove
                                  aroundReflection.sourceDecomposition
                              composable :=
                                retainedBindContextComposable removed targetOuter
                                  sourceOuter correspond removedAbsent region
                                  atSite above
                                  aroundReflection.sourceAbove
                                  aroundReflection.targetAbove
                                  (fun (_pre : PreModel.{u}) env =>
                                    Env.comp env
                                      (contextProjection source removed
                                        aroundReflection.targetSiteOuter
                                        aroundReflection.sourceSiteOuter
                                        aroundReflection.siteCorrespond
                                        aroundReflection.siteRemovedAbsent))
                                  aroundReflection.composable }
                          · dsimp [sourceGenerated]
                            calc
                              (bindContextFor source.val sourceOuter.ids
                                    (source.val.wiresAt region)
                                    sourceAround.context).fill
                                  sourceAround.siteBody =
                                  finishBodyFor source.val sourceOuter.ids
                                    (source.val.wiresAt region)
                                    (sourceAround.context.fill
                                      sourceAround.siteBody) :=
                                bindContextFor_fill source.val
                                  sourceOuter.ids
                                  (source.val.wiresAt region)
                                  sourceAround.context sourceAround.siteBody
                              _ =
                                  finishBodyFor source.val sourceOuter.ids
                                    (source.val.wiresAt region)
                                    (aroundReflection.sourceAbove.fill
                                      (ConcreteElaboration.finishRegion
                                        source.val
                                        aroundReflection.sourceSiteOuter
                                        (source.val.wires removed).scope
                                        aroundReflection.sourceBody)) :=
                                congrArg
                                  (finishBodyFor source.val sourceOuter.ids
                                    (source.val.wiresAt region))
                                  aroundReflection.sourceFill
                              _ =
                                  (bindContextFor source.val sourceOuter.ids
                                      (source.val.wiresAt region)
                                      aroundReflection.sourceAbove).fill
                                    (ConcreteElaboration.finishRegion
                                      source.val
                                      aroundReflection.sourceSiteOuter
                                      (source.val.wires removed).scope
                                      aroundReflection.sourceBody) :=
                                (bindContextFor_fill source.val
                                  sourceOuter.ids
                                  (source.val.wiresAt region)
                                  aroundReflection.sourceAbove
                                  (ConcreteElaboration.finishRegion source.val
                                    aroundReflection.sourceSiteOuter
                                    (source.val.wires removed).scope
                                    aroundReflection.sourceBody)).symm
                          · dsimp [targetGenerated]
                            calc
                              (bindContextFor (Target source removed)
                                    targetOuter.ids
                                    ((Target source removed).wiresAt
                                      (targetRegion source removed region))
                                    targetAround.context).fill
                                  targetAround.siteBody =
                                  finishBodyFor (Target source removed)
                                    targetOuter.ids
                                    ((Target source removed).wiresAt
                                      (targetRegion source removed region))
                                    (targetAround.context.fill
                                      targetAround.siteBody) :=
                                bindContextFor_fill (Target source removed)
                                  targetOuter.ids
                                  ((Target source removed).wiresAt
                                  (targetRegion source removed region))
                                  targetAround.context targetAround.siteBody
                              _ =
                                  finishBodyFor (Target source removed)
                                    targetOuter.ids
                                    ((Target source removed).wiresAt
                                      (targetRegion source removed region))
                                    (aroundReflection.targetAbove.fill
                                      (ConcreteElaboration.finishRegion
                                        (Target source removed)
                                        aroundReflection.targetSiteOuter
                                        (targetRegion source removed
                                          (source.val.wires removed).scope)
                                        aroundReflection.targetBody)) :=
                                congrArg
                                  (finishBodyFor (Target source removed)
                                    targetOuter.ids
                                    ((Target source removed).wiresAt
                                      (targetRegion source removed region)))
                                  aroundReflection.targetFill
                              _ =
                                  (bindContextFor (Target source removed)
                                      targetOuter.ids
                                      ((Target source removed).wiresAt
                                        (targetRegion source removed region))
                                      aroundReflection.targetAbove).fill
                                    (ConcreteElaboration.finishRegion
                                      (Target source removed)
                                      aroundReflection.targetSiteOuter
                                      (targetRegion source removed
                                        (source.val.wires removed).scope)
                                      aroundReflection.targetBody) :=
                                (bindContextFor_fill (Target source removed)
                                  targetOuter.ids
                                  ((Target source removed).wiresAt
                                    (targetRegion source removed region))
                                  aroundReflection.targetAbove
                                  (ConcreteElaboration.finishRegion
                                    (Target source removed)
                                    aroundReflection.targetSiteOuter
                                    (targetRegion source removed
                                      (source.val.wires removed).scope)
                                    aroundReflection.targetBody)).symm

end ExhaustedWireRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
