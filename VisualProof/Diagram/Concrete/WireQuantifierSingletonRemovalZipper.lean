import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalFrame
import VisualProof.Diagram.ContextZipper

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

private abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate source removed

/--
An erasure frame split strictly above a retained scope. The unequal binder
blocks at that scope stay inside the two complete `finishRegion` hole bodies.
-/
structure ErasureAboveScopeReceipt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (scope : source.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)) where
  sourceSiteOuter : ConcreteElaboration.WireContext source.val
  sourceAbove :
    DiagramContext definitions sourceSiteOuter.sigs sourceOuter.sigs
  targetAbove :
    DiagramContext definitions
      (targetContext source removed sourceSiteOuter).sigs
      (targetContext source removed sourceOuter).sigs
  sourceBody :
    Region definitions (sourceSiteOuter.extend scope).sigs
  targetBody :
    Region definitions
      ((targetContext source removed sourceSiteOuter).extend
        (targetRegion source removed scope)).sigs
  sourceFill :
    sourceFrame.context.fill sourceFrame.siteBody =
      sourceAbove.fill
        (ConcreteElaboration.finishRegion source.val sourceSiteOuter scope
          sourceBody)
  targetFill :
    targetFrame.context.fill targetFrame.siteBody =
      targetAbove.fill
        (ConcreteElaboration.finishRegion (Target source removed)
          (targetContext source removed sourceSiteOuter)
          (targetRegion source removed scope) targetBody)
  zipper :
    DiagramContext.SemanticZipper.{u} sourceAbove targetAbove
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (contextRenaming source removed sourceOuter))
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (contextRenaming source removed sourceSiteOuter))

/--
Stop an erasure provenance fold before the current region's binder block.
This is the base constructor used by the above-scope prefix reconstruction.
-/
theorem ErasureFrameProvenance.stopAboveCurrent
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    {site : source.val.RegionId}
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {region : source.val.RegionId}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)}
    (provenance :
      ErasureFrameProvenance source removed site fuel sourceOuter region
        sourceFrame targetFrame) :
    Nonempty
      (ErasureAboveScopeReceipt.{u} source removed region sourceOuter
        sourceFrame targetFrame) := by
  cases provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      sourceBodyCompiled targetBodyCompiled =>
      refine
        ⟨{
          sourceSiteOuter := sourceOuter
          sourceAbove := .hole
          targetAbove := .hole
          sourceBody := sourceBody
          targetBody := targetBody
          sourceFill := ?_
          targetFill := ?_
          zipper := ?_
        }⟩
      · change
          (bindContextFor source.val sourceOuter.ids
              (source.val.wiresAt site) .hole).fill sourceBody =
            ConcreteElaboration.finishRegion source.val sourceOuter site
              sourceBody
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · change
          (bindContextFor (Target source removed)
              (targetContext source removed sourceOuter).ids
              ((Target source removed).wiresAt
                (targetRegion source removed site)) .hole).fill targetBody =
            ConcreteElaboration.finishRegion (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed site) targetBody
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · simpa using
          (DiagramContext.SemanticZipper.hole
            (definitions := definitions)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (contextRenaming source removed sourceOuter)))
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes targetNodes sourceNested sourceAround targetNested
      targetAround sourceNodesCompiled targetNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
      siblings nested =>
      let contextExact :=
        targetContext_extend source removed sourceOuter region
      let rebasedTarget :=
        erasureRebaseRegionFrame contextExact targetAround
      refine
        ⟨{
          sourceSiteOuter := sourceOuter
          sourceAbove := .hole
          targetAbove := .hole
          sourceBody :=
            sourceAround.context.fill sourceAround.siteBody
          targetBody :=
            rebasedTarget.context.fill rebasedTarget.siteBody
          sourceFill := ?_
          targetFill := ?_
          zipper := ?_
        }⟩
      · change
          (bindContextFor source.val sourceOuter.ids
              (source.val.wiresAt region) sourceAround.context).fill
                sourceAround.siteBody =
            ConcreteElaboration.finishRegion source.val sourceOuter region
              (sourceAround.context.fill sourceAround.siteBody)
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · change
          (bindContextFor (Target source removed)
              (targetContext source removed sourceOuter).ids
              ((Target source removed).wiresAt
                (targetRegion source removed region))
              rebasedTarget.context).fill rebasedTarget.siteBody =
            ConcreteElaboration.finishRegion (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed region)
              (rebasedTarget.context.fill rebasedTarget.siteBody)
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · simpa using
          (DiagramContext.SemanticZipper.hole
            (definitions := definitions)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (contextRenaming source removed sourceOuter)))

/-- Transport the complete binder context of one retained erasure region. -/
theorem erasureBindContextZipper
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceOuter.extend region).ids.Nodup)
    (sourceInner :
      DiagramContext definitions sourceHole
        (sourceOuter.extend region).sigs)
    (targetInner :
      DiagramContext definitions targetHole
        ((targetContext source removed sourceOuter).extend
          (targetRegion source removed region)).sigs)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole)
    (inner :
      DiagramContext.SemanticZipper sourceInner targetInner
        (fun pre env =>
          Env.comp env
            (extendedContextRenaming source removed sourceOuter region))
        holeMap) :
    DiagramContext.SemanticZipper
      (bindContextFor source.val sourceOuter.ids
        (source.val.wiresAt region) sourceInner)
      (bindContextFor (Target source removed)
        (targetContext source removed sourceOuter).ids
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        targetInner)
      (fun pre env =>
        Env.comp env (contextRenaming source removed sourceOuter))
      holeMap := by
  have bindDepth :
      ∀ {holeCtx : List Sig}
        (diagram : ConcreteDiagram definitions.length)
        (outerIds localIds : List diagram.WireId)
        (context :
          DiagramContext definitions holeCtx
            ((localIds ++ outerIds).map fun wire =>
              (diagram.wires wire).sig)),
        (bindContextFor diagram outerIds localIds context).cutDepth =
          context.cutDepth := by
    intro holeCtx diagram outerIds localIds context
    induction localIds with
    | nil => simp [bindContextFor]
    | cons head tail induction =>
        simpa [bindContextFor, DiagramContext.cutDepth] using
          induction (.bind (diagram.wires head).sig context)
  constructor
  · rw [bindDepth source.val sourceOuter.ids
        (source.val.wiresAt region) sourceInner,
      bindDepth (Target source removed)
        (targetContext source removed sourceOuter).ids
        ((Target source removed).wiresAt
          (targetRegion source removed region)) targetInner]
    exact inner.cutDepth_eq
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    rw [bindDepth source.val sourceOuter.ids
      (source.val.wiresAt region) sourceInner]
    rw [bindContextFor_fill, bindContextFor_fill,
      finishBodyFor_eq_finishRegion, finishBodyFor_eq_finishRegion]
    generalize effectiveEq :
      direction.through sourceInner.cutDepth = effective
    cases effective with
    | targetToSource =>
        refine effectiveEq.symm ▸ ?_
        simp only [DiagramContext.ContextDirection.holds]
        intro targetFinished
        obtain ⟨targetValues, targetCore⟩ :=
          (ConcreteElaboration.denote_finishRegion definitions
            (Target source removed)
            (targetContext source removed sourceOuter)
            (targetRegion source removed region) pre definitionEnv fixed
            (targetInner.fill targetBody)).mp targetFinished
        obtain ⟨sourceValues, environments⟩ :=
          (extendedEnvironment_correspondence source removed sourceOuter
            region sourceExtendedNodup pre
            (Env.comp fixed (contextRenaming source removed sourceOuter))
            fixed rfl).2 targetValues
        apply
          (ConcreteElaboration.denote_finishRegion definitions source.val
            sourceOuter region pre definitionEnv
            (Env.comp fixed (contextRenaming source removed sourceOuter))
            (sourceInner.fill sourceBody)).mpr
        refine ⟨sourceValues, ?_⟩
        rw [environments]
        have middle :=
          inner.transport direction pre definitionEnv sourceBody targetBody
            (ConcreteElaboration.extendEnvironment
              (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed region) targetValues fixed)
            (by
              intro descendant preserves
              exact localLaw descendant
                (DiagramContext.preservesOuter_bindContextFor
                  (Target source removed)
                  (targetContext source removed sourceOuter)
                  (targetRegion source removed region)
                  targetInner pre targetValues fixed descendant preserves))
        have directedMiddle := effectiveEq ▸ middle
        exact directedMiddle targetCore
    | sourceToTarget =>
        refine effectiveEq.symm ▸ ?_
        simp only [DiagramContext.ContextDirection.holds]
        intro sourceFinished
        obtain ⟨sourceValues, sourceCore⟩ :=
          (ConcreteElaboration.denote_finishRegion definitions source.val
            sourceOuter region pre definitionEnv
            (Env.comp fixed (contextRenaming source removed sourceOuter))
            (sourceInner.fill sourceBody)).mp sourceFinished
        obtain ⟨targetValues, environments⟩ :=
          (extendedEnvironment_correspondence source removed sourceOuter
            region sourceExtendedNodup pre
            (Env.comp fixed (contextRenaming source removed sourceOuter))
            fixed rfl).1 sourceValues
        apply
          (ConcreteElaboration.denote_finishRegion definitions
            (Target source removed)
            (targetContext source removed sourceOuter)
            (targetRegion source removed region) pre definitionEnv fixed
            (targetInner.fill targetBody)).mpr
        refine ⟨targetValues, ?_⟩
        have middle :=
          inner.transport direction pre definitionEnv sourceBody targetBody
            (ConcreteElaboration.extendEnvironment
              (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed region) targetValues fixed)
            (by
              intro descendant preserves
              exact localLaw descendant
                (DiagramContext.preservesOuter_bindContextFor
                  (Target source removed)
                  (targetContext source removed sourceOuter)
                  (targetRegion source removed region)
                  targetInner pre targetValues fixed descendant preserves))
        have directedMiddle := effectiveEq ▸ middle
        apply directedMiddle
        rw [environments] at sourceCore
        exact sourceCore

private theorem ErasureSiblingProvenance.zipper
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    {fuel : Nat}
    (context : ConcreteElaboration.WireContext source.val)
    (region selected : source.val.RegionId)
    {sourceNested :
      RegionFrame definitions source.val (context.extend region)}
    {targetNested :
      RegionFrame definitions (Target source removed)
        (targetContext source removed (context.extend region))}
    {sourceLeading :
      ItemSeq definitions (context.extend region).sigs}
    {targetLeading :
      ItemSeq definitions
        (targetContext source removed (context.extend region)).sigs}
    {children : List source.val.RegionId}
    {sourceFrame :
      RegionFrame definitions source.val (context.extend region)}
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed (context.extend region))}
    (provenance :
      ErasureSiblingProvenance source removed fuel
        (context.extend region) selected sourceNested targetNested
        sourceLeading targetLeading children sourceFrame targetFrame)
    (childrenSubset :
      ∀ child, child ∈ children →
        child ∈ source.val.childrenOf region)
    (childrenNodup : children.Nodup)
    (selectedMember : selected ∈ children)
    (allAbove :
      ∀ child, child ∈ source.val.childrenOf region →
        ConcreteElaboration.ContextAbove source.val
          (context.extend region) child)
    (outsideOther :
      ∀ child, child ∈ source.val.childrenOf region →
        child ≠ selected →
          ¬source.val.Encloses child (source.val.nodes removed).region)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetNested.visible.sigs →
        Env pre sourceNested.visible.sigs)
    (nestedZipper :
      DiagramContext.SemanticZipper sourceNested.context
        targetNested.context
        (fun pre env =>
          Env.comp env
            (contextRenaming source removed (context.extend region)))
        holeMap)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env :
          Env pre
            (targetContext source removed
              (context.extend region)).sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (contextRenaming source removed (context.extend region)))
            sourceLeading) :
    ∃ (sourceVisible : sourceFrame.visible = sourceNested.visible)
      (targetVisible : targetFrame.visible = targetNested.visible),
      congrArg ConcreteElaboration.WireContext.sigs sourceVisible ▸
          sourceFrame.siteBody =
        sourceNested.siteBody ∧
      congrArg ConcreteElaboration.WireContext.sigs targetVisible ▸
          targetFrame.siteBody =
        targetNested.siteBody ∧
      DiagramContext.SemanticZipper sourceFrame.context
        targetFrame.context
        (fun pre env =>
          Env.comp env
            (contextRenaming source removed (context.extend region)))
        (fun pre env =>
          congrArg ConcreteElaboration.WireContext.sigs
              sourceVisible.symm ▸
            holeMap pre
              (congrArg ConcreteElaboration.WireContext.sigs
                targetVisible ▸ env)) := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      sourceSuffixCompiled targetSuffixCompiled =>
      rw [List.nodup_cons] at childrenNodup
      have suffixLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env :
              Env pre
                (targetContext source removed
                  (context.extend region)).sigs),
            denoteItemSeq pre definitionEnv env targetSuffix ↔
              denoteItemSeq pre definitionEnv
                (Env.comp env
                  (contextRenaming source removed (context.extend region)))
                sourceSuffix := by
        intro pre definitionEnv env
        exact
          compiledChildren_equiv source (Target source removed)
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (ConcreteElaboration.compileRegion? definitions
              (Target source removed) fuel)
            (context.extend region)
            (targetContext source removed (context.extend region))
            (contextRenaming source removed (context.extend region))
            (targetRegion source removed) tail sourceSuffixCompiled
            targetSuffixCompiled pre definitionEnv env
            (by
              intro child member sourceBody targetBody sourceCompiled
                targetCompiled
              have fullMember :=
                childrenSubset child (List.mem_cons_of_mem selected member)
              exact
                compileRegion_equiv_outside source removed
                  candidateWellFormed fuel (context.extend region) child
                  (allAbove child fullMember)
                  (outsideOther child fullMember (by
                    intro same
                    subst child
                    exact childrenNodup.1 member))
                  sourceCompiled targetCompiled pre definitionEnv env)
      exact
        ⟨rfl, rfl, rfl, rfl,
          DiagramContext.SemanticZipper.surround
            (DiagramContext.SemanticZipper.cut nestedZipper)
            sourceLeading sourceSuffix targetLeading targetSuffix
            leadingLaw suffixLaw⟩
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      rw [List.nodup_cons] at childrenNodup
      have childMember := childrenSubset child (by simp)
      have bodyLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env :
              Env pre
                (targetContext source removed
                  (context.extend region)).sigs),
            denoteRegion pre definitionEnv env targetBody ↔
              denoteRegion pre definitionEnv
                (Env.comp env
                  (contextRenaming source removed (context.extend region)))
                sourceBody :=
        compileRegion_equiv_outside source removed
          candidateWellFormed fuel (context.extend region) child
          (allAbove child childMember)
          (outsideOther child childMember different)
          sourceBodyCompiled targetBodyCompiled
      exact
        induction
          (fun candidate member =>
            childrenSubset candidate
              (List.mem_cons_of_mem child member))
          childrenNodup.2
          (List.mem_of_ne_of_mem (Ne.symm different) selectedMember)
          (by
            intro pre definitionEnv env
            simp only [denoteItemSeq_append, denoteItemSeq_cons,
              denoteItemSeq_nil, and_true, cut_denotes_negation]
            exact and_congr (leadingLaw pre definitionEnv env)
              (not_congr (bodyLaw pre definitionEnv env)))

/--
Replay a sibling provenance around a context already stopped above a deeper
scope. The completed scope block remains the unique hole body.
-/
private theorem ErasureSiblingProvenance.aboveScope
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    {fuel : Nat}
    (context : ConcreteElaboration.WireContext source.val)
    (region selected scope : source.val.RegionId)
    {sourceNested :
      RegionFrame definitions source.val (context.extend region)}
    {targetNested :
      RegionFrame definitions (Target source removed)
        (targetContext source removed (context.extend region))}
    {sourceLeading :
      ItemSeq definitions (context.extend region).sigs}
    {targetLeading :
      ItemSeq definitions
        (targetContext source removed (context.extend region)).sigs}
    {children : List source.val.RegionId}
    {sourceFrame :
      RegionFrame definitions source.val (context.extend region)}
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed (context.extend region))}
    (provenance :
      ErasureSiblingProvenance source removed fuel
        (context.extend region) selected sourceNested targetNested
        sourceLeading targetLeading children sourceFrame targetFrame)
    (childrenSubset :
      ∀ child, child ∈ children →
        child ∈ source.val.childrenOf region)
    (childrenNodup : children.Nodup)
    (selectedMember : selected ∈ children)
    (allAbove :
      ∀ child, child ∈ source.val.childrenOf region →
        ConcreteElaboration.ContextAbove source.val
          (context.extend region) child)
    (outsideOther :
      ∀ child, child ∈ source.val.childrenOf region →
        child ≠ selected →
          ¬source.val.Encloses child (source.val.nodes removed).region)
    (nestedReceipt :
      ErasureAboveScopeReceipt.{u} source removed scope
        (context.extend region) sourceNested targetNested)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env :
          Env pre
            (targetContext source removed
              (context.extend region)).sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (contextRenaming source removed (context.extend region)))
            sourceLeading) :
    Nonempty
      (ErasureAboveScopeReceipt.{u} source removed scope
        (context.extend region) sourceFrame targetFrame) := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      sourceSuffixCompiled targetSuffixCompiled =>
      rw [List.nodup_cons] at childrenNodup
      have suffixLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env :
              Env pre
                (targetContext source removed
                  (context.extend region)).sigs),
            denoteItemSeq pre definitionEnv env targetSuffix ↔
              denoteItemSeq pre definitionEnv
                (Env.comp env
                  (contextRenaming source removed
                    (context.extend region)))
                sourceSuffix := by
        intro pre definitionEnv env
        exact
          compiledChildren_equiv source (Target source removed)
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (ConcreteElaboration.compileRegion? definitions
              (Target source removed) fuel)
            (context.extend region)
            (targetContext source removed (context.extend region))
            (contextRenaming source removed (context.extend region))
            (targetRegion source removed) tail sourceSuffixCompiled
            targetSuffixCompiled pre definitionEnv env
            (by
              intro child member sourceBody targetBody sourceCompiled
                targetCompiled
              have fullMember :=
                childrenSubset child
                  (List.mem_cons_of_mem selected member)
              exact
                compileRegion_equiv_outside source removed
                  candidateWellFormed fuel (context.extend region) child
                  (allAbove child fullMember)
                  (outsideOther child fullMember (by
                    intro same
                    subst child
                    exact childrenNodup.1 member))
                  sourceCompiled targetCompiled pre definitionEnv env)
      refine
        ⟨{
          sourceSiteOuter := nestedReceipt.sourceSiteOuter
          sourceAbove :=
            .surround sourceLeading (.cut nestedReceipt.sourceAbove)
              sourceSuffix
          targetAbove :=
            .surround targetLeading (.cut nestedReceipt.targetAbove)
              targetSuffix
          sourceBody := nestedReceipt.sourceBody
          targetBody := nestedReceipt.targetBody
          sourceFill := ?_
          targetFill := ?_
          zipper :=
            DiagramContext.SemanticZipper.surround
              (DiagramContext.SemanticZipper.cut nestedReceipt.zipper)
              sourceLeading sourceSuffix targetLeading targetSuffix
              leadingLaw suffixLaw
        }⟩
      · simpa only [DiagramContext.fill] using
          congrArg
            (fun body =>
              Region.surround sourceLeading (.mk (.cons (.cut body) .nil))
                sourceSuffix)
            nestedReceipt.sourceFill
      · simpa only [DiagramContext.fill] using
          congrArg
            (fun body =>
              Region.surround targetLeading (.mk (.cons (.cut body) .nil))
                targetSuffix)
            nestedReceipt.targetFill
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      rw [List.nodup_cons] at childrenNodup
      have childMember := childrenSubset child (by simp)
      have bodyLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env :
              Env pre
                (targetContext source removed
                  (context.extend region)).sigs),
            denoteRegion pre definitionEnv env targetBody ↔
              denoteRegion pre definitionEnv
                (Env.comp env
                  (contextRenaming source removed (context.extend region)))
                sourceBody :=
        compileRegion_equiv_outside source removed candidateWellFormed fuel
          (context.extend region) child (allAbove child childMember)
          (outsideOther child childMember different)
          sourceBodyCompiled targetBodyCompiled
      exact
        induction
          (fun candidate member =>
            childrenSubset candidate
              (List.mem_cons_of_mem child member))
          childrenNodup.2
          (List.mem_of_ne_of_mem (Ne.symm different) selectedMember)
          (by
            intro pre definitionEnv env
            simp only [denoteItemSeq_append, denoteItemSeq_cons,
              denoteItemSeq_nil, and_true, cut_denotes_negation]
            exact and_congr (leadingLaw pre definitionEnv env)
              (not_congr (bodyLaw pre definitionEnv env)))

private theorem envComp_erasureRebaseAbove
    {left right sourceSigs : List Sig}
    (same : left = right)
    (rho : WireRenaming sourceSigs left) :
    (fun (pre : PreModel.{u}) (env : Env pre right) =>
      Env.comp (same.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre right) =>
        Env.comp env (same ▸ rho)) := by
  cases same
  rfl

/--
Truncate one erasure provenance at an enclosing scope and replay only the
strict ancestors above that scope.
-/
theorem ErasureFrameProvenance.aboveScope
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {region : source.val.RegionId}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)}
    (provenance :
      ErasureFrameProvenance source removed
        (source.val.nodes removed).region fuel sourceOuter region sourceFrame
        targetFrame)
    (scope : source.val.RegionId)
    (regionScope : source.val.Encloses region scope)
    (scopeSite :
      source.val.Encloses scope (source.val.nodes removed).region) :
    Nonempty
      (ErasureAboveScopeReceipt.{u} source removed scope sourceOuter
        sourceFrame targetFrame) := by
  induction provenance generalizing scope with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      sourceBodyCompiled targetBodyCompiled =>
      have same :
          (source.val.nodes removed).region = scope :=
        factor_encloses_antisymm definitions source.val source.property
          regionScope scopeSite
      subst scope
      exact
        ErasureFrameProvenance.stopAboveCurrent
          (.site childFuel sourceOuter sourceBody targetBody sourceAbove
            sourceBodyCompiled targetBodyCompiled)
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes targetNodes sourceNested sourceAround targetNested
      targetAround sourceNodesCompiled targetNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
      siblings nested induction =>
      by_cases currentScope : region = scope
      · subst scope
        exact
          ErasureFrameProvenance.stopAboveCurrent
            (.ancestor childFuel sourceOuter region selected notSite
              sourceAbove sourceNodes targetNodes sourceNested sourceAround
              targetNested targetAround sourceNodesCompiled
              targetNodesCompiled selectedFound sourceNestedCompiled
              sourceAroundCompiled targetAroundCompiled siblings nested)
      · have selectedMember :
            selected ∈ source.val.childrenOf region :=
          List.mem_of_find?_eq_some selectedFound
        have selectedData :
            source.val.regions selected = .cut region :=
          ConcreteElaboration.mem_childrenOf source.val region selected
            selectedMember
        have selectedSite :
            source.val.Encloses selected
              (source.val.nodes removed).region :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide
                  (source.val.Encloses candidate
                    (source.val.nodes removed).region))
              selectedFound)
        have selectedScope :
            source.val.Encloses selected scope :=
          selected_child_encloses_scope definitions source.val
            source.property regionScope (Ne.symm currentScope) selectedData
            selectedSite scopeSite
        obtain ⟨nestedReceipt⟩ :=
          induction scope selectedScope scopeSite
        have sourceExtendedNodup :
            (sourceOuter.extend region).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions source.val
            source.property sourceOuter region sourceAbove
        have childrenNodup :
            (source.val.childrenOf region).Nodup := by
          unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
          exact
            (Data.Finite.allFin_nodup source.val.regionCount).filter _
        have allAbove :
            ∀ child, child ∈ source.val.childrenOf region →
              ConcreteElaboration.ContextAbove source.val
                (sourceOuter.extend region) child := by
          intro child member
          exact
            ConcreteElaboration.extend_above_child definitions source.val
              source.property sourceOuter region child sourceAbove
              (ConcreteElaboration.mem_childrenOf source.val region child
                member)
        have outsideOther :
            ∀ child, child ∈ source.val.childrenOf region →
              child ≠ selected →
                ¬source.val.Encloses child
                  (source.val.nodes removed).region := by
          intro child member different childSite
          exact different
            (enclosing_children_unique source region child selected
              (source.val.nodes removed).region member selectedMember
              childSite
              (by
                exact
                  of_decide_eq_true
                    (List.find?_some
                      (p := fun candidate =>
                        decide
                          (source.val.Encloses candidate
                            (source.val.nodes removed).region))
                      selectedFound)))
        have leadingLaw :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (targetContext source removed
                    (sourceOuter.extend region)).sigs),
              denoteItemSeq pre definitionEnv env targetNodes ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                    (contextRenaming source removed
                      (sourceOuter.extend region)))
                  sourceNodes := by
          intro pre definitionEnv env
          exact
            compiledNodes_outside source removed candidateWellFormed
              (sourceOuter.extend region) sourceExtendedNodup region
              (removed_not_mem_nodesAt_of_ne source removed region notSite)
              sourceNodesCompiled targetNodesCompiled pre definitionEnv env
        obtain ⟨aroundReceipt⟩ :=
          siblings.aboveScope candidateWellFormed sourceOuter region selected
            scope (fun _ member => member) childrenNodup selectedMember
            allAbove outsideOther nestedReceipt leadingLaw
        let contextExact :=
          targetContext_extend source removed sourceOuter region
        let outerSigsExact :=
          congrArg ConcreteElaboration.WireContext.sigs contextExact
        let rebasedTarget :=
          erasureRebaseRegionFrame contextExact targetAround
        have rebasedZipperRaw :=
          aroundReceipt.zipper.rebaseTargetOuter
            outerSigsExact aroundReceipt.targetAbove
        have outerMapEquality :
            (fun (pre : PreModel.{u})
              (env :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed region)).sigs) =>
              Env.comp
                (outerSigsExact.symm ▸ env)
                (contextRenaming source removed
                  (sourceOuter.extend region))) =
            (fun (pre : PreModel.{u})
              (env :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed region)).sigs) =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter
                  region)) := by
          simpa [extendedContextRenaming] using
            (envComp_erasureRebaseAbove
              outerSigsExact
              (contextRenaming source removed
                (sourceOuter.extend region)))
        have rebasedZipper :
            DiagramContext.SemanticZipper
              aroundReceipt.sourceAbove
              (outerSigsExact ▸ aroundReceipt.targetAbove)
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (extendedContextRenaming source removed sourceOuter region))
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (contextRenaming source removed
                    aroundReceipt.sourceSiteOuter)) := by
          rw [← outerMapEquality]
          exact rebasedZipperRaw
        let sourceAncestor :=
          bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt region) aroundReceipt.sourceAbove
        let targetAncestor :=
          bindContextFor (Target source removed)
            (targetContext source removed sourceOuter).ids
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            (outerSigsExact ▸ aroundReceipt.targetAbove)
        have ancestorZipper :
            DiagramContext.SemanticZipper sourceAncestor targetAncestor
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (contextRenaming source removed sourceOuter))
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (contextRenaming source removed
                    aroundReceipt.sourceSiteOuter)) := by
          apply erasureBindContextZipper removed sourceOuter region
            sourceExtendedNodup
          exact rebasedZipper
        refine
          ⟨{
            sourceSiteOuter := aroundReceipt.sourceSiteOuter
            sourceAbove := sourceAncestor
            targetAbove := targetAncestor
            sourceBody := aroundReceipt.sourceBody
            targetBody := aroundReceipt.targetBody
            sourceFill := ?_
            targetFill := ?_
            zipper := ancestorZipper
          }⟩
        · change
            (bindContextFor source.val sourceOuter.ids
                (source.val.wiresAt region) sourceAround.context).fill
                  sourceAround.siteBody =
              sourceAncestor.fill
                (ConcreteElaboration.finishRegion source.val
                  aroundReceipt.sourceSiteOuter scope
                  aroundReceipt.sourceBody)
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          unfold sourceAncestor
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          exact
            congrArg
              (ConcreteElaboration.finishRegion source.val sourceOuter
                region)
              aroundReceipt.sourceFill
        · change
            (bindContextFor (Target source removed)
                (targetContext source removed sourceOuter).ids
                ((Target source removed).wiresAt
                  (targetRegion source removed region))
                rebasedTarget.context).fill rebasedTarget.siteBody =
              targetAncestor.fill
                (ConcreteElaboration.finishRegion (Target source removed)
                  (targetContext source removed
                    aroundReceipt.sourceSiteOuter)
                  (targetRegion source removed scope)
                  aroundReceipt.targetBody)
          unfold targetAncestor
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion,
            bindContextFor_fill, finishBodyFor_eq_finishRegion]
          unfold rebasedTarget
          apply congrArg
            (ConcreteElaboration.finishRegion (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed region))
          calc
            (erasureRebaseRegionFrame contextExact
                targetAround).context.fill
                (erasureRebaseRegionFrame contextExact
                  targetAround).siteBody =
                outerSigsExact ▸
                  targetAround.context.fill targetAround.siteBody :=
              (erasureRebaseRegionFrame_fill contextExact targetAround).symm
            _ =
                outerSigsExact ▸
                  aroundReceipt.targetAbove.fill
                    (ConcreteElaboration.finishRegion (Target source removed)
                      (targetContext source removed
                        aroundReceipt.sourceSiteOuter)
                      (targetRegion source removed scope)
                      aroundReceipt.targetBody) :=
              congrArg (fun body => outerSigsExact ▸ body)
                aroundReceipt.targetFill
            _ =
                (outerSigsExact ▸ aroundReceipt.targetAbove).fill
                  (ConcreteElaboration.finishRegion (Target source removed)
                    (targetContext source removed
                      aroundReceipt.sourceSiteOuter)
                    (targetRegion source removed scope)
                    aroundReceipt.targetBody) :=
              by
                simpa only using
                  (DiagramContext.fill_rebaseOuter
                    (definitions := definitions) outerSigsExact
                    aroundReceipt.targetAbove
                    (ConcreteElaboration.finishRegion
                      (Target source removed)
                      (targetContext source removed
                        aroundReceipt.sourceSiteOuter)
                      (targetRegion source removed scope)
                      aroundReceipt.targetBody))
          all_goals rfl

/-- Canonical source-visible to target-visible erasure renaming. -/
def erasureVisibleRenaming
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)}
    (visibleExact :
      targetFrame.visible =
        targetContext source removed sourceFrame.visible) :
    WireRenaming sourceFrame.visible.sigs targetFrame.visible.sigs :=
  congrArg ConcreteElaboration.WireContext.sigs visibleExact.symm ▸
    contextRenaming source removed sourceFrame.visible

private theorem origin_cast_renaming
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (sourceContext : List Sig)
    (rho : WireRenaming sourceContext left.sigs)
    {sig : Sig}
    (value : Var sourceContext sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        ((congrArg ConcreteElaboration.WireContext.sigs same ▸ rho) value) =
      ConcreteElaboration.WireContext.origin diagram left.ids
        (rho value) := by
  cases same
  rfl

theorem erasureVisibleRenaming_origin
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)}
    (visibleExact :
      targetFrame.visible =
        targetContext source removed sourceFrame.visible)
    {sig : Sig}
    (value : Var sourceFrame.visible.sigs sig) :
    ConcreteElaboration.WireContext.origin (Target source removed)
        targetFrame.visible.ids
        (erasureVisibleRenaming removed sourceFrame visibleExact value) =
      targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          sourceFrame.visible.ids value) := by
  unfold erasureVisibleRenaming
  rw [origin_cast_renaming (Target source removed) visibleExact.symm,
    contextRenaming_action]

theorem extendedContextRenaming_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    {sig : Sig}
    (value : Var (context.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin (Target source removed)
        ((targetContext source removed context).extend
          (targetRegion source removed region)).ids
        (extendedContextRenaming source removed context region value) =
      targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          (context.extend region).ids value) := by
  unfold extendedContextRenaming
  rw [origin_cast_renaming (Target source removed)
      (targetContext_extend source removed context region),
    contextRenaming_action]

private theorem origin_injective_of_nodup
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId}
    (nodup : ids.Nodup)
    {sig : Sig}
    (left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig)
    (sameOrigin :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  have origin_mem :
      ∀ {localIds : List diagram.WireId} {localSig : Sig}
        (value :
          Var (localIds.map fun wire => (diagram.wires wire).sig)
            localSig),
        ConcreteElaboration.WireContext.origin diagram localIds value ∈
          localIds := by
    intro localIds localSig value
    induction localIds with
    | nil => exact nomatch value
    | cons head tail induction =>
        cases value with
        | here => simp [ConcreteElaboration.WireContext.origin]
        | there value =>
            exact List.mem_cons_of_mem head (induction value)
  induction ids with
  | nil => exact nomatch left
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have member := origin_mem right
              have equality :
                  head =
                    ConcreteElaboration.WireContext.origin
                      diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [← equality] at member
              exact (nodup.1 member).elim
      | there left =>
          cases right with
          | here =>
              have member := origin_mem left
              have equality :
                  ConcreteElaboration.WireContext.origin diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [equality] at member
              exact (nodup.1 member).elim
          | there right =>
              exact congrArg Var.there
                (induction nodup.2 left right (by
                  simpa [ConcreteElaboration.WireContext.origin] using
                    sameOrigin))

/--
Strict erasure frames commute with the structural outer-variable embedding.
The proof is owned by the two compiler receipts and the canonical erasure
renamings; callers only supply the target visible-context uniqueness fact.
-/
theorem PairedInnerFrame.liftOuter_erasureVisibleRenaming
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    (site region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter))
    (paired :
      PairedInnerFrame source removed region sourceOuter sourceFrame
        targetFrame)
    (notSite : region ≠ site)
    (sourceCompiled :
      compileRegionFrame? definitions source.val site fuel region
          sourceOuter =
        some sourceFrame)
    (targetCompiled :
      compileRegionFrame? definitions (Target source removed)
          (targetRegion source removed site) fuel
          (targetRegion source removed region)
          (targetContext source removed sourceOuter) =
        some targetFrame)
    (visibleExact :
      targetFrame.visible =
        targetContext source removed sourceFrame.visible)
    (targetVisibleNodup : targetFrame.visible.ids.Nodup)
    {sig : Sig}
    (value : Var (sourceOuter.extend region).sigs sig) :
    DiagramContext.liftOuter paired.targetInner
        (extendedContextRenaming source removed sourceOuter region value) =
      erasureVisibleRenaming removed sourceFrame visibleExact
        (DiagramContext.liftOuter paired.sourceInner value) := by
  apply origin_injective_of_nodup (Target source removed)
    targetVisibleNodup
  calc
    _ =
        ConcreteElaboration.WireContext.origin (Target source removed)
          ((targetContext source removed sourceOuter).extend
            (targetRegion source removed region)).ids
          (extendedContextRenaming source removed sourceOuter region
            value) :=
      compileRegionFrame?_strict_inner_liftOuter_origin definitions
        (Target source removed) (targetRegion source removed site) fuel
        (targetRegion source removed region)
        (targetContext source removed sourceOuter) targetFrame
        paired.targetInner
        (fun same => notSite (targetRegion_injective source removed same))
        targetCompiled paired.targetDecomposition _
    _ = targetWire source removed
          (ConcreteElaboration.WireContext.origin source.val
            (sourceOuter.extend region).ids value) :=
      extendedContextRenaming_origin source removed sourceOuter region value
    _ = targetWire source removed
          (ConcreteElaboration.WireContext.origin source.val
            sourceFrame.visible.ids
            (DiagramContext.liftOuter paired.sourceInner value)) := by
      rw [compileRegionFrame?_strict_inner_liftOuter_origin definitions
        source.val site fuel region sourceOuter sourceFrame
        paired.sourceInner notSite sourceCompiled
        paired.sourceDecomposition]
    _ = _ :=
      (erasureVisibleRenaming_origin removed sourceFrame visibleExact
        (DiagramContext.liftOuter paired.sourceInner value)).symm

/-- Transport a target-frame zipper across outer-context equality. -/
theorem semanticZipper_erasureRebaseTargetFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (targetFrame : RegionFrame definitions diagram left)
    {sourceContext :
      DiagramContext definitions sourceHole sourceOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre left.sigs → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetFrame.visible.sigs → Env pre sourceHole}
    (zipper :
      DiagramContext.SemanticZipper sourceContext targetFrame.context
        outerMap holeMap) :
    DiagramContext.SemanticZipper sourceContext
      (erasureRebaseRegionFrame same targetFrame).context
      (fun pre env =>
        outerMap pre
          (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ env))
      (fun pre env =>
        holeMap pre
          (congrArg ConcreteElaboration.WireContext.sigs
            (erasureRebaseRegionFrame_visible same targetFrame) ▸ env)) := by
  subst right
  exact zipper

private theorem envComp_erasureRebase
    {left right sourceSigs : List Sig}
    (same : left = right)
    (rho : WireRenaming sourceSigs left) :
    (fun (pre : PreModel.{u}) (env : Env pre right) =>
      Env.comp (same.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre right) =>
        Env.comp env (same ▸ rho)) := by
  subst right
  rfl

private def transportRenaming
    {source sourceSite target targetSite : List Sig}
    (sourceEquality : source = sourceSite)
    (targetEquality : target = targetSite)
    (rho : WireRenaming sourceSite targetSite) :
    WireRenaming source target :=
  fun {_} value => targetEquality.symm ▸ rho (sourceEquality ▸ value)

private theorem transportRenaming_source_rfl
    {source target targetSite : List Sig}
    (targetEquality : target = targetSite)
    (rho : WireRenaming source targetSite) :
    (transportRenaming (Eq.refl source) targetEquality rho :
        WireRenaming source target) =
      (targetEquality.symm ▸ rho) := by
  cases targetEquality
  rfl

private theorem transportedRegion_trans
    {diagram : ConcreteDiagram definitions.length}
    {left middle right : ConcreteElaboration.WireContext diagram}
    (first : left = middle)
    (second : middle = right)
    (leftBody : Region definitions left.sigs)
    (middleBody : Region definitions middle.sigs)
    (rightBody : Region definitions right.sigs)
    (firstBody :
      congrArg ConcreteElaboration.WireContext.sigs first ▸ leftBody =
        middleBody)
    (secondBody :
      congrArg ConcreteElaboration.WireContext.sigs second ▸ middleBody =
        rightBody) :
    congrArg ConcreteElaboration.WireContext.sigs (first.trans second) ▸
        leftBody =
      rightBody := by
  cases first
  cases second
  exact firstBody.trans secondBody

private theorem cast_symm_cast_value
    {α : Sort u} {motive : α → Sort v}
    {left right : α}
    (same : left = right)
    (value : motive left) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem replacementBodyEquiv_cast
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    {sourceLeft sourceRight :
      ConcreteElaboration.WireContext source.val}
    {targetLeft targetRight :
      ConcreteElaboration.WireContext (Target source removed)}
    (sourceSame : sourceLeft = sourceRight)
    (targetSame : targetLeft = targetRight)
    (leftExact :
      targetLeft = targetContext source removed sourceLeft)
    (rightExact :
      targetRight = targetContext source removed sourceRight)
    (sourceLeftBody : Region definitions sourceLeft.sigs)
    (sourceRightBody : Region definitions sourceRight.sigs)
    (targetLeftBody : Region definitions targetLeft.sigs)
    (targetRightBody : Region definitions targetRight.sigs)
    (sourceBodySame :
      congrArg ConcreteElaboration.WireContext.sigs sourceSame ▸
          sourceLeftBody =
        sourceRightBody)
    (targetBodySame :
      congrArg ConcreteElaboration.WireContext.sigs targetSame ▸
          targetLeftBody =
        targetRightBody)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (replacement : Region definitions targetLeft.sigs)
    (targetEnv : Env pre targetLeft.sigs)
    (canonical :
      denoteRegion pre definitionEnv
          (congrArg ConcreteElaboration.WireContext.sigs targetSame ▸
            targetEnv)
          ((congrArg ConcreteElaboration.WireContext.sigs targetSame ▸
              replacement).conjoin targetRightBody) ↔
        denoteRegion pre definitionEnv
          (Env.comp
            (congrArg ConcreteElaboration.WireContext.sigs targetSame ▸
              targetEnv)
            (congrArg ConcreteElaboration.WireContext.sigs
                rightExact.symm ▸
              contextRenaming source removed sourceRight))
          sourceRightBody) :
    denoteRegion pre definitionEnv targetEnv
        (replacement.conjoin targetLeftBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv
          (congrArg ConcreteElaboration.WireContext.sigs leftExact.symm ▸
            contextRenaming source removed sourceLeft))
        sourceLeftBody := by
  cases sourceSame
  cases targetSame
  cases sourceBodySame
  cases targetBodySame
  have exactProof : rightExact = leftExact := Subsingleton.elim _ _
  subst rightExact
  exact canonical

private theorem envComp_transportRenaming_trans
    {sourceAround sourceNested sourceSite
      targetExtended targetAround targetNested targetSite : List Sig}
    (sourceAroundNested : sourceAround = sourceNested)
    (sourceNestedSite : sourceNested = sourceSite)
    (targetExtendedAround : targetExtended = targetAround)
    (targetAroundNested : targetAround = targetNested)
    (targetNestedSite : targetNested = targetSite)
    (rho : WireRenaming sourceSite targetSite)
    (pre : PreModel.{u})
    (env : Env pre targetExtended) :
    Env.comp env
        (transportRenaming
          (sourceAroundNested.trans sourceNestedSite)
          (targetExtendedAround.trans
            (targetAroundNested.trans targetNestedSite))
          rho) =
      sourceAroundNested.symm ▸
        Env.comp
          (targetAroundNested ▸ (targetExtendedAround ▸ env))
          (transportRenaming sourceNestedSite targetNestedSite rho) := by
  cases sourceAroundNested
  cases sourceNestedSite
  cases targetExtendedAround
  cases targetAroundNested
  cases targetNestedSite
  rfl

private theorem transport_contextRenaming
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    {left right : ConcreteElaboration.WireContext source.val}
    (same : left = right) :
    (transportRenaming
          (congrArg ConcreteElaboration.WireContext.sigs same)
          (congrArg ConcreteElaboration.WireContext.sigs
            (congrArg (targetContext source removed) same))
          (contextRenaming source removed right) :
        WireRenaming left.sigs (targetContext source removed left).sigs) =
      (contextRenaming source removed left :
        WireRenaming left.sigs
          (targetContext source removed left).sigs) := by
  cases same
  rfl

private theorem transport_contextRenaming_change_source
    {source : CheckedDiagram definitions}
    (removed : source.val.NodeId)
    {sourceLeft sourceRight :
      ConcreteElaboration.WireContext source.val}
    {targetActual :
      ConcreteElaboration.WireContext (Target source removed)}
    (sourceSame : sourceLeft = sourceRight)
    (rightExact :
      targetActual = targetContext source removed sourceRight)
    (leftExact :
      targetActual = targetContext source removed sourceLeft) :
    (transportRenaming
        (congrArg ConcreteElaboration.WireContext.sigs sourceSame)
        (congrArg ConcreteElaboration.WireContext.sigs rightExact)
        (contextRenaming source removed sourceRight) :
      WireRenaming sourceLeft.sigs targetActual.sigs) =
    (transportRenaming rfl
        (congrArg ConcreteElaboration.WireContext.sigs leftExact)
        (contextRenaming source removed sourceLeft) :
      WireRenaming sourceLeft.sigs targetActual.sigs) := by
  subst sourceRight
  have sameProof : rightExact = leftExact := Subsingleton.elim _ _
  subst rightExact
  rfl

inductive ErasureFrameZippers
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (universeWitness : Type u)
    (region : source.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)) : Prop where
  | intro
    (paired :
      PairedInnerFrame source removed region sourceOuter sourceFrame
        targetFrame)
    (visibleExact :
      targetFrame.visible =
        targetContext source removed sourceFrame.visible)
    (body :
      ∀ (removedItem : Item definitions sourceFrame.visible.sigs)
        (removedCompiled :
          ConcreteElaboration.compileNodes? definitions source.val
              sourceFrame.visible [removed] =
            some (.cons removedItem .nil))
        (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (replacement : Region definitions targetFrame.visible.sigs)
        (targetEnv : Env pre targetFrame.visible.sigs),
        LocalReplacementAt source removed sourceFrame.visible
            targetFrame.visible visibleExact replacement removedItem pre
            definitionEnv targetEnv →
          (denoteRegion pre definitionEnv targetEnv
                (replacement.conjoin targetFrame.siteBody) ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (erasureVisibleRenaming removed sourceFrame visibleExact))
              sourceFrame.siteBody))
    (inner :
      DiagramContext.SemanticZipper paired.sourceInner paired.targetInner
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (extendedContextRenaming source removed sourceOuter region))
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (erasureVisibleRenaming removed sourceFrame visibleExact)))
    (full :
      DiagramContext.SemanticZipper sourceFrame.context targetFrame.context
        (fun (pre : PreModel.{u}) env =>
          Env.comp env (contextRenaming source removed sourceOuter))
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (erasureVisibleRenaming removed sourceFrame visibleExact))) :
    ErasureFrameZippers source removed universeWitness region sourceOuter
      sourceFrame targetFrame

/-- The fixed-ancestor semantic certificate is a fold over erasure provenance. -/
theorem ErasureFrameProvenance.zippers
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {region : source.val.RegionId}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions (Target source removed)
        (targetContext source removed sourceOuter)}
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (provenance :
      ErasureFrameProvenance source removed
        (source.val.nodes removed).region fuel sourceOuter region sourceFrame
        targetFrame) :
    ErasureFrameZippers source removed (PUnit : Type u) region sourceOuter
      sourceFrame targetFrame := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      sourceBodyCompiled targetBodyCompiled =>
      let sourceFrame :
          RegionFrame definitions source.val sourceOuter :=
        { visible := sourceOuter.extend (source.val.nodes removed).region
          siteBody := sourceBody
          context := bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt (source.val.nodes removed).region) .hole }
      let targetFrame :
          RegionFrame definitions (Target source removed)
            (targetContext source removed sourceOuter) :=
        { visible := (targetContext source removed sourceOuter).extend
            (targetRegion source removed
              (source.val.nodes removed).region)
          siteBody := targetBody
          context := bindContextFor (Target source removed)
            (targetContext source removed sourceOuter).ids
            ((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.nodes removed).region)) .hole }
      have visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible :=
        (targetContext_extend source removed sourceOuter
          (source.val.nodes removed).region).symm
      let paired :
          PairedInnerFrame source removed
            (source.val.nodes removed).region sourceOuter sourceFrame
            targetFrame :=
        ⟨.hole, .hole, rfl, rfl⟩
      have inner :
          DiagramContext.SemanticZipper paired.sourceInner paired.targetInner
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter
                  (source.val.nodes removed).region))
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (erasureVisibleRenaming removed sourceFrame visibleExact)) := by
        simpa [paired, sourceFrame, targetFrame, erasureVisibleRenaming,
          extendedContextRenaming] using
          (DiagramContext.SemanticZipper.hole
            (definitions := definitions)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter
                  (source.val.nodes removed).region)))
      have sourceExtendedNodup :
          (sourceOuter.extend (source.val.nodes removed).region).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions source.val
          source.property sourceOuter (source.val.nodes removed).region
          sourceAbove
      have full :=
        erasureBindContextZipper removed sourceOuter
          (source.val.nodes removed).region sourceExtendedNodup
          paired.sourceInner paired.targetInner
          (fun (pre : PreModel.{u}) env =>
            Env.comp env
              (erasureVisibleRenaming removed sourceFrame visibleExact))
          inner
      have body :
          ∀ (removedItem : Item definitions sourceFrame.visible.sigs)
            (removedCompiled :
              ConcreteElaboration.compileNodes? definitions source.val
                  sourceFrame.visible [removed] =
                some (.cons removedItem .nil))
            (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (replacement : Region definitions targetFrame.visible.sigs)
            (targetEnv : Env pre targetFrame.visible.sigs),
            LocalReplacementAt source removed sourceFrame.visible
                targetFrame.visible visibleExact replacement removedItem pre
                definitionEnv targetEnv →
              (denoteRegion pre definitionEnv targetEnv
                    (replacement.conjoin targetFrame.siteBody) ↔
                denoteRegion pre definitionEnv
                  (Env.comp targetEnv
                    (erasureVisibleRenaming removed sourceFrame visibleExact))
                  sourceFrame.siteBody) := by
        intro removedItem removedCompiled pre definitionEnv replacement
          targetEnv localAt
        have visibleProof :
            visibleExact =
              (targetContext_extend source removed sourceOuter
                (source.val.nodes removed).region).symm :=
          Subsingleton.elim _ _
        rw [visibleProof] at localAt ⊢
        have environments :=
          SingletonRemovalSemantics.env_comp_cast_renaming
            (congrArg ConcreteElaboration.WireContext.sigs
              (targetContext_extend source removed sourceOuter
                (source.val.nodes removed).region))
            (contextRenaming source removed
              (sourceOuter.extend (source.val.nodes removed).region))
            pre targetEnv
        have replacementEquiv :
            denoteRegion pre definitionEnv targetEnv replacement ↔
              denoteItem pre definitionEnv
                (Env.comp targetEnv
                  (extendedContextRenaming source removed sourceOuter
                    (source.val.nodes removed).region))
                removedItem := by
          unfold LocalReplacementAt at localAt
          constructor
          · intro replacementHolds
            exact environments.symm ▸ localAt.mp replacementHolds
          · intro removedHolds
            apply localAt.mpr
            exact environments ▸ removedHolds
        have bodyEquiv :=
          compileScopeBody_replacement source removed candidateWellFormed
            childFuel sourceOuter sourceAbove sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled replacement removedItem
            removedCompiled pre definitionEnv targetEnv replacementEquiv
        simpa [sourceFrame, targetFrame, erasureVisibleRenaming,
          extendedContextRenaming] using bodyEquiv
      exact .intro paired visibleExact body inner full
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes targetNodes sourceNested sourceAround targetNested
      targetAround sourceNodesCompiled targetNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
      siblings nested induction =>
      rcases induction with
        ⟨nestedPaired, nestedVisibleExact, nestedBody, nestedInner,
          nestedFull⟩
      have sourceExtendedNodup :
          (sourceOuter.extend region).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions source.val
          source.property sourceOuter region sourceAbove
      have selectedMember :=
        List.mem_of_find?_eq_some selectedFound
      have childrenNodup : (source.val.childrenOf region).Nodup := by
        unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
        exact (Data.Finite.allFin_nodup source.val.regionCount).filter _
      have allAbove :
          ∀ child, child ∈ source.val.childrenOf region →
            ConcreteElaboration.ContextAbove source.val
              (sourceOuter.extend region) child := by
        intro child member
        exact
          ConcreteElaboration.extend_above_child definitions source.val
            source.property sourceOuter region child sourceAbove
            (ConcreteElaboration.mem_childrenOf source.val region child
              member)
      have selectedEncloses :
          source.val.Encloses selected
            (source.val.nodes removed).region :=
        of_decide_eq_true
          (List.find?_some
            (p := fun candidate =>
              decide
                (source.val.Encloses candidate
                  (source.val.nodes removed).region))
            selectedFound)
      have outsideOther :
          ∀ child, child ∈ source.val.childrenOf region →
            child ≠ selected →
              ¬source.val.Encloses child
                (source.val.nodes removed).region := by
        intro child member different childSite
        exact different
          (enclosing_children_unique source region child selected
            (source.val.nodes removed).region member selectedMember
            childSite selectedEncloses)
      have leadingLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env :
              Env pre
                (targetContext source removed
                  (sourceOuter.extend region)).sigs),
            denoteItemSeq pre definitionEnv env targetNodes ↔
              denoteItemSeq pre definitionEnv
                (Env.comp env
                  (contextRenaming source removed
                    (sourceOuter.extend region)))
                sourceNodes := by
        intro pre definitionEnv env
        exact
          compiledNodes_outside source removed candidateWellFormed
            (sourceOuter.extend region) sourceExtendedNodup region
            (removed_not_mem_nodesAt_of_ne source removed region notSite)
            sourceNodesCompiled targetNodesCompiled pre definitionEnv env
      obtain ⟨sourceAroundVisible, targetAroundVisible, sourceAroundBody,
          targetAroundBody, aroundZipper⟩ :=
        siblings.zipper candidateWellFormed sourceOuter region selected
          (fun _ member => member) childrenNodup selectedMember allAbove
          outsideOther
          (fun (pre : PreModel.{u}) env =>
            Env.comp env
              (erasureVisibleRenaming removed sourceNested
                nestedVisibleExact))
          nestedFull leadingLaw
      have contextEquality :=
        targetContext_extend source removed sourceOuter region
      have rebasedZipperRaw :=
        semanticZipper_erasureRebaseTargetFrame contextEquality targetAround
          aroundZipper
      have rebasedZipper :
          DiagramContext.SemanticZipper sourceAround.context
            (erasureRebaseRegionFrame contextEquality targetAround).context
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter region))
            (fun (pre : PreModel.{u}) env =>
              congrArg ConcreteElaboration.WireContext.sigs
                  sourceAroundVisible.symm ▸
                Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                    targetAroundVisible ▸
                      (congrArg ConcreteElaboration.WireContext.sigs
                        (erasureRebaseRegionFrame_visible contextEquality
                          targetAround) ▸ env))
                  (erasureVisibleRenaming removed sourceNested
                    nestedVisibleExact)) := by
        have outerMapEquality :
            (fun (pre : PreModel.{u})
              (env : Env pre
                ((targetContext source removed sourceOuter).extend
                  (targetRegion source removed region)).sigs) =>
              Env.comp
                (congrArg ConcreteElaboration.WireContext.sigs
                  contextEquality.symm ▸ env)
                (contextRenaming source removed
                  (sourceOuter.extend region))) =
            (fun (pre : PreModel.{u})
              (env : Env pre
                ((targetContext source removed sourceOuter).extend
                  (targetRegion source removed region)).sigs) =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter
                  region)) := by
          simpa [extendedContextRenaming] using
            (envComp_erasureRebase
              (congrArg ConcreteElaboration.WireContext.sigs
                contextEquality)
              (contextRenaming source removed
                (sourceOuter.extend region)))
        rw [← outerMapEquality]
        exact rebasedZipperRaw
      let finalSource :
          RegionFrame definitions source.val sourceOuter :=
        { visible := sourceAround.visible
          siteBody := sourceAround.siteBody
          context := bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt region) sourceAround.context }
      let finalTarget :
          RegionFrame definitions (Target source removed)
            (targetContext source removed sourceOuter) :=
        { visible :=
            (erasureRebaseRegionFrame contextEquality targetAround).visible
          siteBody :=
            (erasureRebaseRegionFrame contextEquality targetAround).siteBody
          context := bindContextFor (Target source removed)
            (targetContext source removed sourceOuter).ids
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            (erasureRebaseRegionFrame contextEquality targetAround).context }
      have visibleExact :
          finalTarget.visible =
            targetContext source removed finalSource.visible := by
        change
          (erasureRebaseRegionFrame contextEquality targetAround).visible =
            targetContext source removed sourceAround.visible
        exact
          (erasureRebaseRegionFrame_visible contextEquality targetAround).trans
            (targetAroundVisible.trans
              (nestedVisibleExact.trans
                (congrArg (targetContext source removed)
                  sourceAroundVisible.symm)))
      have sourceFinalVisible :
          finalSource.visible = sourceNested.visible := by
        simpa [finalSource] using sourceAroundVisible
      have targetRebaseVisible :
          finalTarget.visible = targetAround.visible := by
        simpa [finalTarget] using
          erasureRebaseRegionFrame_visible contextEquality targetAround
      have targetFinalVisible :
          finalTarget.visible = targetNested.visible :=
        targetRebaseVisible.trans targetAroundVisible
      have sourceFinalBody :
          congrArg ConcreteElaboration.WireContext.sigs sourceFinalVisible ▸
              finalSource.siteBody =
            sourceNested.siteBody := by
        simpa [finalSource] using sourceAroundBody
      have targetRebaseBody :
          congrArg ConcreteElaboration.WireContext.sigs
                targetRebaseVisible ▸
              finalTarget.siteBody =
            targetAround.siteBody := by
        simpa [finalTarget] using
          erasureRebaseRegionFrame_siteBody contextEquality targetAround
      have targetFinalBody :
          congrArg ConcreteElaboration.WireContext.sigs targetFinalVisible ▸
              finalTarget.siteBody =
            targetNested.siteBody :=
        transportedRegion_trans targetRebaseVisible targetAroundVisible
          finalTarget.siteBody targetAround.siteBody targetNested.siteBody
          targetRebaseBody targetAroundBody
      let paired :
          PairedInnerFrame source removed region sourceOuter finalSource
            finalTarget :=
        ⟨sourceAround.context,
          (erasureRebaseRegionFrame contextEquality targetAround).context,
          rfl, rfl⟩
      have inner :
          DiagramContext.SemanticZipper paired.sourceInner paired.targetInner
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (extendedContextRenaming source removed sourceOuter region))
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (erasureVisibleRenaming removed finalSource
                  visibleExact)) := by
        have holeMapEquality :
            (fun (pre : PreModel.{u})
              (env :
                Env pre
                  (erasureRebaseRegionFrame contextEquality
                    targetAround).visible.sigs) =>
              Env.comp env
                (erasureVisibleRenaming removed finalSource
                  visibleExact)) =
            (fun (pre : PreModel.{u})
              (env :
                Env pre
                  (erasureRebaseRegionFrame contextEquality
                    targetAround).visible.sigs) =>
              congrArg ConcreteElaboration.WireContext.sigs
                  sourceAroundVisible.symm ▸
                Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                    targetAroundVisible ▸
                      (congrArg ConcreteElaboration.WireContext.sigs
                        (erasureRebaseRegionFrame_visible contextEquality
                          targetAround) ▸ env))
                  (erasureVisibleRenaming removed sourceNested
                    nestedVisibleExact)) := by
          funext pre env sig value
          have composed :=
            envComp_transportRenaming_trans
              (congrArg ConcreteElaboration.WireContext.sigs
                sourceAroundVisible)
              rfl
              (congrArg ConcreteElaboration.WireContext.sigs
                (erasureRebaseRegionFrame_visible contextEquality
                  targetAround))
              (congrArg ConcreteElaboration.WireContext.sigs
                targetAroundVisible)
              (congrArg ConcreteElaboration.WireContext.sigs
                nestedVisibleExact)
              (contextRenaming source removed sourceNested.visible)
              pre env
          have rightExact :
              (erasureRebaseRegionFrame contextEquality
                  targetAround).visible =
                targetContext source removed sourceNested.visible :=
            (erasureRebaseRegionFrame_visible contextEquality
              targetAround).trans
                (targetAroundVisible.trans nestedVisibleExact)
          have leftExact :
              (erasureRebaseRegionFrame contextEquality
                  targetAround).visible =
                targetContext source removed sourceAround.visible := by
            simpa [finalSource, finalTarget] using visibleExact
          have transported :=
            transport_contextRenaming_change_source removed
              sourceAroundVisible rightExact leftExact
          have compTransported :=
            congrArg
              (fun rho : WireRenaming sourceAround.visible.sigs
                  (erasureRebaseRegionFrame contextEquality
                    targetAround).visible.sigs =>
                Env.comp env rho)
              transported
          have combined := compTransported.symm.trans composed
          have targetOnly :=
            transportRenaming_source_rfl
              (congrArg ConcreteElaboration.WireContext.sigs leftExact)
              (contextRenaming source removed sourceAround.visible)
          have compTargetOnly :=
            congrArg
              (fun rho : WireRenaming sourceAround.visible.sigs
                  (erasureRebaseRegionFrame contextEquality
                    targetAround).visible.sigs =>
                Env.comp env rho)
              targetOnly
          have finalCombined := compTargetOnly.symm.trans combined
          simpa [erasureVisibleRenaming, finalSource,
            transportRenaming_source_rfl] using
            congrFun (congrFun finalCombined sig) value
        rw [holeMapEquality]
        simpa [paired, finalSource, finalTarget] using rebasedZipper
      have full :=
        erasureBindContextZipper removed sourceOuter region
          sourceExtendedNodup paired.sourceInner paired.targetInner
          (fun (pre : PreModel.{u}) env =>
            Env.comp env
              (erasureVisibleRenaming removed finalSource visibleExact))
          inner
      exact .intro paired visibleExact (by
        intro removedItem removedCompiled pre definitionEnv replacement
          targetEnv localAt
        let nestedReplacement :
            Region definitions targetNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            targetFinalVisible ▸ replacement
        let nestedRemovedItem :
            Item definitions sourceNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            sourceFinalVisible ▸ removedItem
        let nestedTargetEnv :
            Env pre targetNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            targetFinalVisible ▸ targetEnv
        have nestedRemovedCompiled :
            ConcreteElaboration.compileNodes? definitions source.val
                sourceNested.visible [removed] =
              some (.cons nestedRemovedItem .nil) := by
          have casted :=
            compileNodes_cast_context source.val sourceFinalVisible
              [removed] removedCompiled
          rw [cast_itemSeq_singleton] at casted
          exact casted
        have nestedLocal :
            LocalReplacementAt source removed sourceNested.visible
              targetNested.visible nestedVisibleExact nestedReplacement
              nestedRemovedItem pre definitionEnv nestedTargetEnv := by
          apply
            LocalReplacementAt.cast source removed sourceFinalVisible
              targetFinalVisible visibleExact nestedVisibleExact replacement
              removedItem pre definitionEnv nestedTargetEnv
          have environmentTransport :
              congrArg ConcreteElaboration.WireContext.sigs
                    targetFinalVisible.symm ▸
                  nestedTargetEnv =
                targetEnv := by
            unfold nestedTargetEnv
            exact
              cast_symm_cast_value
                (congrArg ConcreteElaboration.WireContext.sigs
                  targetFinalVisible)
                targetEnv
          rw [environmentTransport]
          exact localAt
        have nestedEquiv :=
          nestedBody nestedRemovedItem nestedRemovedCompiled pre
            definitionEnv nestedReplacement nestedTargetEnv nestedLocal
        simpa [erasureVisibleRenaming] using
          (replacementBodyEquiv_cast removed sourceFinalVisible
            targetFinalVisible visibleExact nestedVisibleExact
            finalSource.siteBody sourceNested.siteBody finalTarget.siteBody
            targetNested.siteBody sourceFinalBody targetFinalBody pre
            definitionEnv replacement targetEnv nestedEquiv)) inner full

/--
Retain the paired contexts immediately inside any enclosing region's binders.
The semantic receipt is eliminated from the generated provenance zipper.
-/
theorem PairedGeneratedFrame.enclosing_replacement_receipt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions (Target source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions (Target source removed)
          (targetRegion source removed (source.val.nodes removed).region)
          fuel (targetRegion source removed region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ replacement : Region definitions targetFrame.visible.sigs,
          ∃ inner :
              PairedInnerFrame source removed region sourceOuter sourceFrame
                targetFrame,
            inner.ReplacementDenotation visibleExact replacement removedItem
              pre definitionEnv := by
  rcases paired with
    ⟨targetFrame, sourceAbove, sourceGenerated, provenance⟩
  have targetGenerated := provenance.targetGenerated
  have zippers :=
    provenance.zippers erasure.candidate_wellFormed
  rcases zippers with
    ⟨innerFrame, visibleExact, body, inner, full⟩
  refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
  intro replacement
  refine ⟨innerFrame, ?_⟩
  intro fixedTargetEnv localLaw
  apply
    inner.equivalence pre definitionEnv sourceFrame.siteBody
      (replacement.conjoin targetFrame.siteBody) fixedTargetEnv
  intro descendant preserves
  exact
    body removedItem removedCompiled pre definitionEnv replacement descendant
      (localLaw descendant preserves)

/-- The site-scope specialization of the provenance body certificate. -/
theorem PairedGeneratedFrame.fixedScope_replacement_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region
        (source.val.nodes removed).region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions (Target source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions (Target source removed)
          (targetRegion source removed (source.val.nodes removed).region)
          fuel
          (targetRegion source removed (source.val.nodes removed).region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ (replacement : Region definitions targetFrame.visible.sigs)
          (targetVisibleEnv : Env pre targetFrame.visible.sigs),
          (denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
            denoteItem pre definitionEnv
              (Env.comp
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleExact ▸
                  targetVisibleEnv)
                (contextRenaming source removed sourceFrame.visible))
              removedItem) →
          (denoteRegion pre definitionEnv targetVisibleEnv
                (replacement.conjoin targetFrame.siteBody) ↔
            denoteRegion pre definitionEnv
              (Env.comp
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleExact ▸
                  targetVisibleEnv)
                (contextRenaming source removed sourceFrame.visible))
              sourceFrame.siteBody) := by
  rcases paired with
    ⟨targetFrame, sourceAbove, sourceGenerated, provenance⟩
  have targetGenerated := provenance.targetGenerated
  have zippers :=
    provenance.zippers erasure.candidate_wellFormed
  rcases zippers with
    ⟨innerFrame, visibleExact, body, inner, full⟩
  refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
  intro replacement targetVisibleEnv localAt
  have bodyEquiv :=
    body removedItem removedCompiled pre definitionEnv replacement
      targetVisibleEnv localAt
  have environments :=
    env_comp_cast_renaming
      (congrArg ConcreteElaboration.WireContext.sigs visibleExact.symm)
      (contextRenaming source removed sourceFrame.visible) pre
      targetVisibleEnv
  constructor
  · intro targetHolds
    exact environments ▸ bodyEquiv.mp targetHolds
  · intro sourceHolds
    exact bodyEquiv.mpr (environments.symm ▸ sourceHolds)

/-- Whole-frame replacement semantics is the full provenance zipper eliminator. -/
theorem PairedGeneratedFrame.replacement_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions (Target source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions (Target source removed)
          (targetRegion source removed (source.val.nodes removed).region)
          fuel (targetRegion source removed region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ replacement : Region definitions targetFrame.visible.sigs,
          (∀ targetVisibleEnv : Env pre targetFrame.visible.sigs,
            denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
              denoteItem pre definitionEnv
                (Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                      visibleExact ▸
                    targetVisibleEnv)
                  (contextRenaming source removed sourceFrame.visible))
                removedItem) →
          ∀ targetOuterEnv :
              Env pre (targetContext source removed sourceOuter).sigs,
            denoteRegion pre definitionEnv targetOuterEnv
                (targetFrame.context.fill
                  (replacement.conjoin targetFrame.siteBody)) ↔
              denoteRegion pre definitionEnv
                (Env.comp targetOuterEnv
                  (contextRenaming source removed sourceOuter))
                (sourceFrame.context.fill sourceFrame.siteBody) := by
  rcases paired with
    ⟨targetFrame, sourceAbove, sourceGenerated, provenance⟩
  have targetGenerated := provenance.targetGenerated
  have zippers :=
    provenance.zippers erasure.candidate_wellFormed
  rcases zippers with
    ⟨innerFrame, visibleExact, body, inner, full⟩
  refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
  intro replacement localLaw targetOuterEnv
  apply
    full.equivalence pre definitionEnv sourceFrame.siteBody
      (replacement.conjoin targetFrame.siteBody) targetOuterEnv
  intro descendant preserves
  exact
    body removedItem removedCompiled pre definitionEnv replacement descendant
      (localLaw descendant)

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
