import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsFrameNaturality
import VisualProof.Diagram.Concrete.WirePrimitive.ContentAlignment
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityRecursive

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteElaboration
open ConcreteWireQuantifier

private def rebaseContextOuter
    (same : leftOuter = rightOuter)
    (context : DiagramContext definitions hole leftOuter) :
    DiagramContext definitions hole rightOuter :=
  same ▸ context

private def rebaseContextHole
    (same : leftHole = rightHole)
    (context : DiagramContext definitions leftHole outer) :
    DiagramContext definitions rightHole outer :=
  same ▸ context

private theorem cast_bindMany_hole_local
    (bound outer : List Sig)
    (same : source = bound ++ outer) :
    same ▸
        (DiagramContext.bindMany bound
          (same ▸
            (.hole : DiagramContext definitions source source))) =
      DiagramContext.bindMany bound
        (.hole : DiagramContext definitions
          (bound ++ outer) (bound ++ outer)) := by
  cases same
  rfl

private theorem rebase_bindContextFor_hole_local
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (rightOuter : List Sig)
    (outerExact :
      (outerIds.map fun wire => (diagram.wires wire).sig) = rightOuter)
    (visibleExact :
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig) =
        (localIds.map fun wire => (diagram.wires wire).sig) ++ rightOuter) :
    rebaseContextHole visibleExact
        (rebaseContextOuter outerExact
          (bindContextFor diagram outerIds localIds
            (.hole : DiagramContext definitions
              ((localIds ++ outerIds).map
                fun wire => (diagram.wires wire).sig)
              ((localIds ++ outerIds).map
                fun wire => (diagram.wires wire).sig)))) =
      DiagramContext.bindMany
        (localIds.map fun wire => (diagram.wires wire).sig)
        (.hole : DiagramContext definitions
          ((localIds.map fun wire => (diagram.wires wire).sig) ++ rightOuter)
          ((localIds.map fun wire => (diagram.wires wire).sig) ++
            rightOuter)) := by
  rw [bindContextFor_eq_bindMany]
  unfold rebaseContextHole rebaseContextOuter
  cases outerExact
  exact cast_bindMany_hole_local _ _ _

private def rebaseItemSeq
    (same : left = right)
    (items : ItemSeq definitions left) : ItemSeq definitions right :=
  same ▸ items

private theorem rebaseContextHole_surroundCut
    (same : leftHole = rightHole)
    (leading suffix : ItemSeq definitions outer)
    (inner : DiagramContext definitions leftHole outer) :
    rebaseContextHole same (.surround leading (.cut inner) suffix) =
      .surround leading (.cut (rebaseContextHole same inner)) suffix := by
  cases same
  rfl

private theorem rebaseContext_surroundCut
    (holeExact : leftHole = rightHole)
    (outerExact : leftOuter = rightOuter)
    (leading suffix : ItemSeq definitions leftOuter)
    (inner : DiagramContext definitions leftHole leftOuter) :
    rebaseContextHole holeExact
        (rebaseContextOuter outerExact
          (.surround leading (.cut inner) suffix)) =
      .surround (rebaseItemSeq outerExact leading)
        (.cut
          (rebaseContextHole holeExact
            (rebaseContextOuter outerExact inner)))
        (rebaseItemSeq outerExact suffix) := by
  cases holeExact
  cases outerExact
  rfl

private theorem rebase_bindContextFor_inner_local
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (rightLocal rightOuter : List Sig)
    (outerExact :
      (outerIds.map fun wire => (diagram.wires wire).sig) = rightOuter)
    (localExact :
      (localIds.map fun wire => (diagram.wires wire).sig) = rightLocal)
    (extendedExact :
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig) =
        rightLocal ++ rightOuter)
    (holeExact : leftHole = rightHole)
    (inner : DiagramContext definitions leftHole
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig)) :
    rebaseContextHole holeExact
        (rebaseContextOuter outerExact
          (bindContextFor diagram outerIds localIds inner)) =
      DiagramContext.bindMany rightLocal
        (rebaseContextHole holeExact
          (rebaseContextOuter extendedExact inner)) := by
  rw [bindContextFor_eq_bindMany]
  unfold rebaseContextHole rebaseContextOuter
  cases outerExact
  cases localExact
  have extendedProofExact :
      extendedExact =
        @List.map_append _ _
          (fun wire => (diagram.wires wire).sig) localIds outerIds :=
    Subsingleton.elim _ _
  cases extendedProofExact
  cases holeExact
  rfl

private noncomputable def ContentAlignment.PairedContext.rebaseOuter
    (same : leftOuter = rightOuter)
    {sourceInner : DiagramContext definitions
      (sourceLocal ++ siteOuter) leftOuter}
    {targetInner : DiagramContext definitions
      (targetLocal ++ siteOuter) leftOuter}
    (paired : ContentAlignment.PairedContext definitions
      sourceLocal targetLocal siteOuter sourceInner targetInner) :
    ContentAlignment.PairedContext definitions
      sourceLocal targetLocal siteOuter
      (rebaseContextOuter same sourceInner)
      (rebaseContextOuter same targetInner) := by
  cases same
  exact paired

private theorem rebaseContext_outer_trans_hole
    (holeExact : leftHole = rightHole)
    (first : leftOuter = middleOuter)
    (second : middleOuter = rightOuter)
    (inner : DiagramContext definitions leftHole leftOuter) :
    rebaseContextHole holeExact
        (rebaseContextOuter (first.trans second) inner) =
      rebaseContextOuter second
        (rebaseContextHole holeExact
          (rebaseContextOuter first inner)) := by
  cases holeExact
  cases first
  cases second
  rfl

private def rebaseSiteBody
    (outer : ConcreteElaboration.WireContext diagram)
    (left right : diagram.RegionId)
    (same : left = right)
    (body : Region definitions (outer.extend left).sigs) :
    Region definitions (outer.extend right).sigs := by
  cases same
  exact body

private theorem siteFrame_reindex
    (diagram : ConcreteDiagram definitions.length)
    (outer : WireContext diagram)
    (left right : diagram.RegionId)
    (same : left = right)
    (body : Region definitions (outer.extend left).sigs) :
    ({ visible := outer.extend left
       siteBody := body
       context := bindContextFor diagram outer.ids (diagram.wiresAt left)
         .hole } : RegionFrame definitions diagram outer) =
      { visible := outer.extend right
        siteBody := rebaseSiteBody outer left right same body
        context := bindContextFor diagram outer.ids (diagram.wiresAt right)
          .hole } := by
  cases same
  rfl

private theorem encloses_trans_local
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram outer middle).mp
      outerMiddle
  obtain ⟨innerSteps, innerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram middle inner).mp
      middleInner
  have combined :
      diagram.climb (innerSteps.val + outerSteps.val) inner = some outer := by
    rw [ConcreteDiagram.climb_add, innerClimb]
    exact outerClimb
  have bounded :=
    ConcreteElaboration.successfulClimb_le_count definitions diagram
      wellFormed (innerSteps.val + outerSteps.val) inner outer combined
  apply (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
  exact ⟨⟨innerSteps.val + outerSteps.val, by omega⟩, combined⟩

private theorem rebaseItemSeq_append_cut
    (same : target = source)
    (sourceLeading : ItemSeq definitions source)
    (targetLeading : ItemSeq definitions target)
    (sourceBody : Region definitions source)
    (targetBody : Region definitions target)
    (leadingExact : rebaseItemSeq same targetLeading = sourceLeading)
    (bodyExact : same ▸ targetBody = sourceBody) :
    rebaseItemSeq same
        (targetLeading.append (.cons (.cut targetBody) .nil)) =
      sourceLeading.append (.cons (.cut sourceBody) .nil) := by
  cases same
  have leadingExact' : targetLeading = sourceLeading := by
    simpa [rebaseItemSeq] using leadingExact
  have bodyExact' : targetBody = sourceBody := by simpa using bodyExact
  subst targetLeading
  subst targetBody
  rfl

private theorem rebaseItemSeq_cons_cut
    (same : target = source)
    (sourceHead : Region definitions source)
    (targetHead : Region definitions target)
    (sourceTail : ItemSeq definitions source)
    (targetTail : ItemSeq definitions target)
    (headExact : same ▸ targetHead = sourceHead)
    (tailExact : rebaseItemSeq same targetTail = sourceTail) :
    rebaseItemSeq same (.cons (.cut targetHead) targetTail) =
      (.cons (.cut sourceHead) sourceTail : ItemSeq definitions source) := by
  cases same
  have headExact' : targetHead = sourceHead := by simpa using headExact
  have tailExact' : targetTail = sourceTail := by
    simpa [rebaseItemSeq] using tailExact
  subst targetHead
  subst targetTail
  rfl

private theorem rebaseItemSeq_nil
    (same : target = source) :
    rebaseItemSeq same (.nil : ItemSeq definitions target) =
      (.nil : ItemSeq definitions source) := by
  cases same
  rfl

private theorem compileChildren_reindexed_outside
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (fuel : Nat)
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (children : List source.val.RegionId)
    (targetAbove : ∀ child, child ∈ children →
      ContextAbove result.checked.val targetContext
        (result.regionImage child))
    (outside : ∀ child, child ∈ children →
      ¬source.val.Encloses (source.val.wires wire).scope child ∧
      ¬source.val.Encloses child (source.val.wires wire).scope)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      compileChildrenWith? definitions source.val
          (compileRegion? definitions source.val fuel)
          sourceContext children = some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      compileChildrenWith? definitions result.checked.val
          (compileRegion? definitions result.checked.val fuel)
          targetContext (children.map result.regionImage) =
        some targetItems ∧
      rebaseItemSeq context.sigs_exact targetItems = sourceItems := by
  induction children generalizing sourceItems with
  | nil =>
      have sourceExact : sourceItems = .nil :=
        (Option.some.inj sourceCompiled).symm
      subst sourceItems
      exact ⟨.nil, rfl, rebaseItemSeq_nil context.sigs_exact⟩
  | cons child tail induction =>
      obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsExact⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions source.val
          (compileRegion? definitions source.val fuel)
          sourceContext child tail sourceItems sourceCompiled
      subst sourceItems
      obtain ⟨targetHead, targetHeadCompiled, targetHeadExact⟩ :=
        ArgumentResult.RetainedContext.compileRegion_reindexed_outside
          result localized fuel child
          sourceContext targetContext context
          (targetAbove child (by simp))
          (outside child (by simp)).1 (outside child (by simp)).2
          sourceHeadCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailExact⟩ :=
        induction
          (by
            intro candidate member
            exact targetAbove candidate (by simp [member]))
          (by
            intro candidate member
            exact outside candidate (by simp [member]))
          sourceTailCompiled
      refine ⟨.cons (.cut targetHead) targetTail, ?_, ?_⟩
      · simp [compileChildrenWith?, targetHeadCompiled, targetTailCompiled]
      · exact rebaseItemSeq_cons_cut context.sigs_exact sourceHead targetHead
          sourceTail targetTail targetHeadExact targetTailExact

private noncomputable def ContentAlignment.PairedContext.bindMany
    (bound : List Sig)
    {sourceInner : DiagramContext definitions
      (sourceLocal ++ siteOuter) (bound ++ outer)}
    {targetInner : DiagramContext definitions
      (targetLocal ++ siteOuter) (bound ++ outer)}
    (paired : ContentAlignment.PairedContext definitions
      sourceLocal targetLocal siteOuter sourceInner targetInner) :
    ContentAlignment.PairedContext definitions
      sourceLocal targetLocal siteOuter
      (DiagramContext.bindMany bound sourceInner)
      (DiagramContext.bindMany bound targetInner) := by
  induction bound generalizing outer with
  | nil => exact paired
  | cons signature rest induction =>
      exact induction (.bind signature paired)

/-- The source and target frame compilers retain one identical outer spine.
Only the ordered binder block local to the acted scope may differ. -/
structure ArgumentResult.FrameContextPair
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    {sourceOuter : WireContext source.val}
    {targetOuter : WireContext result.checked.val}
    (outer : result.RetainedContext sourceOuter targetOuter)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame : RegionFrame definitions result.checked.val targetOuter) where
  sourceSiteOuter : WireContext source.val
  targetSiteOuter : WireContext result.checked.val
  siteOuterRetained :
    result.RetainedContext sourceSiteOuter targetSiteOuter
  sourceVisibleContextExact :
    sourceFrame.visible =
      sourceSiteOuter.extend (source.val.wires wire).scope
  targetVisibleContextExact :
    targetFrame.visible =
      targetSiteOuter.extend
        (result.checked.val.wires result.targetWire).scope
  siteOuter : List Sig
  siteOuter_exact : siteOuter = sourceSiteOuter.sigs
  sourceVisibleExact :
    sourceFrame.visible.sigs =
      ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope ++ siteOuter
  targetVisibleExact :
    targetFrame.visible.sigs =
      ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope ++ siteOuter
  paired :
    ContentAlignment.PairedContext definitions
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      siteOuter
      (rebaseContextHole sourceVisibleExact sourceFrame.context)
      (rebaseContextHole targetVisibleExact
        (rebaseContextOuter outer.sigs_exact targetFrame.context))

private def ArgumentResult.FrameContextPair.atSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    {sourceOuter : WireContext source.val}
    {targetOuter : WireContext result.checked.val}
    (outer : result.RetainedContext sourceOuter targetOuter)
    (sourceBody : Region definitions
      (sourceOuter.extend (source.val.wires wire).scope).sigs)
    (targetBody : Region definitions
      (targetOuter.extend
        (result.checked.val.wires result.targetWire).scope).sigs) :
    result.FrameContextPair outer
      { visible := sourceOuter.extend (source.val.wires wire).scope
        siteBody := sourceBody
        context := bindContextFor source.val sourceOuter.ids
          (source.val.wiresAt (source.val.wires wire).scope) .hole }
      { visible := targetOuter.extend
          (result.checked.val.wires result.targetWire).scope
        siteBody := targetBody
        context := bindContextFor result.checked.val targetOuter.ids
          (result.checked.val.wiresAt
            (result.checked.val.wires result.targetWire).scope) .hole } := by
  let sourceVisibleExact :=
    WireContext.sigs_extend sourceOuter (source.val.wires wire).scope
  let targetVisibleExact :=
    (WireContext.sigs_extend targetOuter
      (result.checked.val.wires result.targetWire).scope).trans
      (congrArg
        (List.append
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope))
        outer.sigs_exact)
  refine
    { sourceSiteOuter := sourceOuter
      targetSiteOuter := targetOuter
      siteOuterRetained := outer
      sourceVisibleContextExact := rfl
      targetVisibleContextExact := rfl
      siteOuter := sourceOuter.sigs
      siteOuter_exact := rfl
      sourceVisibleExact := sourceVisibleExact
      targetVisibleExact := targetVisibleExact
      paired := ?_ }
  have sourceContextExact :
      rebaseContextHole sourceVisibleExact
          (bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt (source.val.wires wire).scope) .hole) =
        DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole : DiagramContext definitions
            (ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ sourceOuter.sigs)
            (ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ sourceOuter.sigs)) := by
    exact rebase_bindContextFor_hole_local source.val sourceOuter.ids
      (source.val.wiresAt (source.val.wires wire).scope) sourceOuter.sigs
      rfl sourceVisibleExact
  have targetContextExact :
      rebaseContextHole targetVisibleExact
          (rebaseContextOuter outer.sigs_exact
            (bindContextFor result.checked.val targetOuter.ids
              (result.checked.val.wiresAt
                (result.checked.val.wires result.targetWire).scope) .hole)) =
        DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole : DiagramContext definitions
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope ++
                sourceOuter.sigs)
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope ++
                sourceOuter.sigs)) := by
    exact rebase_bindContextFor_hole_local result.checked.val targetOuter.ids
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope)
      sourceOuter.sigs outer.sigs_exact targetVisibleExact
  change ContentAlignment.PairedContext definitions _ _ sourceOuter.sigs
    (rebaseContextHole sourceVisibleExact
      (bindContextFor source.val sourceOuter.ids
        (source.val.wiresAt (source.val.wires wire).scope) .hole))
    (rebaseContextHole targetVisibleExact
      (rebaseContextOuter outer.sigs_exact
        (bindContextFor result.checked.val targetOuter.ids
          (result.checked.val.wiresAt
            (result.checked.val.wires result.targetWire).scope) .hole)))
  rw [sourceContextExact]
  let targetContext : DiagramContext definitions
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope ++
          sourceOuter.sigs)
      sourceOuter.sigs :=
    rebaseContextHole targetVisibleExact
      (rebaseContextOuter outer.sigs_exact
        (bindContextFor result.checked.val targetOuter.ids
          (result.checked.val.wiresAt
            (result.checked.val.wires result.targetWire).scope) .hole))
  change ContentAlignment.PairedContext definitions _ _ sourceOuter.sigs
    (DiagramContext.bindMany
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope) .hole)
    targetContext
  have targetContextExact' : targetContext =
        DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole : DiagramContext definitions
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope ++
                sourceOuter.sigs)
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope ++
                sourceOuter.sigs)) :=
    by
      dsimp only [targetContext]
      exact rebase_bindContextFor_hole_local result.checked.val targetOuter.ids
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        sourceOuter.sigs outer.sigs_exact targetVisibleExact
  exact targetContextExact'.symm ▸
    (ContentAlignment.PairedContext.terminal
      (definitions := definitions)
      (sourceLocal := ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      (targetLocal := ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      (siteOuter := sourceOuter.sigs))

private def ArgumentResult.FrameContextPair.surround
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceOuter : WireContext source.val}
    {targetOuter : WireContext result.checked.val}
    {outer : result.RetainedContext sourceOuter targetOuter}
    {sourceNested : RegionFrame definitions source.val sourceOuter}
    {targetNested : RegionFrame definitions result.checked.val targetOuter}
    (nested : result.FrameContextPair outer sourceNested targetNested)
    (sourceLeading sourceSuffix : ItemSeq definitions sourceOuter.sigs)
    (targetLeading targetSuffix : ItemSeq definitions targetOuter.sigs)
    (leadingExact :
      rebaseItemSeq outer.sigs_exact targetLeading = sourceLeading)
    (suffixExact :
      rebaseItemSeq outer.sigs_exact targetSuffix = sourceSuffix) :
    result.FrameContextPair outer
      { visible := sourceNested.visible
        siteBody := sourceNested.siteBody
        context := .surround sourceLeading (.cut sourceNested.context)
          sourceSuffix }
      { visible := targetNested.visible
        siteBody := targetNested.siteBody
        context := .surround targetLeading (.cut targetNested.context)
          targetSuffix } := by
  refine
    { sourceSiteOuter := nested.sourceSiteOuter
      targetSiteOuter := nested.targetSiteOuter
      siteOuterRetained := nested.siteOuterRetained
      sourceVisibleContextExact := nested.sourceVisibleContextExact
      targetVisibleContextExact := nested.targetVisibleContextExact
      siteOuter := nested.siteOuter
      siteOuter_exact := nested.siteOuter_exact
      sourceVisibleExact := nested.sourceVisibleExact
      targetVisibleExact := nested.targetVisibleExact
      paired := ?_ }
  let sourceContext :=
    rebaseContextHole nested.sourceVisibleExact
      (DiagramContext.surround sourceLeading (.cut sourceNested.context)
        sourceSuffix)
  let targetContext :=
    rebaseContextHole nested.targetVisibleExact
      (rebaseContextOuter outer.sigs_exact
        (DiagramContext.surround targetLeading (.cut targetNested.context)
          targetSuffix))
  change ContentAlignment.PairedContext definitions _ _ nested.siteOuter
    sourceContext targetContext
  have sourceContextExact : sourceContext =
      DiagramContext.surround sourceLeading
        (.cut
          (rebaseContextHole nested.sourceVisibleExact
            sourceNested.context)) sourceSuffix := by
    exact rebaseContextHole_surroundCut nested.sourceVisibleExact
      sourceLeading sourceSuffix sourceNested.context
  have targetContextExact : targetContext =
      DiagramContext.surround sourceLeading
        (.cut
          (rebaseContextHole nested.targetVisibleExact
            (rebaseContextOuter outer.sigs_exact targetNested.context)))
        sourceSuffix := by
    dsimp only [targetContext]
    rw [rebaseContext_surroundCut, leadingExact, suffixExact]
  exact sourceContextExact.symm ▸ targetContextExact.symm ▸
    (ContentAlignment.PairedContext.surround sourceLeading sourceSuffix
      (ContentAlignment.PairedContext.cut nested.paired))

private noncomputable def ArgumentResult.FrameContextPair.bindRegion
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceOuter : WireContext source.val}
    {targetOuter : WireContext result.checked.val}
    (outer : result.RetainedContext sourceOuter targetOuter)
    (sourceRegion : source.val.RegionId)
    (targetRegion : result.checked.val.RegionId)
    (localExact :
      ContentAlignment.localSignatures result.checked.val targetRegion =
        ContentAlignment.localSignatures source.val sourceRegion)
    (extended : result.RetainedContext
      (sourceOuter.extend sourceRegion) (targetOuter.extend targetRegion))
    {sourceNested : RegionFrame definitions source.val
      (sourceOuter.extend sourceRegion)}
    {targetNested : RegionFrame definitions result.checked.val
      (targetOuter.extend targetRegion)}
    (nested : result.FrameContextPair extended sourceNested targetNested) :
    result.FrameContextPair outer
      { visible := sourceNested.visible
        siteBody := sourceNested.siteBody
        context := bindContextFor source.val sourceOuter.ids
          (source.val.wiresAt sourceRegion) sourceNested.context }
      { visible := targetNested.visible
        siteBody := targetNested.siteBody
        context := bindContextFor result.checked.val targetOuter.ids
          (result.checked.val.wiresAt targetRegion) targetNested.context } := by
  refine
    { sourceSiteOuter := nested.sourceSiteOuter
      targetSiteOuter := nested.targetSiteOuter
      siteOuterRetained := nested.siteOuterRetained
      sourceVisibleContextExact := nested.sourceVisibleContextExact
      targetVisibleContextExact := nested.targetVisibleContextExact
      siteOuter := nested.siteOuter
      siteOuter_exact := nested.siteOuter_exact
      sourceVisibleExact := nested.sourceVisibleExact
      targetVisibleExact := nested.targetVisibleExact
      paired := ?_ }
  let sourceLocal := ContentAlignment.localSignatures source.val sourceRegion
  let sourceExtendExact := WireContext.sigs_extend sourceOuter sourceRegion
  let targetExtendExact := WireContext.sigs_extend targetOuter targetRegion
  let targetDirectExact := targetExtendExact.trans
    (ConcreteElaboration.appendSignaturesExact outer.sigs_exact localExact)
  let sourceContext := rebaseContextHole nested.sourceVisibleExact
    (bindContextFor source.val sourceOuter.ids
      (source.val.wiresAt sourceRegion) sourceNested.context)
  let targetContext := rebaseContextHole nested.targetVisibleExact
    (rebaseContextOuter outer.sigs_exact
      (bindContextFor result.checked.val targetOuter.ids
        (result.checked.val.wiresAt targetRegion) targetNested.context))
  change ContentAlignment.PairedContext definitions _ _ nested.siteOuter
    sourceContext targetContext
  let rebasedPair :=
    ContentAlignment.PairedContext.rebaseOuter sourceExtendExact nested.paired
  let boundPair := rebasedPair.bindMany sourceLocal
  have sourceContextExact : sourceContext =
      DiagramContext.bindMany sourceLocal
        (rebaseContextOuter sourceExtendExact
          (rebaseContextHole nested.sourceVisibleExact
            sourceNested.context)) := by
    calc
      sourceContext = DiagramContext.bindMany sourceLocal
          (rebaseContextHole nested.sourceVisibleExact
            (rebaseContextOuter sourceExtendExact sourceNested.context)) := by
        simpa [sourceContext, sourceLocal, rebaseContextOuter] using
          (rebase_bindContextFor_inner_local source.val sourceOuter.ids
            (source.val.wiresAt sourceRegion)
            (ContentAlignment.localSignatures source.val sourceRegion)
            sourceOuter.sigs rfl rfl sourceExtendExact
            nested.sourceVisibleExact sourceNested.context)
      _ = _ := congrArg (DiagramContext.bindMany sourceLocal)
        (rebaseContext_outer_trans_hole nested.sourceVisibleExact rfl
          sourceExtendExact sourceNested.context)
  have targetContextExact : targetContext =
      DiagramContext.bindMany sourceLocal
        (rebaseContextOuter sourceExtendExact
          (rebaseContextHole nested.targetVisibleExact
            (rebaseContextOuter extended.sigs_exact
              targetNested.context))) := by
    have directProofExact :
        targetDirectExact = extended.sigs_exact.trans sourceExtendExact :=
      Subsingleton.elim _ _
    calc
      targetContext = DiagramContext.bindMany sourceLocal
          (rebaseContextHole nested.targetVisibleExact
            (rebaseContextOuter targetDirectExact targetNested.context)) := by
        simpa [targetContext, sourceLocal] using
          (rebase_bindContextFor_inner_local result.checked.val targetOuter.ids
            (result.checked.val.wiresAt targetRegion)
            (ContentAlignment.localSignatures source.val sourceRegion)
            sourceOuter.sigs outer.sigs_exact localExact targetDirectExact
            nested.targetVisibleExact targetNested.context)
      _ = DiagramContext.bindMany sourceLocal
          (rebaseContextHole nested.targetVisibleExact
            (rebaseContextOuter
              (extended.sigs_exact.trans sourceExtendExact)
              targetNested.context)) := by rw [directProofExact]
      _ = _ := congrArg (DiagramContext.bindMany sourceLocal)
        (rebaseContext_outer_trans_hole nested.targetVisibleExact
          extended.sigs_exact sourceExtendExact targetNested.context)
  exact sourceContextExact.symm ▸ targetContextExact.symm ▸ boundPair

/-- The construction-owned checked region image is injective. -/
theorem ArgumentResult.regionImage_injective
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Function.Injective result.regionImage := by
  intro left right same
  rw [result.regionImage_exact left, result.regionImage_exact right] at same
  exact result.regionEquiv.injective same

private theorem ArgumentResult.childrenOf_regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.childrenOf (result.regionImage region) =
      (source.val.childrenOf region).map result.regionImage := by
  rw [result.childrenOf_decomposition]
  apply List.map_congr_left
  intro child _member
  exact (result.regionImage_exact child).symm

private theorem ArgumentResult.find?_regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : source.val.RegionId) :
    ∀ children : List source.val.RegionId,
      ((children.map result.regionImage).find? fun candidate =>
          decide (result.checked.val.Encloses candidate
            (result.regionImage site))) =
        (children.find? fun candidate =>
          decide (source.val.Encloses candidate site)).map
            result.regionImage
  | [] => rfl
  | child :: tail => by
      simp only [List.map_cons, List.find?_cons]
      rw [show
        decide (result.checked.val.Encloses (result.regionImage child)
          (result.regionImage site)) =
            decide (source.val.Encloses child site) by
          exact decide_eq_decide.mpr (result.regionImage_encloses child site)]
      by_cases encloses : source.val.Encloses child site
      · simp [encloses]
      · simp [encloses, result.find?_regionImage site tail]

set_option maxHeartbeats 1000000 in
private theorem compileSiblingFrame_pair
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (fuel : Nat)
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (selected : source.val.RegionId)
    {sourceNested : RegionFrame definitions source.val sourceContext}
    {targetNested : RegionFrame definitions result.checked.val targetContext}
    (nested : result.FrameContextPair context sourceNested targetNested)
    (sourceLeading : ItemSeq definitions sourceContext.sigs)
    (targetLeading : ItemSeq definitions targetContext.sigs)
    (leadingExact :
      rebaseItemSeq context.sigs_exact targetLeading = sourceLeading) :
    ∀ (children : List source.val.RegionId),
      children.Nodup →
      (∀ child, child ∈ children → child ≠ selected →
        ¬source.val.Encloses (source.val.wires wire).scope child ∧
        ¬source.val.Encloses child (source.val.wires wire).scope) →
      (∀ child, child ∈ children →
        ContextAbove result.checked.val targetContext
          (result.regionImage child)) →
      ∀ {sourceFrame : RegionFrame definitions source.val sourceContext}
        {targetFrame : RegionFrame definitions result.checked.val targetContext},
        compileSiblingFrame? definitions source.val fuel sourceContext
            selected sourceNested sourceLeading children = some sourceFrame →
        compileSiblingFrame? definitions result.checked.val fuel targetContext
            (result.regionImage selected) targetNested targetLeading
            (children.map result.regionImage) = some targetFrame →
        Nonempty (result.FrameContextPair context sourceFrame targetFrame) := by
  intro children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro nodup outside above sourceFrame targetFrame sourceCompiled
        targetCompiled
      simp [compileSiblingFrame?] at sourceCompiled
  | cons child tail induction =>
      intro nodup outside above sourceFrame targetFrame sourceCompiled
        targetCompiled
      rw [List.nodup_cons] at nodup
      by_cases same : child = selected
      · subst child
        simp only [compileSiblingFrame?, ↓reduceDIte] at sourceCompiled
        simp only [List.map_cons, compileSiblingFrame?, ↓reduceDIte]
          at targetCompiled
        obtain ⟨sourceSuffix, sourceSuffixCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetSuffix, targetSuffixCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have sourceFrameExact := Option.some.inj sourceFrameEquation
        have targetFrameExact := Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        obtain ⟨generatedSuffix, generatedSuffixCompiled,
            generatedSuffixExact⟩ :=
          compileChildren_reindexed_outside result localized fuel context tail
            (by
              intro candidate member
              exact above candidate (by simp [member]))
            (by
              intro candidate member
              apply outside candidate (by simp [member])
              intro candidateSelected
              subst candidate
              exact nodup.1 member)
            sourceSuffixCompiled
        have targetSuffixExact : targetSuffix = generatedSuffix :=
          Option.some.inj
            (targetSuffixCompiled.symm.trans generatedSuffixCompiled)
        subst targetSuffix
        exact ⟨nested.surround sourceLeading sourceSuffix targetLeading
          generatedSuffix leadingExact generatedSuffixExact⟩
      · simp only [compileSiblingFrame?, same, ↓reduceDIte] at sourceCompiled
        have targetDifferent :
            result.regionImage child ≠ result.regionImage selected :=
          fun equality => same (result.regionImage_injective equality)
        simp only [List.map_cons, compileSiblingFrame?, targetDifferent,
          ↓reduceDIte] at targetCompiled
        obtain ⟨sourceHead, sourceHeadCompiled, sourceRestCompiled⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetHead, targetHeadCompiled, targetRestCompiled⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have childOutside := outside child (by simp) same
        obtain ⟨generatedHead, generatedHeadCompiled,
            generatedHeadExact⟩ :=
          ArgumentResult.RetainedContext.compileRegion_reindexed_outside
            result localized fuel child sourceContext targetContext context
            (above child (by simp)) childOutside.1 childOutside.2
            sourceHeadCompiled
        have targetHeadExact : targetHead = generatedHead :=
          Option.some.inj
            (targetHeadCompiled.symm.trans generatedHeadCompiled)
        subst targetHead
        apply induction
          (sourceLeading.append (.cons (.cut sourceHead) .nil))
          (targetLeading.append (.cons (.cut generatedHead) .nil))
          (rebaseItemSeq_append_cut context.sigs_exact sourceLeading
            targetLeading sourceHead generatedHead leadingExact
            generatedHeadExact)
          nodup.2
          (by
            intro candidate member different
            exact outside candidate (by simp [member]) different)
          (by
            intro candidate member
            exact above candidate (by simp [member]))
          sourceRestCompiled targetRestCompiled

set_option maxHeartbeats 1600000 in
private theorem compileRegionFrame_pair
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization) :
    ∀ (fuel : Nat)
      (region : source.val.RegionId)
      (sourceOuter : WireContext source.val)
      (targetOuter : WireContext result.checked.val)
      (outer : result.RetainedContext sourceOuter targetOuter)
      (_sourceEncloses :
        source.val.Encloses region (source.val.wires wire).scope)
      (_targetAbove : ContextAbove result.checked.val targetOuter
        (result.regionImage region))
      {sourceFrame : RegionFrame definitions source.val sourceOuter}
      {targetFrame : RegionFrame definitions result.checked.val targetOuter},
      compileRegionFrame? definitions source.val
          (source.val.wires wire).scope fuel region sourceOuter =
        some sourceFrame →
      compileRegionFrame? definitions result.checked.val
          (result.checked.val.wires result.targetWire).scope fuel
          (result.regionImage region) targetOuter =
        some targetFrame →
      Nonempty (result.FrameContextPair outer sourceFrame targetFrame) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region sourceOuter targetOuter outer sourceEncloses targetAbove
        sourceFrame targetFrame sourceCompiled targetCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ childFuel induction =>
      intro region sourceOuter targetOuter outer sourceEncloses targetAbove
        sourceFrame targetFrame sourceCompiled targetCompiled
      by_cases atSite : region = (source.val.wires wire).scope
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceCompiled
        have targetAtSite :
            result.regionImage (source.val.wires wire).scope =
              (result.checked.val.wires result.targetWire).scope :=
          result.targetWire_scope_regionImage.symm
        simp only [compileRegionFrame?, targetAtSite, ↓reduceDIte]
          at targetCompiled
        obtain ⟨sourceBody, sourceBodyCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetBody, targetBodyCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have sourceFrameExact := Option.some.inj sourceFrameEquation
        have targetFrameExact := Option.some.inj targetFrameEquation
        let targetBody' := rebaseSiteBody targetOuter
          (result.regionImage (source.val.wires wire).scope)
          (result.checked.val.wires result.targetWire).scope targetAtSite
          targetBody
        have targetRecordExact := siteFrame_reindex result.checked.val
          targetOuter (result.regionImage (source.val.wires wire).scope)
          (result.checked.val.wires result.targetWire).scope targetAtSite
          targetBody
        have targetFrameCanonical : targetFrame =
            ({ visible := targetOuter.extend
                (result.checked.val.wires result.targetWire).scope
               siteBody := targetBody'
               context := bindContextFor result.checked.val targetOuter.ids
                 (result.checked.val.wiresAt
                   (result.checked.val.wires result.targetWire).scope)
                 .hole } :
              RegionFrame definitions result.checked.val targetOuter) :=
          targetFrameExact.symm.trans targetRecordExact
        subst sourceFrame
        rw [targetFrameCanonical]
        exact ⟨ArgumentResult.FrameContextPair.atSite result outer
          sourceBody targetBody'⟩
      · simp only [compileRegionFrame?, atSite, ↓reduceDIte]
          at sourceCompiled
        have targetNotAtSite :
            result.regionImage region ≠
              (result.checked.val.wires result.targetWire).scope := by
          rw [result.targetWire_scope_regionImage]
          intro same
          exact atSite (result.regionImage_injective same)
        simp only [compileRegionFrame?, targetNotAtSite, ↓reduceDIte]
          at targetCompiled
        obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨sourceSelected, sourceSelectedFound,
            sourceAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNodes
        obtain ⟨sourceNested, sourceNestedCompiled, sourceAfterNested⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterSelected
        obtain ⟨sourceAround, sourceAroundCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNested
        obtain ⟨targetNodes, targetNodesCompiled, targetAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        obtain ⟨targetSelected, targetSelectedFound,
            targetAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNodes
        obtain ⟨targetNested, targetNestedCompiled, targetAfterNested⟩ :=
          Option.bind_eq_some_iff.mp targetAfterSelected
        obtain ⟨targetAround, targetAroundCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNested
        have sourceFrameExact := Option.some.inj sourceFrameEquation
        have targetFrameExact := Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        have targetChildrenExact := result.childrenOf_regionImage region
        rw [targetChildrenExact, result.targetWire_scope_regionImage,
          result.find?_regionImage (source.val.wires wire).scope,
          sourceSelectedFound] at targetSelectedFound
        have targetSelectedExact :
            targetSelected = result.regionImage sourceSelected :=
          (Option.some.inj targetSelectedFound).symm
        subst targetSelected
        rw [targetChildrenExact] at targetAroundCompiled
        have sourceSelectedMember :=
          List.mem_of_find?_eq_some sourceSelectedFound
        have sourceSelectedData :=
          ConcreteElaboration.mem_childrenOf source.val region sourceSelected
            sourceSelectedMember
        have sourceSelectedEncloses :
            source.val.Encloses sourceSelected
              (source.val.wires wire).scope :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide (source.val.Encloses candidate
                  (source.val.wires wire).scope))
              sourceSelectedFound)
        have notBelow :
            ¬source.val.Encloses (source.val.wires wire).scope region := by
          intro reverse
          have same := factor_encloses_antisymm definitions source.val
            source.property sourceEncloses reverse
          exact atSite same
        let extended := outer.extendStrictlyAbove localized region
          sourceEncloses atSite
        have targetExtendedNodup :
            (targetOuter.extend (result.regionImage region)).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions result.checked.val
            result.checked.property targetOuter (result.regionImage region)
            targetAbove
        obtain ⟨generatedNodes, generatedNodesCompiled,
            generatedNodesExact⟩ :=
          extended.compileNodes_reindexed targetExtendedNodup
            (ArgumentResult.RetainedContext.nodesAt_strictlyAbove result
              region sourceEncloses atSite)
            sourceNodesCompiled
        have targetNodesExact : targetNodes = generatedNodes :=
          Option.some.inj
            (targetNodesCompiled.symm.trans generatedNodesCompiled)
        subst targetNodes
        have targetSelectedData :
            result.checked.val.regions
                (result.regionImage sourceSelected) =
              .cut (result.regionImage region) := by
          rw [result.regionImage_exact sourceSelected,
            result.regionImage_exact region,
            result.regionImage_data sourceSelected]
          simp [sourceSelectedData, CRegion.rename]
        have targetSelectedAbove :=
          ConcreteElaboration.extend_above_child definitions
            result.checked.val result.checked.property targetOuter
            (result.regionImage region) (result.regionImage sourceSelected)
            targetAbove targetSelectedData
        obtain ⟨nestedPair⟩ :=
          induction sourceSelected (sourceOuter.extend region)
            (targetOuter.extend (result.regionImage region)) extended
            sourceSelectedEncloses targetSelectedAbove
            sourceNestedCompiled targetNestedCompiled
        have childrenNodup : (source.val.childrenOf region).Nodup := by
          unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
          exact (Data.Finite.allFin_nodup source.val.regionCount).filter _
        have otherOutside :
            ∀ child, child ∈ source.val.childrenOf region →
              child ≠ sourceSelected →
              ¬source.val.Encloses (source.val.wires wire).scope child ∧
              ¬source.val.Encloses child (source.val.wires wire).scope := by
          intro child member different
          have childData := ConcreteElaboration.mem_childrenOf source.val
            region child member
          have regionChild :=
            InsertionCompilation.NaturalityInternal.parent_encloses_child
              source.val child region childData
          have childStrict :=
            InsertionCompilation.NaturalityInternal.checked_child_ne_parent
              definitions source.val source.property child region childData
          have selectedNotChild :
              ¬source.val.Encloses sourceSelected child := by
            intro selectedChild
            rcases
                InsertionCompilation.NaturalityInternal.checked_encloses_child_split
                  source.val sourceSelected child region childData
                    selectedChild
              with same | selectedRegion
            · exact different same.symm
            · have regionSelected :=
                InsertionCompilation.NaturalityInternal.parent_encloses_child
                  source.val sourceSelected region sourceSelectedData
              have same :=
                InsertionCompilation.NaturalityInternal.checked_encloses_antisymm
                  definitions source.val source.property selectedRegion
                  regionSelected
              exact
                (InsertionCompilation.NaturalityInternal.checked_child_ne_parent
                  definitions source.val source.property sourceSelected region
                  sourceSelectedData) same
          have selectedNotBelow :
              ¬source.val.Encloses (source.val.wires wire).scope child := by
            intro actedChild
            exact selectedNotChild
              (encloses_trans_local definitions source.val source.property
                sourceSelectedEncloses actedChild)
          refine ⟨selectedNotBelow, ?_⟩
          intro childActed
          have selectedChild :=
            InsertionCompilation.NaturalityInternal.selected_child_encloses_middle
              definitions source.val source.property regionChild childStrict
              sourceSelectedData sourceSelectedEncloses childActed
          exact selectedNotChild selectedChild
        have allChildrenAbove :
            ∀ child, child ∈ source.val.childrenOf region →
              ContextAbove result.checked.val
                (targetOuter.extend (result.regionImage region))
                (result.regionImage child) := by
          intro child member
          have childData := ConcreteElaboration.mem_childrenOf source.val
            region child member
          have targetChildData :
              result.checked.val.regions (result.regionImage child) =
                .cut (result.regionImage region) := by
            rw [result.regionImage_exact child,
              result.regionImage_exact region,
              result.regionImage_data child]
            simp [childData, CRegion.rename]
          exact ConcreteElaboration.extend_above_child definitions
            result.checked.val result.checked.property targetOuter
            (result.regionImage region) (result.regionImage child)
            targetAbove targetChildData
        obtain ⟨aroundPair⟩ :=
          compileSiblingFrame_pair result localized childFuel extended
            sourceSelected nestedPair sourceNodes generatedNodes
            generatedNodesExact (source.val.childrenOf region) childrenNodup
            otherOutside allChildrenAbove sourceAroundCompiled
            targetAroundCompiled
        have localExact :=
          ArgumentResult.RetainedContext.localSigs_exact_not_below
            (result := result) localized region notBelow
        exact ⟨aroundPair.bindRegion outer region (result.regionImage region)
          localExact extended⟩

/-- Construction-owned source/target frame pair at the acted scope.  Unlike
the later signature-only factorization, this receipt retains the concrete
site-outer contexts and their exact wire map. -/
noncomputable def ArgumentResult.actedScopeFramePair
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (sourceScope : SiteCompilation source (source.val.wires wire).scope)
    (targetScope : SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope) :
    result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      sourceScope.frame targetScope.frame := by
  have rootEncloses :
      source.val.Encloses source.val.root (source.val.wires wire).scope :=
    of_decide_eq_true
      ((List.all_eq_true.mp source.property.all_regions_reach_root)
        (source.val.wires wire).scope
        (Data.Finite.mem_allFin (source.val.wires wire).scope))
  have targetRootAbove :
      ContextAbove result.checked.val (WireContext.empty result.checked.val)
        (result.regionImage source.val.root) := by
    refine ⟨by simp [WireContext.empty], ?_⟩
    intro targetWire member
    simp [WireContext.empty] at member
  have sourceGenerated := sourceScope.frame_generated
  have targetGenerated := targetScope.frame_generated
  rw [result.targetRoot_exact] at targetGenerated
  have fuelExact : result.checked.val.regionCount + 1 =
      source.val.regionCount + 1 := by rw [← result.regionCount_exact]
  have targetGenerated' :
      compileRegionFrame? definitions result.checked.val
          (result.checked.val.wires result.targetWire).scope
          (source.val.regionCount + 1) (result.regionImage source.val.root)
          (WireContext.empty result.checked.val) =
        some targetScope.frame := by
    rw [← fuelExact]
    exact targetGenerated
  exact Classical.choice (compileRegionFrame_pair result localized
    (source.val.regionCount + 1) source.val.root
    (WireContext.empty source.val) (WireContext.empty result.checked.val)
    (ArgumentResult.RetainedContext.empty result) rootEncloses
    targetRootAbove sourceGenerated targetGenerated')

/-- The two canonical scope compilers for an argument replacement always
expose one exactly shared outer spine, and the executable alignment checker
rediscovers that construction-owned receipt. -/
theorem checkSiteContextFactorization_argument_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (sourceScope : SiteCompilation source (source.val.wires wire).scope)
    (targetScope : SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope) :
    ∃ found,
      ContentAlignment.checkSiteContextFactorization sourceScope targetScope =
        some found := by
  let pair := result.actedScopeFramePair localized sourceScope targetScope
  have paired : ContentAlignment.PairedContext definitions
      (ContentAlignment.localSignatures source.val
        (source.val.wires wire).scope)
      (ContentAlignment.localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      pair.siteOuter
      (pair.sourceVisibleExact ▸ sourceScope.frame.context)
      (pair.targetVisibleExact ▸ targetScope.frame.context) := by
    simpa [rebaseContextOuter, ArgumentResult.RetainedContext.empty] using
      pair.paired
  let factorization := ContentAlignment.SiteContextFactorization.ofPaired
    pair.siteOuter pair.sourceVisibleExact pair.targetVisibleExact paired
  exact ContentAlignment.checkSiteContextFactorization_complete factorization

end ConcreteWirePrimitive
end VisualProof
