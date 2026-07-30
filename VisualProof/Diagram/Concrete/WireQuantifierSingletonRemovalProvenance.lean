import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemoval
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoin
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrameSupport

namespace VisualProof

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

/--
Recursive authority for one singleton-erasure sibling branch. It records the
selected child and every skipped sibling while the target branch is generated.
-/
inductive ErasureSiblingProvenance
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceTarget : source.val.RegionId)
    (sourceNested :
      RegionFrame definitions source.val sourceOuter)
    (targetNested :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter)) :
    ItemSeq definitions sourceOuter.sigs →
    ItemSeq definitions (targetContext source removed sourceOuter).sigs →
    List source.val.RegionId →
    RegionFrame definitions source.val sourceOuter →
    RegionFrame definitions
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed)
      (targetContext source removed sourceOuter) →
    Prop where
  | selected
      (sourceLeading :
        ItemSeq definitions sourceOuter.sigs)
      (targetLeading :
        ItemSeq definitions (targetContext source removed sourceOuter).sigs)
      (tail : List source.val.RegionId)
      (sourceSuffix : ItemSeq definitions sourceOuter.sigs)
      (targetSuffix :
        ItemSeq definitions (targetContext source removed sourceOuter).sigs)
      (sourceSuffixCompiled :
        ConcreteElaboration.compileChildrenWith? definitions source.val
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            sourceOuter tail =
          some sourceSuffix)
      (targetSuffixCompiled :
        ConcreteElaboration.compileChildrenWith? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (ConcreteElaboration.compileRegion? definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed) fuel)
            (targetContext source removed sourceOuter)
            (tail.map (targetRegion source removed)) =
          some targetSuffix) :
      ErasureSiblingProvenance source removed fuel sourceOuter sourceTarget
        sourceNested targetNested sourceLeading targetLeading
        (sourceTarget :: tail)
        { visible := sourceNested.visible
          siteBody := sourceNested.siteBody
          context := .surround sourceLeading (.cut sourceNested.context)
            sourceSuffix }
        { visible := targetNested.visible
          siteBody := targetNested.siteBody
          context := .surround targetLeading (.cut targetNested.context)
            targetSuffix }
  | outside
      (sourceLeading :
        ItemSeq definitions sourceOuter.sigs)
      (targetLeading :
        ItemSeq definitions (targetContext source removed sourceOuter).sigs)
      (child : source.val.RegionId)
      (tail : List source.val.RegionId)
      (different : child ≠ sourceTarget)
      (sourceBody : Region definitions sourceOuter.sigs)
      (targetBody :
        Region definitions (targetContext source removed sourceOuter).sigs)
      (sourceBodyCompiled :
        ConcreteElaboration.compileRegion? definitions source.val fuel child
            sourceOuter =
          some sourceBody)
      (targetBodyCompiled :
        ConcreteElaboration.compileRegion? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            fuel (targetRegion source removed child)
            (targetContext source removed sourceOuter) =
          some targetBody)
      {sourceFrame :
        RegionFrame definitions source.val sourceOuter}
      {targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed sourceOuter)}
      (rest :
        ErasureSiblingProvenance source removed fuel sourceOuter sourceTarget
          sourceNested targetNested
          (sourceLeading.append (.cons (.cut sourceBody) .nil))
          (targetLeading.append (.cons (.cut targetBody) .nil))
          tail sourceFrame targetFrame) :
      ErasureSiblingProvenance source removed fuel sourceOuter sourceTarget
        sourceNested targetNested sourceLeading targetLeading
        (child :: tail) sourceFrame targetFrame

private theorem compileSiblingFrame_withProvenance
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceTarget : source.val.RegionId)
    (sourceNested : RegionFrame definitions source.val sourceOuter)
    (targetNested :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter))
    (nestedVisible :
      targetNested.visible =
        targetContext source removed sourceNested.visible) :
    ∀ (sourceLeading : ItemSeq definitions sourceOuter.sigs)
      (targetLeading :
        ItemSeq definitions
          (targetContext source removed sourceOuter).sigs)
      (children : List source.val.RegionId)
      {sourceFrame : RegionFrame definitions source.val sourceOuter},
      compileSiblingFrame? definitions source.val fuel sourceOuter
          sourceTarget sourceNested sourceLeading children =
        some sourceFrame →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove source.val sourceOuter child) →
      ∃ targetFrame :
          RegionFrame definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter),
        compileSiblingFrame? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            fuel (targetContext source removed sourceOuter)
            (targetRegion source removed sourceTarget) targetNested
            targetLeading
            (children.map (targetRegion source removed)) =
          some targetFrame ∧
        targetFrame.visible =
          targetContext source removed sourceFrame.visible ∧
        ErasureSiblingProvenance source removed fuel sourceOuter
          sourceTarget sourceNested targetNested sourceLeading targetLeading
          children sourceFrame targetFrame := by
  intro sourceLeading targetLeading children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro sourceFrame compiled above
      simp [compileSiblingFrame?] at compiled
  | cons child tail induction =>
      intro sourceFrame compiled above
      by_cases same : child = sourceTarget
      · subst child
        simp only [compileSiblingFrame?, ↓reduceDIte] at compiled
        obtain ⟨sourceSuffix, sourceSuffixCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp compiled
        have sourceFrameExact :
            ({ visible := sourceNested.visible
               siteBody := sourceNested.siteBody
               context :=
                 .surround sourceLeading (.cut sourceNested.context)
                   sourceSuffix } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        obtain ⟨targetSuffix, targetSuffixCompiled⟩ :=
          compileChildren_natural_of source.val
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (ConcreteElaboration.compileRegion? definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed) fuel)
            sourceOuter (targetContext source removed sourceOuter)
            (targetRegion source removed) tail sourceSuffixCompiled
            (by
              intro candidate member body bodyCompiled
              exact
                compileRegion_natural source removed candidateWellFormed fuel
                  sourceOuter candidate
                  (above candidate
                    (List.mem_cons_of_mem sourceTarget member))
                  bodyCompiled)
        let targetFrame :
            RegionFrame definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (targetContext source removed sourceOuter) :=
          { visible := targetNested.visible
            siteBody := targetNested.siteBody
            context :=
              .surround targetLeading (.cut targetNested.context)
                targetSuffix }
        refine ⟨targetFrame, ?_, nestedVisible, ?_⟩
        · simp [compileSiblingFrame?, targetFrame, targetSuffixCompiled]
        · exact
            .selected sourceLeading targetLeading tail sourceSuffix
              targetSuffix sourceSuffixCompiled targetSuffixCompiled
      · simp only [compileSiblingFrame?, same, ↓reduceDIte] at compiled
        obtain ⟨sourceBody, sourceBodyCompiled, rest⟩ :=
          Option.bind_eq_some_iff.mp compiled
        obtain ⟨targetBody, targetBodyCompiled⟩ :=
          compileRegion_natural source removed candidateWellFormed fuel
            sourceOuter child (above child (by simp)) sourceBodyCompiled
        obtain ⟨targetFrame, targetCompiled, visible, provenance⟩ :=
          induction
            (sourceLeading.append (.cons (.cut sourceBody) .nil))
            (targetLeading.append (.cons (.cut targetBody) .nil))
            rest (by
              intro candidate member
              exact above candidate (List.mem_cons_of_mem child member))
        refine ⟨targetFrame, ?_, visible, ?_⟩
        · rw [targetRegion_eq] at targetBodyCompiled targetCompiled
          simp [compileSiblingFrame?, same, targetBodyCompiled,
            targetCompiled]
        · exact
            .outside sourceLeading targetLeading child tail same sourceBody
              targetBody sourceBodyCompiled targetBodyCompiled provenance

/-- Reindex a generated item sequence along outer-context equality. -/
def erasureRebaseItemSeq
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (items : ItemSeq definitions left.sigs) :
    ItemSeq definitions right.sigs := by
  subst right
  exact items

/-- Reindex a generated frame along outer-context equality. -/
def erasureRebaseRegionFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    RegionFrame definitions diagram right := by
  subst right
  exact frame

@[simp] theorem erasureRebaseRegionFrame_visible
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    (erasureRebaseRegionFrame same frame).visible = frame.visible := by
  subst right
  rfl

@[simp] theorem erasureRebaseRegionFrame_siteBody
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    congrArg ConcreteElaboration.WireContext.sigs
          (erasureRebaseRegionFrame_visible same frame) ▸
        (erasureRebaseRegionFrame same frame).siteBody =
      frame.siteBody := by
  subst right
  rfl

/-- Filling a frame commutes with reindexing its exposed outer context. -/
theorem erasureRebaseRegionFrame_fill
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    congrArg ConcreteElaboration.WireContext.sigs same ▸
        frame.context.fill frame.siteBody =
      (erasureRebaseRegionFrame same frame).context.fill
        (erasureRebaseRegionFrame same frame).siteBody := by
  cases same
  rfl

private theorem compileFrameBranch_cast_context_withProvenance
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    {right :
      ConcreteElaboration.WireContext
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)}
    (same : targetContext source removed sourceOuter = right)
    (site : source.val.RegionId)
    (fuel : Nat)
    (selected : source.val.RegionId)
    (sourceSelected : source.val.RegionId)
    (nodes : List
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).NodeId)
    (children : List source.val.RegionId)
    {sourceLeading : ItemSeq definitions sourceOuter.sigs}
    {sourceNested sourceFrame :
      RegionFrame definitions source.val sourceOuter}
    {targetLeading :
      ItemSeq definitions (targetContext source removed sourceOuter).sigs}
    {targetNested targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed) (targetContext source removed sourceOuter)}
    (targetLeadingCompiled :
      ConcreteElaboration.compileNodes? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed sourceOuter) nodes =
        some targetLeading)
    (targetNestedCompiled :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetRegion source removed site) fuel
          (targetRegion source removed selected)
          (targetContext source removed sourceOuter) =
        some targetNested)
    (targetFrameCompiled :
      compileSiblingFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          fuel (targetContext source removed sourceOuter)
          (targetRegion source removed selected) targetNested
          targetLeading (children.map (targetRegion source removed)) =
        some targetFrame)
    (provenance :
      ErasureSiblingProvenance source removed fuel sourceOuter
        sourceSelected sourceNested targetNested sourceLeading targetLeading
        children sourceFrame targetFrame) :
    ∃ (rightLeading : ItemSeq definitions right.sigs)
      (rightNested rightFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed) right),
      ConcreteElaboration.compileNodes? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          right nodes = some rightLeading ∧
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetRegion source removed site) fuel
          (targetRegion source removed selected) right =
        some rightNested ∧
      compileSiblingFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          fuel right (targetRegion source removed selected) rightNested
          rightLeading (children.map (targetRegion source removed)) =
        some rightFrame ∧
      rightLeading = erasureRebaseItemSeq same targetLeading ∧
      rightNested = erasureRebaseRegionFrame same targetNested ∧
      rightFrame = erasureRebaseRegionFrame same targetFrame := by
  subst right
  exact
    ⟨targetLeading, targetNested, targetFrame, targetLeadingCompiled,
      targetNestedCompiled, targetFrameCompiled, rfl, rfl, rfl⟩

/--
Single recursive authority for a source-generated singleton-erasure frame.
Every ancestor retains both the selected nested frame and its sibling branch.
-/
inductive ErasureFrameProvenance
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (site : source.val.RegionId) :
    (fuel : Nat) →
    (sourceOuter : ConcreteElaboration.WireContext source.val) →
    (region : source.val.RegionId) →
    RegionFrame definitions source.val sourceOuter →
    RegionFrame definitions
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed)
      (targetContext source removed sourceOuter) →
    Prop where
  | site
      (childFuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (sourceBody : Region definitions (sourceOuter.extend site).sigs)
      (targetBody :
        Region definitions
          ((targetContext source removed sourceOuter).extend
            (targetRegion source removed site)).sigs)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceOuter site)
      (sourceBodyCompiled :
        compileRegionBody? definitions source.val childFuel site sourceOuter =
          some sourceBody)
      (targetBodyCompiled :
        compileRegionBody? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            childFuel (targetRegion source removed site)
            (targetContext source removed sourceOuter) =
          some targetBody) :
      ErasureFrameProvenance source removed site (childFuel + 1)
        sourceOuter site
        { visible := sourceOuter.extend site
          siteBody := sourceBody
          context := bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt site) .hole }
        { visible := (targetContext source removed sourceOuter).extend
            (targetRegion source removed site)
          siteBody := targetBody
          context := bindContextFor
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter).ids
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).wiresAt (targetRegion source removed site))
            .hole }
  | ancestor
      (childFuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (region selected : source.val.RegionId)
      (notSite : region ≠ site)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceOuter region)
      (sourceNodes :
        ItemSeq definitions (sourceOuter.extend region).sigs)
      (targetNodes :
        ItemSeq definitions
          (targetContext source removed (sourceOuter.extend region)).sigs)
      (sourceNested sourceAround :
        RegionFrame definitions source.val (sourceOuter.extend region))
      (targetNested targetAround :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed (sourceOuter.extend region)))
      (sourceNodesCompiled :
        ConcreteElaboration.compileNodes? definitions source.val
            (sourceOuter.extend region) (source.val.nodesAt region) =
          some sourceNodes)
      (targetNodesCompiled :
        ConcreteElaboration.compileNodes? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed (sourceOuter.extend region))
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).nodesAt (targetRegion source removed region)) =
          some targetNodes)
      (selectedFound :
        (source.val.childrenOf region).find?
            (fun candidate => decide (source.val.Encloses candidate site)) =
          some selected)
      (sourceNestedCompiled :
        compileRegionFrame? definitions source.val site childFuel selected
            (sourceOuter.extend region) =
          some sourceNested)
      (sourceAroundCompiled :
        compileSiblingFrame? definitions source.val childFuel
            (sourceOuter.extend region) selected sourceNested sourceNodes
            (source.val.childrenOf region) =
          some sourceAround)
      (targetAroundCompiled :
        compileSiblingFrame? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            childFuel
            (targetContext source removed (sourceOuter.extend region))
            (targetRegion source removed selected) targetNested targetNodes
            ((source.val.childrenOf region).map
              (targetRegion source removed)) =
          some targetAround)
      (siblings :
        ErasureSiblingProvenance source removed childFuel
          (sourceOuter.extend region) selected sourceNested targetNested
          sourceNodes targetNodes (source.val.childrenOf region)
          sourceAround targetAround)
      (nested :
        ErasureFrameProvenance source removed site childFuel
          (sourceOuter.extend region) selected sourceNested targetNested) :
      ErasureFrameProvenance source removed site (childFuel + 1)
        sourceOuter region
        { visible := sourceAround.visible
          siteBody := sourceAround.siteBody
          context := bindContextFor source.val sourceOuter.ids
            (source.val.wiresAt region) sourceAround.context }
        { visible :=
            (erasureRebaseRegionFrame
              (targetContext_extend source removed sourceOuter region)
              targetAround).visible
          siteBody :=
            (erasureRebaseRegionFrame
              (targetContext_extend source removed sourceOuter region)
              targetAround).siteBody
          context := bindContextFor
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter).ids
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).wiresAt (targetRegion source removed region))
            (erasureRebaseRegionFrame
              (targetContext_extend source removed sourceOuter region)
              targetAround).context }

/-- Target compilation is derived by folding the retained erasure provenance. -/
theorem ErasureFrameProvenance.targetGenerated
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    {site region : source.val.RegionId}
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter)}
    (provenance :
      ErasureFrameProvenance source removed site fuel sourceOuter region
        sourceFrame targetFrame) :
    compileRegionFrame? definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetRegion source removed site) fuel
        (targetRegion source removed region)
        (targetContext source removed sourceOuter) =
      some targetFrame := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      sourceBodyCompiled targetBodyCompiled =>
      simp [compileRegionFrame?, targetBodyCompiled]
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes targetNodes sourceNested sourceAround targetNested
      targetAround sourceNodesCompiled targetNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
      siblings nested induction =>
      have contextEquality :=
        targetContext_extend source removed sourceOuter region
      obtain ⟨targetNodes', targetNested', targetAround',
          targetNodesCompiled', targetNestedCompiled',
          targetAroundCompiled', targetNodesExact, targetNestedExact,
          targetAroundExact⟩ :=
        compileFrameBranch_cast_context_withProvenance source removed
          (sourceOuter.extend region) contextEquality site childFuel selected
          selected
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).nodesAt (targetRegion source removed region))
          (source.val.childrenOf region) targetNodesCompiled induction
          targetAroundCompiled siblings
      subst targetNodes'
      subst targetNested'
      subst targetAround'
      have targetNotAtSite :
          targetRegion source removed region ≠
            targetRegion source removed site :=
        fun same => notSite (targetRegion_injective source removed same)
      simp only [compileRegionFrame?, targetNotAtSite, ↓reduceDIte]
      rw [targetNodesCompiled']
      rw [target_childrenOf, target_find_enclosing, selectedFound]
      simp only [Option.map_some]
      let finalAround :=
        erasureRebaseRegionFrame contextEquality targetAround
      let finalFrame :
          RegionFrame definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter) :=
        { visible := finalAround.visible
          siteBody := finalAround.siteBody
          context := bindContextFor
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter).ids
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).wiresAt
                (targetRegion source removed region))
            finalAround.context }
      change
        (compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetRegion source removed site) childFuel
          (targetRegion source removed selected)
          ((targetContext source removed sourceOuter).extend
            (targetRegion source removed region))).bind (fun nested =>
            (compileSiblingFrame? definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              childFuel
              ((targetContext source removed sourceOuter).extend
                (targetRegion source removed region))
              (targetRegion source removed selected) nested
              (erasureRebaseItemSeq contextEquality targetNodes)
              ((source.val.childrenOf region).map
                (targetRegion source removed))).bind (fun around =>
                  some
                    { visible := around.visible
                      siteBody := around.siteBody
                      context := bindContextFor
                        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                          source removed)
                        (targetContext source removed sourceOuter).ids
                        ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                          source removed).wiresAt
                            (targetRegion source removed region))
                        around.context })) =
          some finalFrame
      rw [targetNestedCompiled']
      simp only [Option.bind_some]
      rw [targetAroundCompiled']
      rfl

/-- Visible-context exactness is also a provenance fold. -/
theorem ErasureFrameProvenance.targetVisible
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    {site region : source.val.RegionId}
    {fuel : Nat}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter)}
    (provenance :
      ErasureFrameProvenance source removed site fuel sourceOuter region
        sourceFrame targetFrame) :
    targetFrame.visible =
      targetContext source removed sourceFrame.visible := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      sourceBodyCompiled targetBodyCompiled =>
      exact
        (targetContext_extend source removed sourceOuter site).symm
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes targetNodes sourceNested sourceAround targetNested
      targetAround sourceNodesCompiled targetNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
      siblings nested induction =>
      have sourceAroundVisible :=
        siblingFrame_visible definitions source.val childFuel
          (sourceOuter.extend region) selected sourceNested sourceNodes
          (source.val.childrenOf region) sourceAroundCompiled
      have targetAroundVisible :=
        siblingFrame_visible definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          childFuel
          (targetContext source removed (sourceOuter.extend region))
          (targetRegion source removed selected) targetNested targetNodes
          ((source.val.childrenOf region).map
            (targetRegion source removed))
          targetAroundCompiled
      change
        (erasureRebaseRegionFrame
          (targetContext_extend source removed sourceOuter region)
          targetAround).visible =
          targetContext source removed sourceAround.visible
      exact
        (erasureRebaseRegionFrame_visible
          (targetContext_extend source removed sourceOuter region)
          targetAround).trans
          (targetAroundVisible.trans
            (induction.trans
              (congrArg (targetContext source removed)
                sourceAroundVisible.symm)))

set_option maxHeartbeats 1600000 in
private theorem compileRegionFrame_withProvenance
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions) :
    ∀ (fuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (region site : source.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceOuter region)
      {sourceFrame : RegionFrame definitions source.val sourceOuter},
      compileRegionFrame? definitions source.val site fuel region
          sourceOuter =
        some sourceFrame →
      ∃ targetFrame :
          RegionFrame definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed sourceOuter),
        ErasureFrameProvenance source removed site fuel sourceOuter region
          sourceFrame targetFrame := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceOuter region site sourceAbove sourceFrame sourceCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ childFuel induction =>
      intro sourceOuter region site sourceAbove sourceFrame sourceCompiled
      by_cases atSite : region = site
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceCompiled
        obtain ⟨sourceBody, sourceBodyCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        have sourceFrameExact :
            ({ visible := sourceOuter.extend site
               siteBody := sourceBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt site) .hole } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        obtain ⟨targetBody, targetBodyCompiled⟩ :=
          compileRegionBody_natural source removed candidateWellFormed
            childFuel sourceOuter site sourceAbove sourceBodyCompiled
        let targetFrame :
            RegionFrame definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (targetContext source removed sourceOuter) :=
          { visible :=
              (targetContext source removed sourceOuter).extend
                (targetRegion source removed site)
            siteBody := targetBody
            context :=
              bindContextFor
                (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                  source removed)
                (targetContext source removed sourceOuter).ids
                ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                  source removed).wiresAt
                    (targetRegion source removed site))
                .hole }
        exact
          ⟨targetFrame,
            ErasureFrameProvenance.site childFuel sourceOuter sourceBody
              targetBody sourceAbove sourceBodyCompiled
              targetBodyCompiled⟩
      · simp only [compileRegionFrame?, atSite, ↓reduceDIte]
          at sourceCompiled
        obtain ⟨sourceNodes, sourceNodesCompiled, afterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨sourceChild, sourceChildFound, afterChild⟩ :=
          Option.bind_eq_some_iff.mp afterNodes
        obtain ⟨sourceNested, sourceNestedCompiled, afterNested⟩ :=
          Option.bind_eq_some_iff.mp afterChild
        obtain ⟨sourceAround, sourceAroundCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp afterNested
        have sourceFrameExact :
            ({ visible := sourceAround.visible
               siteBody := sourceAround.siteBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt region) sourceAround.context } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        have sourceExtendedNodup :
            (sourceOuter.extend region).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions source.val
            source.property sourceOuter region sourceAbove
        obtain ⟨filteredNodes, filteredNodesCompiled⟩ :=
          compileNodes_filter definitions source.val
            (sourceOuter.extend region) removed
            (source.val.nodesAt region) sourceNodesCompiled
        have sourceTargetNodesCompiled :
            ConcreteElaboration.compileNodes? definitions source.val
                (sourceOuter.extend region)
                (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                    source removed).nodesAt
                  (targetRegion source removed region)).map
                  (sourceNode source removed)) =
              some filteredNodes := by
          simpa [targetRegion] using
            (erased_nodesAt_sources source removed region ▸
              filteredNodesCompiled)
        obtain ⟨targetNodes, targetNodesCompiled, _⟩ :=
          survivingNodes_natural source removed candidateWellFormed
            (sourceOuter.extend region) sourceExtendedNodup
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).nodesAt
              (targetRegion source removed region))
            sourceTargetNodesCompiled
        have targetContextExtended :
            targetContext source removed (sourceOuter.extend region) =
              (targetContext source removed sourceOuter).extend
                (targetRegion source removed region) :=
          targetContext_extend source removed sourceOuter region
        have sourceChildMember :
            sourceChild ∈ source.val.childrenOf region :=
          List.mem_of_find?_eq_some sourceChildFound
        have sourceChildAbove :
            ConcreteElaboration.ContextAbove source.val
              (sourceOuter.extend region) sourceChild :=
          ConcreteElaboration.extend_above_child definitions source.val
            source.property sourceOuter region sourceChild sourceAbove
            (ConcreteElaboration.mem_childrenOf source.val region
              sourceChild sourceChildMember)
        obtain ⟨targetNested, nestedProvenance⟩ :=
          induction (sourceOuter.extend region) sourceChild site
            sourceChildAbove sourceNestedCompiled
        have targetNestedCompiled := nestedProvenance.targetGenerated
        have nestedVisible := nestedProvenance.targetVisible
        obtain ⟨targetAround, targetAroundCompiled, aroundVisible,
            siblingProvenance⟩ :=
          compileSiblingFrame_withProvenance source removed
            candidateWellFormed childFuel (sourceOuter.extend region)
            sourceChild sourceNested targetNested nestedVisible sourceNodes
            targetNodes (source.val.childrenOf region) sourceAroundCompiled
            (by
              intro child childMember
              exact
                ConcreteElaboration.extend_above_child definitions
                  source.val source.property sourceOuter region child
                  sourceAbove
                  (ConcreteElaboration.mem_childrenOf source.val region
                    child childMember))
        obtain
            ⟨targetNodes', targetNested', targetAround',
              targetNodesCompiled', targetNestedCompiled',
              targetAroundCompiled', targetNodesExact, targetNestedExact,
              targetAroundExact⟩ :=
          compileFrameBranch_cast_context_withProvenance source removed
            (sourceOuter.extend region) targetContextExtended site childFuel
            sourceChild sourceChild
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).nodesAt
                (targetRegion source removed region))
            (source.val.childrenOf region) targetNodesCompiled
            targetNestedCompiled targetAroundCompiled siblingProvenance
        subst targetNodes'
        subst targetNested'
        subst targetAround'
        let targetFrame :
            RegionFrame definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (targetContext source removed sourceOuter) :=
          { visible :=
              (erasureRebaseRegionFrame targetContextExtended
                targetAround).visible
            siteBody :=
              (erasureRebaseRegionFrame targetContextExtended
                targetAround).siteBody
            context :=
              bindContextFor
                (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                  source removed)
                (targetContext source removed sourceOuter).ids
                ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                  source removed).wiresAt
                    (targetRegion source removed region))
                (erasureRebaseRegionFrame targetContextExtended
                  targetAround).context }
        exact
          ⟨targetFrame,
            ErasureFrameProvenance.ancestor childFuel sourceOuter region
              sourceChild atSite sourceAbove sourceNodes targetNodes
              sourceNested sourceAround targetNested targetAround
              sourceNodesCompiled targetNodesCompiled sourceChildFound
              sourceNestedCompiled sourceAroundCompiled targetAroundCompiled
              siblingProvenance nestedProvenance⟩

/--
One source-accepted frame and its canonical target, retaining the recursive
authority that generated the target.
-/
inductive PairedGeneratedFrame
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (site region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter) : Prop where
  | intro
    (targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter))
    (sourceAbove :
      ConcreteElaboration.ContextAbove source.val sourceOuter region)
    (sourceGenerated :
      compileRegionFrame? definitions source.val site fuel region sourceOuter =
        some sourceFrame)
    (provenance :
      ErasureFrameProvenance source removed site fuel sourceOuter region
        sourceFrame targetFrame) :
    PairedGeneratedFrame source removed site region fuel sourceOuter
      sourceFrame

/-- Generate the canonical target receipt from the accepted source traversal. -/
theorem pairedGeneratedFrame
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (site region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove source.val sourceOuter region)
    (sourceGenerated :
      compileRegionFrame? definitions source.val site fuel region sourceOuter =
        some sourceFrame) :
    PairedGeneratedFrame source removed site region fuel sourceOuter
      sourceFrame := by
  obtain ⟨targetFrame, provenance⟩ :=
    compileRegionFrame_withProvenance source removed
      erasure.candidate_wellFormed fuel sourceOuter region site sourceAbove
      sourceGenerated
  exact .intro targetFrame sourceAbove sourceGenerated provenance

/-- Project a relation-join receipt into the canonical paired frame receipt. -/
theorem RelationJoinStep.pairedGeneratedFrame
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (sourceFrame :
      RegionFrame definitions step.prior.val sourceOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove step.prior.val sourceOuter region)
    (sourceGenerated :
      compileRegionFrame? definitions step.prior.val site fuel region
          sourceOuter =
        some sourceFrame) :
    PairedGeneratedFrame step.prior step.priorApplication site region fuel
      sourceOuter sourceFrame :=
  SingletonRemovalSemantics.pairedGeneratedFrame
    step.prior step.priorApplication
    (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
      site region fuel sourceOuter sourceFrame
    sourceAbove sourceGenerated

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
