import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinAboveScope
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalCompiler

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

open Internal

/--
Truncate the two exact frame provenances together at an enclosing source
scope.  The current region is tested before either binder block is crossed, so
the completed scope expression remains the unique hole body.
-/
private theorem RelationJoinStep.compileNodes_rebaseItemSeq
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (nodes : List diagram.NodeId)
    {items : ItemSeq definitions left.sigs}
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram left nodes =
        some items) :
    ConcreteElaboration.compileNodes? definitions diagram right nodes =
      some
        (InsertionCompilation.NaturalityInternal.rebaseItemSeq same
          items) := by
  cases same
  exact compiled

private theorem RelationJoinStep.contextAbove_rebaseOuter
    {definitionCount : Nat}
    {diagram : ConcreteDiagram definitionCount}
    {left right : ConcreteElaboration.WireContext diagram}
    {region : diagram.RegionId}
    (same : left = right)
    (above : ConcreteElaboration.ContextAbove diagram left region) :
    ConcreteElaboration.ContextAbove diagram right region := by
  cases same
  exact above

private theorem RelationJoinStep.envComp_rebase
    {definitions : List (List Sig)}
    {sourceContext middleContext : List Sig}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (outer : WireRenaming middleContext left.sigs)
    (inner : WireRenaming sourceContext middleContext) :
    (fun (pre : PreModel.{u}) (env : Env pre right.sigs) =>
      Env.comp
        (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ env)
        (fun {_} value => outer (inner value))) =
      (fun (pre : PreModel.{u}) (env : Env pre right.sigs) =>
        Env.comp env
          (fun {_} value =>
            (congrArg ConcreteElaboration.WireContext.sigs same ▸ outer)
              (inner value))) := by
  cases same
  rfl

private theorem RelationJoinStep.rebaseGeneratedFrame_trans
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left middle right : ConcreteElaboration.WireContext diagram}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (frame : RegionFrame definitions diagram left) :
    InsertionCompilation.NaturalityInternal.rebaseRegionFrame
        (leftMiddle.trans middleRight) frame =
      InsertionCompilation.NaturalityInternal.rebaseRegionFrame middleRight
        (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
          leftMiddle frame) := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem RelationJoinStep.rebaseGeneratedFrame_exact
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    InsertionCompilation.NaturalityInternal.rebaseRegionFrame same frame =
      { visible := frame.visible
        siteBody := frame.siteBody
        context :=
          congrArg ConcreteElaboration.WireContext.sigs same ▸
            frame.context } := by
  cases same
  rfl

private theorem RelationJoinStep.rebaseGeneratedFrameProvenance
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {fuel : Nat}
    {left right siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val left}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          left)}
    (same : left = right)
    (sourceGenerated :
      compileRegionFrame? definitions base.val site fuel region left =
        some sourceFrame)
    (provenance :
      InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance
        compiled fuel left siteOuter region sourceFrame targetFrame) :
    compileRegionFrame? definitions base.val site fuel region right =
        some
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceFrame) ∧
      compileRegionFrame? definitions attachment.diagram
          (attachment.hostRegion site)
          (fuel + fragment.val.diagram.regionCount)
          (attachment.hostRegion region)
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            right) =
        some
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetFrame) ∧
      InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance
        compiled fuel right siteOuter region
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceFrame)
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetFrame) ∧
      congrArg ConcreteElaboration.WireContext.sigs same ▸
          sourceFrame.context.fill sourceFrame.siteBody =
        (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
          sourceFrame).context.fill
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceFrame).siteBody ∧
      congrArg ConcreteElaboration.WireContext.sigs
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same) ▸
          targetFrame.context.fill targetFrame.siteBody =
        (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
          (congrArg
            (InsertionCompilation.NaturalityInternal.hostContext attachment)
            same)
          targetFrame).context.fill
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetFrame).siteBody := by
  cases same
  exact ⟨sourceGenerated, provenance.targetGenerated, provenance, rfl, rfl⟩

private theorem RelationJoinStep.rebaseGeneratedSiblingProvenance
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {left right : ConcreteElaboration.WireContext base.val}
    {selected : base.val.RegionId}
    {sourceNested sourceFrame :
      RegionFrame definitions base.val left}
    {targetNested targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          left)}
    {sourceLeading : ItemSeq definitions left.sigs}
    {targetLeading :
      ItemSeq definitions
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          left).sigs}
    {children : List base.val.RegionId}
    (same : left = right)
    (provenance :
      InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance
        compiled sourceFuel targetFuel left
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            left)
          selected sourceNested targetNested sourceLeading targetLeading
          children sourceFrame targetFrame) :
    InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance
        compiled sourceFuel targetFuel right
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            right)
          selected
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceNested)
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetNested)
          (InsertionCompilation.NaturalityInternal.rebaseItemSeq same
            sourceLeading)
          (InsertionCompilation.NaturalityInternal.rebaseItemSeq
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetLeading)
          children
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceFrame)
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetFrame) ∧
      compileSiblingFrame? definitions base.val sourceFuel right selected
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceNested)
          (InsertionCompilation.NaturalityInternal.rebaseItemSeq same
            sourceLeading)
          children =
        some
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame same
            sourceFrame) ∧
      compileSiblingFrame? definitions attachment.diagram targetFuel
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            right)
          (attachment.hostRegion selected)
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetNested)
          (InsertionCompilation.NaturalityInternal.rebaseItemSeq
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetLeading)
          (children.map attachment.hostRegion) =
        some
          (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
            (congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              same)
            targetFrame) := by
  cases same
  exact ⟨provenance, provenance.sourceGenerated, provenance.targetGenerated⟩

private theorem RelationJoinStep.pairedFrameAboveScope
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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
    (baseFrameExact : insertionBaseFrame = baseFrame)
    (scope : source.val.RegionId)
    (regionScope : source.val.Encloses region scope)
    (scopeSite :
      source.val.Encloses scope (source.val.nodes removed).region) :
    ∃ receipt :
        RelationJoinStep.PairedAboveScopeReflection.{u} source removed
          candidateWellFormed compiled scope sourceOuter sourceFrame
          targetFrame,
      compileRegionFrame? definitions source.val scope fuel region
          sourceOuter =
        some receipt.sourceStopped ∧
      compileRegionFrame? definitions attachment.diagram
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed scope))
          (fuel + fragment.val.diagram.regionCount)
          (attachment.hostRegion
            (SingletonRemovalSemantics.targetRegion source removed region))
          (InsertionCompilation.NaturalityInternal.hostContext attachment
            (SingletonRemovalSemantics.targetContext source removed
              sourceOuter)) =
        some receipt.targetStopped := by
  subst insertionBaseFrame
  induction erasure generalizing scope siteOuter with
  | site childFuel sourceOuter sourceBody baseBody sourceAbove
      sourceBodyCompiled baseBodyCompiled =>
      have scopeExact :
          (source.val.nodes removed).region = scope :=
        factor_encloses_antisymm definitions source.val source.property
          regionScope scopeSite
      subst scope
      exact
        RelationJoinStep.pairedStopAboveCurrent source removed
          candidateWellFormed compiled
          (.site childFuel sourceOuter sourceBody baseBody sourceAbove
            sourceBodyCompiled baseBodyCompiled)
          insertion rfl
  | ancestor childFuel sourceOuter region selected notSite sourceAbove
      sourceNodes baseNodes sourceNested sourceAround baseNested baseAround
      sourceNodesCompiled baseNodesCompiled selectedFound
      sourceNestedCompiled sourceAroundCompiled baseAroundCompiled
      erasureSiblings erasureNested induction =>
      by_cases currentScope : region = scope
      · subst scope
        exact
          RelationJoinStep.pairedStopAboveCurrent source removed
            candidateWellFormed compiled
            (.ancestor childFuel sourceOuter region selected notSite
              sourceAbove sourceNodes baseNodes sourceNested sourceAround
              baseNested baseAround sourceNodesCompiled baseNodesCompiled
              selectedFound sourceNestedCompiled sourceAroundCompiled
              baseAroundCompiled erasureSiblings erasureNested)
            insertion rfl
      · refine
          InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance.rec
            (base := singletonErasureBase source removed candidateWellFormed)
            (site :=
              SingletonRemovalSemantics.targetRegion source removed
                (source.val.nodes removed).region)
            (fragment := fragment) (fragmentCompiled := fragmentCompiled)
            (attachment := attachment) (compiled := compiled)
            (motive := fun insertionFuel insertionOuter _ insertionRegion
                insertionBase insertionTarget _ =>
              insertionFuel = childFuel + 1 →
              insertionOuter =
                  SingletonRemovalSemantics.targetContext source removed
                    sourceOuter →
              insertionRegion =
                  SingletonRemovalSemantics.targetRegion source removed
                    region →
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
                          (SingletonRemovalSemantics.targetRegion source
                            removed region))
                        (SingletonRemovalSemantics.erasureRebaseRegionFrame
                          (SingletonRemovalSemantics.targetContext_extend source
                            removed sourceOuter region)
                          baseAround).context }) →
              HEq insertionTarget targetFrame →
              ∃ receipt :
                  RelationJoinStep.PairedAboveScopeReflection.{u} source
                    removed candidateWellFormed compiled scope sourceOuter
                    { visible := sourceAround.visible
                      siteBody := sourceAround.siteBody
                      context :=
                        bindContextFor source.val sourceOuter.ids
                          (source.val.wiresAt region) sourceAround.context }
                    targetFrame,
                compileRegionFrame? definitions source.val scope
                      (childFuel + 1) region sourceOuter =
                  some receipt.sourceStopped ∧
                compileRegionFrame? definitions attachment.diagram
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          scope))
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
          intro fuelExact outerExact regionExact insertionBaseExact
            targetExact
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
            otherOutside allChildrenAbove insertionNested insertionInduction
          intro fuelExact outerExact regionExact insertionBaseExact targetExact
          subst baseOuter
          cases regionExact
          cases targetExact
          have insertionFuelExact : insertionFuel = childFuel := by omega
          subst insertionFuel
          let baseContextExact :
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter).extend
                  (SingletonRemovalSemantics.targetRegion source removed
                    region) =
                SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region) :=
            (SingletonRemovalSemantics.targetContext_extend source removed
              sourceOuter region).symm
          let nestedTargetContextExact :=
            congrArg
              (InsertionCompilation.NaturalityInternal.hostContext
                attachment)
              baseContextExact
          let canonicalBaseNodes :=
            InsertionCompilation.NaturalityInternal.rebaseItemSeq
              baseContextExact insertionBaseNodes
          let canonicalTargetNodes :=
            InsertionCompilation.NaturalityInternal.rebaseItemSeq
              nestedTargetContextExact targetNodes
          let canonicalBaseNested :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              baseContextExact insertionBaseNested
          let canonicalTargetNested :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              nestedTargetContextExact targetNested
          let canonicalBaseAround :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              baseContextExact insertionBaseAround
          let canonicalTargetAround :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              nestedTargetContextExact targetAround
          have canonicalBaseNodesCompiled :
              ConcreteElaboration.compileNodes? definitions
                  (singletonErasureBase source removed
                    candidateWellFormed).val
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))
                  ((singletonErasureBase source removed
                    candidateWellFormed).val.nodesAt
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)) =
                some canonicalBaseNodes := by
            exact
              RelationJoinStep.compileNodes_rebaseItemSeq baseContextExact _
                insertionBaseNodesCompiled
          have canonicalTargetNodesCompiled :
              ConcreteElaboration.compileNodes? definitions
                  attachment.diagram
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      (sourceOuter.extend region)))
                  (((singletonErasureBase source removed
                    candidateWellFormed).val.nodesAt
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)).map attachment.hostNode) =
                some canonicalTargetNodes := by
            exact
              RelationJoinStep.compileNodes_rebaseItemSeq
                nestedTargetContextExact _ targetNodesCompiled
          obtain ⟨canonicalBaseNestedCompiled,
              canonicalTargetNestedCompiled, canonicalInsertionNested,
              canonicalBaseNestedFill, canonicalTargetNestedFill⟩ :=
            RelationJoinStep.rebaseGeneratedFrameProvenance
              baseContextExact insertionBaseNestedCompiled insertionNested
          change
            compileRegionFrame? definitions
                (singletonErasureBase source removed
                  candidateWellFormed).val
                (SingletonRemovalSemantics.targetRegion source removed
                  (source.val.nodes removed).region)
                childFuel
                baseSelected
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region)) =
              some canonicalBaseNested at canonicalBaseNestedCompiled
          change
            compileRegionFrame? definitions attachment.diagram
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    (source.val.nodes removed).region))
                (childFuel + fragment.val.diagram.regionCount)
                (attachment.hostRegion baseSelected)
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))) =
              some canonicalTargetNested at canonicalTargetNestedCompiled
          change
            InsertionCompilation.NaturalityInternal.GeneratedFrameProvenance
              compiled childFuel
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region))
                insertionSiteOuter
                baseSelected
                canonicalBaseNested canonicalTargetNested
              at canonicalInsertionNested
          obtain ⟨canonicalInsertionSiblings,
              canonicalBaseAroundCompiled,
              canonicalTargetAroundCompiled⟩ :=
            RelationJoinStep.rebaseGeneratedSiblingProvenance
              baseContextExact insertionSiblings
          change
            InsertionCompilation.NaturalityInternal.GeneratedSiblingProvenance
              compiled childFuel
                (childFuel + fragment.val.diagram.regionCount)
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region))
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region)))
                baseSelected
                canonicalBaseNested canonicalTargetNested
                canonicalBaseNodes canonicalTargetNodes
                ((singletonErasureBase source removed
                  candidateWellFormed).val.childrenOf
                  (SingletonRemovalSemantics.targetRegion source removed
                    region))
                canonicalBaseAround canonicalTargetAround
              at canonicalInsertionSiblings
          change
            compileSiblingFrame? definitions
                (singletonErasureBase source removed
                  candidateWellFormed).val childFuel
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region))
                baseSelected
                canonicalBaseNested canonicalBaseNodes
                ((singletonErasureBase source removed
                  candidateWellFormed).val.childrenOf
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)) =
              some canonicalBaseAround at canonicalBaseAroundCompiled
          change
            compileSiblingFrame? definitions attachment.diagram
                (childFuel + fragment.val.diagram.regionCount)
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region)))
                (attachment.hostRegion baseSelected)
                canonicalTargetNested canonicalTargetNodes
                (((singletonErasureBase source removed
                  candidateWellFormed).val.childrenOf
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)).map attachment.hostRegion) =
              some canonicalTargetAround at canonicalTargetAroundCompiled
          have selectedMember :
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
                source.property regionScope (Ne.symm currentScope)
                selectedData selectedSite scopeSite
          have scopeSelectedFound :
              (source.val.childrenOf region).find?
                  (fun candidate =>
                    decide (source.val.Encloses candidate scope)) =
                some selected := by
            apply
              RelationJoinStep.find?_eq_some_of_unique_true
                (source.val.childrenOf region) selected
                (fun candidate =>
                  decide (source.val.Encloses candidate scope))
                selectedMember
                (decide_eq_true selectedScope)
            intro candidate member candidateScope
            have candidateScope' :
                source.val.Encloses candidate scope :=
              of_decide_eq_true candidateScope
            exact
              SingletonRemovalSemantics.enclosing_children_unique source
                region candidate selected (source.val.nodes removed).region
                member selectedMember
                (ExhaustedWireRemovalSemantics.checked_encloses_trans source
                  candidateScope' scopeSite)
                selectedSite
          have baseSelectedExact :
              baseSelected =
                SingletonRemovalSemantics.targetRegion source removed
                  selected := by
            change
              ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed).childrenOf
                (SingletonRemovalSemantics.targetRegion source removed
                  region)).find?
                  (fun candidate =>
                    decide
                      ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                        source removed).Encloses candidate
                        (SingletonRemovalSemantics.targetRegion source removed
                          (source.val.nodes removed).region))) =
                some baseSelected at baseSelectedFound
            apply Option.some.inj
            calc
              some baseSelected =
                  ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                    source removed).childrenOf
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)).find?
                    (fun candidate =>
                      decide
                        ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                          source removed).Encloses candidate
                          (SingletonRemovalSemantics.targetRegion source
                            removed (source.val.nodes removed).region))) :=
                baseSelectedFound.symm
              _ = some
                  (SingletonRemovalSemantics.targetRegion source removed
                      selected) := by
                rw [SingletonRemovalSemantics.target_childrenOf,
                  SingletonRemovalSemantics.target_find_enclosing,
                  selectedFound]
                rfl
          subst baseSelected
          have baseNestedExact : canonicalBaseNested = baseNested :=
            Option.some.inj
              (canonicalBaseNestedCompiled.symm.trans
                erasureNested.targetGenerated)
          rw [baseNestedExact] at canonicalInsertionNested canonicalInsertionSiblings canonicalBaseAroundCompiled
          obtain ⟨nestedReceipt, nestedSourceStoppedCompiled,
              nestedTargetStoppedCompiled⟩ :=
            induction
              (insertion := canonicalInsertionNested)
              (scope := scope)
              selectedScope scopeSite
          have baseNodesExact : canonicalBaseNodes = baseNodes :=
            Option.some.inj
              (canonicalBaseNodesCompiled.symm.trans baseNodesCompiled)
          rw [baseNodesExact] at canonicalInsertionSiblings canonicalBaseAroundCompiled
          simp only [singletonErasureBase] at canonicalInsertionSiblings canonicalBaseAroundCompiled
          rw [SingletonRemovalSemantics.target_childrenOf] at canonicalInsertionSiblings canonicalBaseAroundCompiled
          have baseAroundExact : canonicalBaseAround = baseAround :=
            Option.some.inj
              (canonicalBaseAroundCompiled.symm.trans
                baseAroundCompiled)
          rw [baseAroundExact] at canonicalInsertionSiblings
          have sourceExtendedNodup :
              (sourceOuter.extend region).ids.Nodup :=
            ConcreteElaboration.extend_nodup definitions source.val
              source.property sourceOuter region sourceAbove
          have sourceChildrenNodup :
              (source.val.childrenOf region).Nodup := by
            unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
            exact
              (Data.Finite.allFin_nodup source.val.regionCount).filter _
          have allSourceAbove :
              ∀ child, child ∈ source.val.childrenOf region →
                ConcreteElaboration.ContextAbove source.val
                  (sourceOuter.extend region) child := by
            intro child member
            exact
              ConcreteElaboration.extend_above_child definitions source.val
                source.property sourceOuter region child sourceAbove
                (ConcreteElaboration.mem_childrenOf source.val region child
                  member)
          have sourceOutside :
              ∀ child, child ∈ source.val.childrenOf region →
                child ≠ selected →
                  ¬source.val.Encloses child
                    (source.val.nodes removed).region := by
            intro child member different childSite
            exact different
              (SingletonRemovalSemantics.enclosing_children_unique source
                region child selected (source.val.nodes removed).region
                member selectedMember childSite selectedSite)
          have baseOutside :
              ∀ child, child ∈ source.val.childrenOf region →
                child ≠ selected →
                  ¬(singletonErasureBase source removed
                    candidateWellFormed).val.Encloses
                    (SingletonRemovalSemantics.targetRegion source removed
                      child)
                      (SingletonRemovalSemantics.targetRegion source removed
                        (source.val.nodes removed).region) := by
            intro child member different
            apply otherOutside
            · simpa only [singletonErasureBase,
                SingletonRemovalSemantics.target_childrenOf] using
                (List.mem_map.mpr ⟨child, member, rfl⟩)
            · intro same
              exact different
                (SingletonRemovalSemantics.targetRegion_injective source
                  removed same)
          have targetAboveForSource :
              ∀ child, child ∈ source.val.childrenOf region →
                ConcreteElaboration.ContextAbove attachment.diagram
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      (sourceOuter.extend region)))
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      child)) := by
            intro child member
            apply
              RelationJoinStep.contextAbove_rebaseOuter
                nestedTargetContextExact
            exact
              allChildrenAbove
                (SingletonRemovalSemantics.targetRegion source removed child)
                (by
                  simpa only [singletonErasureBase,
                    SingletonRemovalSemantics.target_childrenOf] using
                    (List.mem_map.mpr ⟨child, member, rfl⟩))
          have leadingPriorBase :
              ∀ (pre : PreModel.{u})
                (definitionEnv : DefinitionEnv pre definitions)
                (env :
                  Env pre
                    (SingletonRemovalSemantics.targetContext source removed
                      (sourceOuter.extend region)).sigs),
                denoteItemSeq pre definitionEnv env baseNodes ↔
                  denoteItemSeq pre definitionEnv
                    (Env.comp env
                      (SingletonRemovalSemantics.contextRenaming source
                        removed (sourceOuter.extend region)))
                    sourceNodes := by
            intro pre definitionEnv env
            exact
              SingletonRemovalSemantics.compiledNodes_outside source removed
                candidateWellFormed (sourceOuter.extend region)
                sourceExtendedNodup region
                (SingletonRemovalSemantics.removed_not_mem_nodesAt_of_ne
                  source removed region notSite)
                sourceNodesCompiled baseNodesCompiled pre definitionEnv env
          have targetCanonicalNodup :=
            (targetAboveForSource selected selectedMember).1
          obtain ⟨naturalTargetNodes, naturalTargetNodesCompiled,
              naturalTargetNodesShape⟩ :=
            InsertionCompilation.NaturalityInternal.copiedHostNodes_natural
              compiled
              (SingletonRemovalSemantics.targetContext source removed
                (sourceOuter.extend region))
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region)))
              targetCanonicalNodup
              (InsertionCompilation.NaturalityInternal.hostContextRenaming
                attachment
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region)))
              (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region)))
              ((singletonErasureBase source removed
                candidateWellFormed).val.nodesAt
                  (SingletonRemovalSemantics.targetRegion source removed
                    region))
              baseNodesCompiled
          have targetNodesShape :
              canonicalTargetNodes =
                baseNodes.renameWires
                  (InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        (sourceOuter.extend region))) := by
            have exactNodes : naturalTargetNodes = canonicalTargetNodes :=
              Option.some.inj
                (naturalTargetNodesCompiled.symm.trans
                  canonicalTargetNodesCompiled)
            exact exactNodes.symm.trans naturalTargetNodesShape
          have leadingBaseTarget :
              ∀ (pre : PreModel.{u})
                (definitionEnv : DefinitionEnv pre definitions)
                (env :
                  Env pre
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        (sourceOuter.extend region))).sigs),
                denoteItemSeq pre definitionEnv env canonicalTargetNodes ↔
                  denoteItemSeq pre definitionEnv
                    (Env.comp env
                      (InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed (sourceOuter.extend region))))
                    baseNodes := by
            intro pre definitionEnv env
            rw [targetNodesShape, denoteItemSeq_renameWires]
          obtain ⟨aroundReceipt, sourceAroundStoppedCompiled,
              targetAroundStoppedCompiled⟩ :=
            RelationJoinStep.pairedSiblingAboveScope source removed
              candidateWellFormed compiled childFuel
              (sourceOuter.extend region) selected scope erasureSiblings
              canonicalInsertionSiblings rfl
              rfl
              sourceChildrenNodup selectedMember allSourceAbove sourceOutside
              baseOutside targetAboveForSource nestedReceipt
              leadingPriorBase leadingBaseTarget
          let targetContextExact :=
            nestedTargetContextExact.symm.trans
              (InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
                  compiled
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)
                  baseNotSite)
          let targetOuterSigsExact :=
            congrArg ConcreteElaboration.WireContext.sigs targetContextExact
          have rebasedComposableRaw :=
            aroundReceipt.composable.rebaseTargetOuter targetOuterSigsExact
          have targetCurrentAbove :=
            InsertionCompilation.NaturalityInternal.hostContext_above compiled
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)
              (SingletonRemovalSemantics.targetRegion source removed region)
              baseAbove
          have targetExtendedNodup :=
            ConcreteElaboration.extend_nodup definitions attachment.diagram
              compiled.generated_wellFormed
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceOuter))
              (attachment.hostRegion
                (SingletonRemovalSemantics.targetRegion source removed
                  region))
              targetCurrentAbove
          have rebasedComposable :
              DiagramContext.ComposableSemanticZipper
                aroundReceipt.sourceAbove
                (targetOuterSigsExact ▸ aroundReceipt.targetAbove)
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostExtendedRenaming compiled
                          (SingletonRemovalSemantics.targetRegion source
                            removed region)
                          baseNotSite
                          (SingletonRemovalSemantics.targetContext source
                            removed sourceOuter)
                          (InsertionCompilation.NaturalityInternal.hostContext
                            attachment
                            (SingletonRemovalSemantics.targetContext source
                              removed sourceOuter))
                          (InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter))
                          (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter))
                          (SingletonRemovalSemantics.extendedContextRenaming
                            source removed sourceOuter region value)))
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed aroundReceipt.sourceSiteOuter value))) := by
            have throughCompositeExact :
                (fun {sig : Sig}
                    (value : Var (sourceOuter.extend region).sigs sig) =>
                  InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      (sourceOuter.extend region))
                    ((InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).extend
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)))
                    targetContextExact
                    (SingletonRemovalSemantics.contextRenaming source removed
                      (sourceOuter.extend region) value)) =
                  (fun {sig : Sig}
                      (value : Var (sourceOuter.extend region).sigs sig) =>
                    InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                      attachment
                      ((SingletonRemovalSemantics.targetContext source removed
                        sourceOuter).extend
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))
                      ((InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)).extend
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source removed
                            region)))
                      (InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
                        compiled
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)
                        baseNotSite)
                      (SingletonRemovalSemantics.extendedContextRenaming
                        source removed sourceOuter region value)) := by
              funext sig value
              apply
                InsertionCompilation.NaturalityInternal.origin_injective
                  attachment.diagram _ targetExtendedNodup
              calc
                _ =
                    attachment.hostWire
                      (ConcreteElaboration.WireContext.origin
                        (singletonErasureBase source removed
                          candidateWellFormed).val
                        (SingletonRemovalSemantics.targetContext source removed
                          (sourceOuter.extend region)).ids
                        (SingletonRemovalSemantics.contextRenaming source
                          removed (sourceOuter.extend region) value)) := by
                      unfold
                        InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                      rw [origin_cast_renaming attachment.diagram
                          targetContextExact,
                        InsertionCompilation.NaturalityInternal.hostContextRenaming_origin]
                _ =
                    attachment.hostWire
                      (SingletonRemovalSemantics.targetWire source removed
                        (ConcreteElaboration.WireContext.origin source.val
                          (sourceOuter.extend region).ids value)) := by
                      exact
                        congrArg attachment.hostWire
                          (by
                            simpa only [singletonErasureBase] using
                              SingletonRemovalSemantics.contextRenaming_action
                                source removed (sourceOuter.extend region)
                                value)
                _ =
                    attachment.hostWire
                      (ConcreteElaboration.WireContext.origin
                        (singletonErasureBase source removed
                          candidateWellFormed).val
                        ((SingletonRemovalSemantics.targetContext source
                          removed sourceOuter).extend
                          (SingletonRemovalSemantics.targetRegion source
                            removed region)).ids
                        (SingletonRemovalSemantics.extendedContextRenaming
                          source removed sourceOuter region value)) := by
                      exact
                        congrArg attachment.hostWire
                          (by
                            simpa only [singletonErasureBase] using
                              (extendedContextRenaming_origin source removed
                                sourceOuter region value).symm)
                _ =
                    ConcreteElaboration.WireContext.origin attachment.diagram
                      (InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        ((SingletonRemovalSemantics.targetContext source
                          removed sourceOuter).extend
                          (SingletonRemovalSemantics.targetRegion source
                            removed region))).ids
                      (InsertionCompilation.NaturalityInternal.hostContextRenaming
                        attachment
                        ((SingletonRemovalSemantics.targetContext source
                          removed sourceOuter).extend
                          (SingletonRemovalSemantics.targetRegion source
                            removed region))
                        (SingletonRemovalSemantics.extendedContextRenaming
                          source removed sourceOuter region value)) := by
                      exact
                        (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin
                          attachment
                          ((SingletonRemovalSemantics.targetContext source
                            removed sourceOuter).extend
                            (SingletonRemovalSemantics.targetRegion source
                              removed region))
                          _).symm
                _ = _ := by
                  unfold
                    InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                  exact
                    (origin_cast_renaming attachment.diagram
                      (InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
                        compiled
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)
                        baseNotSite)
                      _ _ _).symm
            have throughExtendedExact :
                (fun {sig : Sig}
                    (value : Var (sourceOuter.extend region).sigs sig) =>
                  InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                    attachment
                    ((SingletonRemovalSemantics.targetContext source removed
                      sourceOuter).extend
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))
                    ((InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).extend
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)))
                    (InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
                      compiled
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)
                      baseNotSite)
                    (SingletonRemovalSemantics.extendedContextRenaming
                      source removed sourceOuter region value)) =
                  (fun {sig : Sig}
                      (value : Var (sourceOuter.extend region).sigs sig) =>
                    InsertionCompilation.NaturalityInternal.hostExtendedRenaming
                      compiled
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)
                      baseNotSite
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)
                      (InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter))
                      (InsertionCompilation.NaturalityInternal.hostContextRenaming
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter))
                      (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter))
                      (SingletonRemovalSemantics.extendedContextRenaming
                        source removed sourceOuter region value)) := by
              have hostExtendedExact :=
                InsertionCompilation.NaturalityInternal.hostContextRenamingThrough_extend
                  compiled
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)
                  (SingletonRemovalSemantics.targetRegion source removed region)
                  baseNotSite targetExtendedNodup
              funext sig value
              exact
                congrFun (congrFun hostExtendedExact sig)
                  (SingletonRemovalSemantics.extendedContextRenaming source
                    removed sourceOuter region value)
            have outerMapExact :
                (fun (pre : PreModel.{u})
                  (env :
                    Env pre
                      ((InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)).extend
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source
                            removed region))).sigs) =>
                  Env.comp
                    (targetOuterSigsExact.symm ▸ env)
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed (sourceOuter.extend region))
                          (SingletonRemovalSemantics.contextRenaming source
                            removed (sourceOuter.extend region) value))) =
                (fun (pre : PreModel.{u})
                  (env :
                    Env pre
                      ((InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)).extend
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source
                            removed region))).sigs) =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostExtendedRenaming compiled
                          (SingletonRemovalSemantics.targetRegion source
                            removed region)
                          baseNotSite
                          (SingletonRemovalSemantics.targetContext source
                            removed sourceOuter)
                          (InsertionCompilation.NaturalityInternal.hostContext
                            attachment
                            (SingletonRemovalSemantics.targetContext source
                              removed sourceOuter))
                          (InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter))
                          (InsertionCompilation.NaturalityInternal.hostContextRenaming_origin attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter))
                          (SingletonRemovalSemantics.extendedContextRenaming
                            source removed sourceOuter region value))) := by
              calc
                _ =
                    (fun (pre : PreModel.{u})
                      (env :
                        Env pre
                          ((InsertionCompilation.NaturalityInternal.hostContext
                            attachment
                            (SingletonRemovalSemantics.targetContext source
                              removed sourceOuter)).extend
                            (attachment.hostRegion
                              (SingletonRemovalSemantics.targetRegion source
                                removed region))).sigs) =>
                      Env.comp env
                        (fun {_} value =>
                          InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                            attachment
                            (SingletonRemovalSemantics.targetContext source
                              removed (sourceOuter.extend region))
                            ((InsertionCompilation.NaturalityInternal.hostContext
                              attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter)).extend
                              (attachment.hostRegion
                                (SingletonRemovalSemantics.targetRegion source
                                  removed region)))
                            targetContextExact
                            (SingletonRemovalSemantics.contextRenaming source
                              removed (sourceOuter.extend region) value))) := by
                        simpa only
                          [InsertionCompilation.NaturalityInternal.hostContextRenamingThrough]
                          using
                            (RelationJoinStep.envComp_rebase
                              (definitions := definitions)
                              targetContextExact
                              (InsertionCompilation.NaturalityInternal.hostContextRenaming
                                attachment
                                (SingletonRemovalSemantics.targetContext source
                                  removed (sourceOuter.extend region)))
                              (SingletonRemovalSemantics.contextRenaming source
                                removed (sourceOuter.extend region)))
                _ =
                    (fun (pre : PreModel.{u})
                      (env :
                        Env pre
                          ((InsertionCompilation.NaturalityInternal.hostContext
                            attachment
                            (SingletonRemovalSemantics.targetContext source
                              removed sourceOuter)).extend
                            (attachment.hostRegion
                              (SingletonRemovalSemantics.targetRegion source
                                removed region))).sigs) =>
                      Env.comp env
                        (fun {_} value =>
                          InsertionCompilation.NaturalityInternal.hostContextRenamingThrough
                            attachment
                            ((SingletonRemovalSemantics.targetContext source
                              removed sourceOuter).extend
                              (SingletonRemovalSemantics.targetRegion source
                                removed region))
                            ((InsertionCompilation.NaturalityInternal.hostContext
                              attachment
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter)).extend
                              (attachment.hostRegion
                                (SingletonRemovalSemantics.targetRegion source
                                  removed region)))
                            (InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
                              compiled
                              (SingletonRemovalSemantics.targetContext source
                                removed sourceOuter)
                              (SingletonRemovalSemantics.targetRegion source
                                removed region)
                              baseNotSite)
                            (SingletonRemovalSemantics.extendedContextRenaming
                              source removed sourceOuter region value))) := by
                        rw [throughCompositeExact]
                _ = _ := by rw [throughExtendedExact]
            rw [← outerMapExact]
            exact rebasedComposableRaw
          let sourceAncestor :=
            bindContextFor source.val sourceOuter.ids
              (source.val.wiresAt region) aroundReceipt.sourceAbove
          let targetAncestor :=
            bindContextFor attachment.diagram
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                (SingletonRemovalSemantics.targetContext source removed
                  sourceOuter)).ids
              (attachment.diagram.wiresAt
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)))
              (targetOuterSigsExact ▸ aroundReceipt.targetAbove)
          let targetBinderContextExact :
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region))).sigs =
                ((attachment.diagram.wiresAt
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))) ++
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).ids).map
                    (fun wire => (attachment.diagram.wires wire).sig) := by
            exact targetOuterSigsExact
          let bound :
              List Sig :=
            (source.val.wiresAt region).map
              (fun wire => (source.val.wires wire).sig)
          let sourceBinderSigsExact :
              (sourceOuter.extend region).sigs =
                bound ++ sourceOuter.sigs := by
            unfold bound ConcreteElaboration.WireContext.extend
              ConcreteElaboration.WireContext.sigs
            exact List.map_append
          let targetLocalSigsExact :
              (attachment.diagram.wiresAt
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      region))).map
                    (fun wire => (attachment.diagram.wires wire).sig) =
                bound := by
            exact
              (InsertionCompilation.NaturalityInternal.hostRegionLocalSigs_eq
                compiled
                (SingletonRemovalSemantics.targetRegion source removed region)
                baseNotSite).trans
                (RelationJoinStep.erasureRegionLocalSigs_eq source removed
                  sourceOuter region)
          let targetMapAppendExact :
              ((attachment.diagram.wiresAt
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      region))) ++
                (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).ids).map
                    (fun wire => (attachment.diagram.wires wire).sig) =
                (attachment.diagram.wiresAt
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))).map
                      (fun wire => (attachment.diagram.wires wire).sig) ++
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).sigs := by
            exact List.map_append
          let targetCanonicalSigsExact :
              ((InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).extend
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    region))).sigs =
                bound ++
                  (InsertionCompilation.NaturalityInternal.hostContext attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).sigs := by
            calc
              _ =
                  ((attachment.diagram.wiresAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))) ++
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).ids).map
                      (fun wire => (attachment.diagram.wires wire).sig) :=
                targetOuterSigsExact.symm.trans targetBinderContextExact
              _ =
                  (attachment.diagram.wiresAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))).map
                        (fun wire => (attachment.diagram.wires wire).sig) ++
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).sigs := by
                exact List.map_append
              _ = _ := by rw [targetLocalSigsExact]
          let sourceStoppedAncestor :
              RegionFrame definitions source.val sourceOuter :=
            { visible := aroundReceipt.sourceStopped.visible
              siteBody := aroundReceipt.sourceStopped.siteBody
              context :=
                bindContextFor source.val sourceOuter.ids
                  (source.val.wiresAt region)
                  aroundReceipt.sourceStopped.context }
          let targetStoppedAncestor :
              RegionFrame definitions attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)) :=
            { visible := aroundReceipt.targetStopped.visible
              siteBody := aroundReceipt.targetStopped.siteBody
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
                  (targetBinderContextExact ▸
                    aroundReceipt.targetStopped.context) }
          let sourceToBaseExtended :
              WireRenaming
                (sourceOuter.extend region).sigs
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region)).sigs :=
            SingletonRemovalSemantics.contextRenaming source removed
              (sourceOuter.extend region)
          let baseToRawExtended :
              WireRenaming
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region)).sigs
                (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))).sigs :=
            InsertionCompilation.NaturalityInternal.hostContextRenaming
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                (sourceOuter.extend region))
          let rawFullRenaming :
              WireRenaming
                (sourceOuter.extend region).sigs
                (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))).sigs :=
            fun {_} value =>
              baseToRawExtended (sourceToBaseExtended value)
          have rawTargetExtendedNodup :
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                (SingletonRemovalSemantics.targetContext source removed
                  (sourceOuter.extend region))).ids.Nodup := by
            rw [targetContextExact]
            exact targetExtendedNodup
          let rawFullTargetToSource :
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))).sigs =
                (sourceOuter.extend region).sigs :=
            (InsertionCompilation.NaturalityInternal.hostContext_sigs
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                (sourceOuter.extend region))).trans
              (SingletonRemovalSemantics.targetContext_sigs source removed
                (sourceOuter.extend region))
          have rawFullIdentity :
              (fun {sig} (value : Var (sourceOuter.extend region).sigs sig) =>
                rawFullTargetToSource ▸ rawFullRenaming value) =
                (fun {_}
                  (value : Var (sourceOuter.extend region).sigs _) => value) := by
            exact
              composeRenaming_reindexed_identity
                (SingletonRemovalSemantics.targetContext_sigs source removed
                  (sourceOuter.extend region))
                (InsertionCompilation.NaturalityInternal.hostContext_sigs
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region)))
                sourceToBaseExtended baseToRawExtended
                (SingletonRemovalSemantics.contextRenaming_reindex_identity
                  source removed (sourceOuter.extend region))
                (InsertionCompilation.NaturalityInternal.hostContextRenaming_reindex_identity
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))
                  rawTargetExtendedNodup)
          let sourceToBaseOuter :
              WireRenaming sourceOuter.sigs
                (SingletonRemovalSemantics.targetContext source removed
                  sourceOuter).sigs :=
            SingletonRemovalSemantics.contextRenaming source removed
              sourceOuter
          let baseToTargetOuter :
              WireRenaming
                (SingletonRemovalSemantics.targetContext source removed
                  sourceOuter).sigs
                (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).sigs :=
            InsertionCompilation.NaturalityInternal.hostContextRenaming
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)
          let outerRenaming :
              WireRenaming sourceOuter.sigs
                (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).sigs :=
            fun {_} value => baseToTargetOuter (sourceToBaseOuter value)
          let outerTargetToSource :
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)).sigs =
                sourceOuter.sigs :=
            (InsertionCompilation.NaturalityInternal.hostContext_sigs
              attachment
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)).trans
              (SingletonRemovalSemantics.targetContext_sigs source removed
                sourceOuter)
          have outerIdentity :
              (fun {sig} (value : Var sourceOuter.sigs sig) =>
                outerTargetToSource ▸ outerRenaming value) =
                (fun {_} (value : Var sourceOuter.sigs _) => value) := by
            exact
              composeRenaming_reindexed_identity
                (SingletonRemovalSemantics.targetContext_sigs source removed
                  sourceOuter)
                (InsertionCompilation.NaturalityInternal.hostContext_sigs
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                sourceToBaseOuter baseToTargetOuter
                (SingletonRemovalSemantics.contextRenaming_reindex_identity
                  source removed sourceOuter)
                (InsertionCompilation.NaturalityInternal.hostContextRenaming_reindex_identity
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter)
                  targetCurrentAbove.1)
          let rawTargetToCanonical :
              (InsertionCompilation.NaturalityInternal.hostContext attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    (sourceOuter.extend region))).sigs =
                bound ++
                  (InsertionCompilation.NaturalityInternal.hostContext attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).sigs :=
            targetOuterSigsExact.trans targetCanonicalSigsExact
          let canonicalFullRenaming :
              WireRenaming (bound ++ sourceOuter.sigs)
                (bound ++
                  (InsertionCompilation.NaturalityInternal.hostContext attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).sigs) :=
            transportRenaming sourceBinderSigsExact.symm
              rawTargetToCanonical.symm rawFullRenaming
          let canonicalTargetToSource :
              bound ++
                    (InsertionCompilation.NaturalityInternal.hostContext attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).sigs =
                bound ++ sourceOuter.sigs :=
            congrArg (List.append bound) outerTargetToSource
          have canonicalFullIdentity :
              (fun {sig} (value : Var (bound ++ sourceOuter.sigs) sig) =>
                canonicalTargetToSource ▸ canonicalFullRenaming value) =
                (fun {_}
                  (value : Var (bound ++ sourceOuter.sigs) _) => value) := by
            exact
              transportRenaming_reindexed_identity
                sourceBinderSigsExact.symm rawTargetToCanonical.symm
                rawFullTargetToSource canonicalTargetToSource rawFullRenaming
                rawFullIdentity
          have canonicalFullRenamingExact :
              (canonicalFullRenaming :
                WireRenaming (bound ++ sourceOuter.sigs)
                  (bound ++
                    (InsertionCompilation.NaturalityInternal.hostContext attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).sigs)) =
                (DiagramContext.ComposableSemanticZipper.liftMany
                  bound outerRenaming :
                    WireRenaming (bound ++ sourceOuter.sigs)
                      (bound ++
                        (InsertionCompilation.NaturalityInternal.hostContext attachment
                          (SingletonRemovalSemantics.targetContext source removed
                            sourceOuter)).sigs)) := by
            exact
              DiagramContext.ComposableSemanticZipper.eq_liftMany_of_reindexed_identity
                bound outerTargetToSource outerRenaming canonicalFullRenaming
                outerIdentity canonicalFullIdentity
          have canonicalComposableRaw :=
            (aroundReceipt.composable.rebaseSourceOuter
                sourceBinderSigsExact).rebaseTargetOuter
              rawTargetToCanonical
          have canonicalComposable :
              DiagramContext.ComposableSemanticZipper
                (sourceBinderSigsExact ▸ aroundReceipt.sourceAbove)
                (rawTargetToCanonical ▸ aroundReceipt.targetAbove)
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env canonicalFullRenaming)
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed aroundReceipt.sourceSiteOuter value))) := by
            rw [← envComp_transportRenaming sourceBinderSigsExact
              rawTargetToCanonical rawFullRenaming]
            exact canonicalComposableRaw
          have liftedComposable :
              DiagramContext.ComposableSemanticZipper
                (sourceBinderSigsExact ▸ aroundReceipt.sourceAbove)
                (rawTargetToCanonical ▸ aroundReceipt.targetAbove)
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (DiagramContext.ComposableSemanticZipper.liftMany
                      bound outerRenaming))
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed aroundReceipt.sourceSiteOuter value))) := by
            rw [← canonicalFullRenamingExact]
            exact canonicalComposable
          have boundComposable :=
            DiagramContext.ComposableSemanticZipper.bindMany
              bound outerRenaming liftedComposable
          have sourceAncestorExact :
              sourceAncestor =
                DiagramContext.bindMany bound
                  (sourceBinderSigsExact ▸ aroundReceipt.sourceAbove) := by
            unfold sourceAncestor
            rw [RelationJoinStep.bindContextFor_eq_bindMany]
            unfold bound
            have proofExact :
                (@List.map_append _ _
                    (fun wire => (source.val.wires wire).sig)
                    (source.val.wiresAt region) sourceOuter.ids) =
                  sourceBinderSigsExact :=
              Subsingleton.elim _ _
            rw [proofExact]
            rfl
          have targetAncestorExact :
              targetAncestor =
                DiagramContext.bindMany bound
                  (rawTargetToCanonical ▸ aroundReceipt.targetAbove) := by
            unfold targetAncestor
            rw [RelationJoinStep.bindContextFor_eq_bindMany]
            change
              DiagramContext.bindMany
                  ((attachment.diagram.wiresAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))).map
                        (fun wire => (attachment.diagram.wires wire).sig))
                  (targetMapAppendExact ▸
                    (targetBinderContextExact ▸
                      aroundReceipt.targetAbove)) =
                DiagramContext.bindMany bound
                  (rawTargetToCanonical ▸ aroundReceipt.targetAbove)
            rw [RelationJoinStep.cast_context_trans targetBinderContextExact
              targetMapAppendExact]
            rw [RelationJoinStep.bindMany_reindexBound
              targetLocalSigsExact]
            rw [RelationJoinStep.cast_context_trans]
          have ancestorComposable :
              DiagramContext.ComposableSemanticZipper
                sourceAncestor targetAncestor
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed sourceOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed sourceOuter value)))
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (fun {_} value =>
                      InsertionCompilation.NaturalityInternal.hostContextRenaming attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter)
                          (SingletonRemovalSemantics.contextRenaming source
                            removed aroundReceipt.sourceSiteOuter value))) := by
            rw [sourceAncestorExact, targetAncestorExact]
            simpa only [outerRenaming] using boundComposable
          let rebasedTarget :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              targetContextExact canonicalTargetAround
          let rawTargetContextExact :=
            InsertionCompilation.NaturalityInternal.hostContext_extend_offsite
              compiled
              (SingletonRemovalSemantics.targetContext source removed
                sourceOuter)
              (SingletonRemovalSemantics.targetRegion source removed region)
              baseNotSite
          let rawRebasedTarget :=
            InsertionCompilation.NaturalityInternal.rebaseRegionFrame
              rawTargetContextExact targetAround
          have rawRebasedTargetExact :
              rawRebasedTarget = rebasedTarget := by
            unfold rawRebasedTarget rebasedTarget canonicalTargetAround
            have proofExact :
                rawTargetContextExact =
                  nestedTargetContextExact.trans targetContextExact :=
              Subsingleton.elim _ _
            rw [proofExact]
            exact
              RelationJoinStep.rebaseGeneratedFrame_trans
                nestedTargetContextExact targetContextExact targetAround
          refine
            ⟨{
              sourceSiteOuter := aroundReceipt.sourceSiteOuter
              sourceAbove := sourceAncestor
              targetAbove := targetAncestor
              sourceBody := aroundReceipt.sourceBody
              targetBody := aroundReceipt.targetBody
              sourceStopped := sourceStoppedAncestor
              targetStopped := targetStoppedAncestor
              sourceStoppedVisible :=
                aroundReceipt.sourceStoppedVisible
              targetStoppedVisible :=
                aroundReceipt.targetStoppedVisible
              sourceDecomposition :=
                DiagramContext.StopsAboveBindMany.bindContextFor_cast
                  ((congrArg ConcreteElaboration.WireContext.sigs
                      aroundReceipt.sourceStoppedVisible).trans
                    (ConcreteElaboration.WireContext.sigs_extend
                      aroundReceipt.sourceSiteOuter scope))
                  source.val sourceOuter.ids (source.val.wiresAt region)
                  aroundReceipt.sourceStopped.context
                  aroundReceipt.sourceAbove
                  aroundReceipt.sourceDecomposition
              targetDecomposition :=
                by
                  let holeExact :=
                    (congrArg ConcreteElaboration.WireContext.sigs
                        aroundReceipt.targetStoppedVisible).trans
                      (ConcreteElaboration.WireContext.sigs_extend
                        (InsertionCompilation.NaturalityInternal.hostContext
                          attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter))
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source
                            removed scope)))
                  have rebased :=
                    DiagramContext.StopsAboveBindMany.rebaseOuter_cast
                      holeExact targetBinderContextExact
                      aroundReceipt.targetAbove
                      aroundReceipt.targetStopped.context
                      aroundReceipt.targetDecomposition
                  have bound :=
                    DiagramContext.StopsAboveBindMany.bindContextFor_cast
                      holeExact attachment.diagram
                      (InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          sourceOuter)).ids
                      (attachment.diagram.wiresAt
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source removed
                            region)))
                      (targetBinderContextExact ▸
                        aroundReceipt.targetStopped.context)
                      (targetBinderContextExact ▸
                        aroundReceipt.targetAbove)
                      rebased
                  simpa only [targetAncestor, targetStoppedAncestor] using bound
              sourceStoppedBody := aroundReceipt.sourceStoppedBody
              targetStoppedBody := aroundReceipt.targetStoppedBody
              sourceFill := ?_
              targetFill := ?_
              composable := ancestorComposable
            }, ?_, ?_⟩
          · change
              (bindContextFor source.val sourceOuter.ids
                  (source.val.wiresAt region)
                  sourceAround.context).fill sourceAround.siteBody =
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
              (bindContextFor attachment.diagram
                  (InsertionCompilation.NaturalityInternal.hostContext
                    attachment
                    (SingletonRemovalSemantics.targetContext source removed
                      sourceOuter)).ids
                  (attachment.diagram.wiresAt
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)))
                  rawRebasedTarget.context).fill rawRebasedTarget.siteBody =
                targetAncestor.fill
                  (ConcreteElaboration.finishRegion attachment.diagram
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        aroundReceipt.sourceSiteOuter))
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        scope))
                    aroundReceipt.targetBody)
            rw [rawRebasedTargetExact]
            unfold targetAncestor
            rw [bindContextFor_fill, finishBodyFor_eq_finishRegion,
              bindContextFor_fill, finishBodyFor_eq_finishRegion]
            apply congrArg
              (ConcreteElaboration.finishRegion attachment.diagram
                (InsertionCompilation.NaturalityInternal.hostContext
                  attachment
                  (SingletonRemovalSemantics.targetContext source removed
                    sourceOuter))
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    region)))
            calc
              (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
                    targetContextExact canonicalTargetAround).context.fill
                  (InsertionCompilation.NaturalityInternal.rebaseRegionFrame
                    targetContextExact canonicalTargetAround).siteBody =
                  targetOuterSigsExact ▸
                    canonicalTargetAround.context.fill
                      canonicalTargetAround.siteBody :=
                (InsertionCompilation.NaturalityInternal.rebaseRegionFrame_fill
                  targetContextExact canonicalTargetAround).symm
              _ =
                  targetOuterSigsExact ▸
                    aroundReceipt.targetAbove.fill
                      (ConcreteElaboration.finishRegion attachment.diagram
                        (InsertionCompilation.NaturalityInternal.hostContext
                          attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed aroundReceipt.sourceSiteOuter))
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source removed
                            scope))
                        aroundReceipt.targetBody) :=
                congrArg (fun body => targetOuterSigsExact ▸ body)
                  aroundReceipt.targetFill
              _ =
                  (targetOuterSigsExact ▸ aroundReceipt.targetAbove).fill
                    (ConcreteElaboration.finishRegion attachment.diagram
                      (InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          aroundReceipt.sourceSiteOuter))
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          scope))
                      aroundReceipt.targetBody) := by
                simpa only using
                  (DiagramContext.fill_rebaseOuter
                    (definitions := definitions) targetOuterSigsExact
                    aroundReceipt.targetAbove
                    (ConcreteElaboration.finishRegion attachment.diagram
                      (InsertionCompilation.NaturalityInternal.hostContext
                        attachment
                        (SingletonRemovalSemantics.targetContext source removed
                          aroundReceipt.sourceSiteOuter))
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          scope))
                      aroundReceipt.targetBody))
            all_goals try rfl
          · have sourceNotAtScope : region ≠ scope := currentScope
            have sourceFuelShape :
                childFuel + 1 = childFuel + 1 := rfl
            rw [sourceFuelShape]
            simp only [compileRegionFrame?]
            split
            · rename_i same
              exact (sourceNotAtScope same).elim
            · rw [sourceNodesCompiled, scopeSelectedFound]
              simp [nestedSourceStoppedCompiled,
                sourceAroundStoppedCompiled, sourceStoppedAncestor]
          · have targetNotAtScope :
                attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region) ≠
                  attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        scope) := by
              intro same
              exact
                currentScope
                  (SingletonRemovalSemantics.targetRegion_injective source
                    removed
                    (InsertionCompilation.NaturalityInternal.hostRegion_injective
                      attachment same))
            have baseScopeSelectedFound :
                (((singletonErasureBase source removed
                  candidateWellFormed).val.childrenOf
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)).find?
                    (fun candidate =>
                      decide
                        ((singletonErasureBase source removed
                          candidateWellFormed).val.Encloses candidate
                          (SingletonRemovalSemantics.targetRegion source
                            removed scope)))) =
                  some
                    (SingletonRemovalSemantics.targetRegion source removed
                      selected) := by
              have found :=
                SingletonRemovalSemantics.target_find_enclosing source
                  removed scope (source.val.childrenOf region)
              rw [scopeSelectedFound] at found
              simpa only [singletonErasureBase,
                SingletonRemovalSemantics.target_childrenOf] using found
            have hostScopeSelectedFound :
                (attachment.diagram.childrenOf
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        region))).find?
                    (fun candidate =>
                      decide
                        (attachment.diagram.Encloses candidate
                          (attachment.hostRegion
                            (SingletonRemovalSemantics.targetRegion source
                              removed scope)))) =
                  some
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        selected)) := by
              rw [
                InsertionCompilation.NaturalityInternal.hostChildren_offsite
                  compiled
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)
                    baseNotSite]
              have hostFindExact :
                  (((singletonErasureBase source removed
                    candidateWellFormed).val.childrenOf
                      (SingletonRemovalSemantics.targetRegion source removed
                        region)).map attachment.hostRegion).find?
                      (fun candidate =>
                        decide
                          (attachment.diagram.Encloses candidate
                            (attachment.hostRegion
                              (SingletonRemovalSemantics.targetRegion source
                                removed scope)))) =
                    (((singletonErasureBase source removed
                      candidateWellFormed).val.childrenOf
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)).find?
                        (fun candidate =>
                          decide
                            ((singletonErasureBase source removed
                              candidateWellFormed).val.Encloses candidate
                              (SingletonRemovalSemantics.targetRegion source
                                removed scope)))).map attachment.hostRegion := by
                apply RelationJoinStep.find?_map_exact
                intro child
                by_cases childScope :
                    (singletonErasureBase source removed
                      candidateWellFormed).val.Encloses child
                        (SingletonRemovalSemantics.targetRegion source removed
                          scope)
                · exact
                    (decide_eq_true
                      ((RelationJoinStep.hostEncloses_iff_exact compiled child
                        (SingletonRemovalSemantics.targetRegion source removed
                          scope)).2 childScope)).trans
                      (decide_eq_true childScope).symm
                · exact
                    (decide_eq_false
                      (fun hostChildScope =>
                        childScope
                          ((RelationJoinStep.hostEncloses_iff_exact compiled
                            child
                            (SingletonRemovalSemantics.targetRegion source
                              removed scope)).1 hostChildScope))).trans
                      (decide_eq_false childScope).symm
              rw [hostFindExact, baseScopeSelectedFound]
              rfl
            have canonicalStoppedNodesCompiled :
                ConcreteElaboration.compileNodes? definitions
                    attachment.diagram
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        (sourceOuter.extend region)))
                    (attachment.diagram.nodesAt
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))) =
                  some canonicalTargetNodes := by
              rw [
                InsertionCompilation.NaturalityInternal.hostNodes_offsite
                  compiled
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)
                    baseNotSite]
              exact canonicalTargetNodesCompiled
            have canonicalAroundStoppedCompiled :
                compileSiblingFrame? definitions attachment.diagram
                    (childFuel + fragment.val.diagram.regionCount)
                    (InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        (sourceOuter.extend region)))
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        selected))
                    nestedReceipt.targetStopped canonicalTargetNodes
                    (attachment.diagram.childrenOf
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region))) =
                  some aroundReceipt.targetStopped := by
              rw [
                InsertionCompilation.NaturalityInternal.hostChildren_offsite
                  compiled
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)
                    baseNotSite]
              simp only [singletonErasureBase]
              rw [SingletonRemovalSemantics.target_childrenOf,
                RelationJoinStep.map_map_exact]
              exact targetAroundStoppedCompiled
            obtain ⟨rawStoppedNodes, rawStoppedNested, rawStoppedAround,
                rawStoppedNodesCompiled, rawStoppedNestedCompiled,
                rawStoppedAroundCompiled, _rawStoppedVisible,
                rawStoppedNodesExact, rawStoppedNestedExact,
                rawStoppedAroundExact⟩ :=
              InsertionCompilation.NaturalityInternal.compileFrameBranch_cast_context
                attachment.diagram targetContextExact
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    scope))
                (childFuel + fragment.val.diagram.regionCount)
                (attachment.hostRegion
                  (SingletonRemovalSemantics.targetRegion source removed
                    selected))
                (attachment.diagram.nodesAt
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)))
                (attachment.diagram.childrenOf
                  (attachment.hostRegion
                    (SingletonRemovalSemantics.targetRegion source removed
                      region)))
                (leading := canonicalTargetNodes)
                (nested := nestedReceipt.targetStopped)
                (frame := aroundReceipt.targetStopped)
                canonicalStoppedNodesCompiled
                nestedTargetStoppedCompiled
                canonicalAroundStoppedCompiled
            subst rawStoppedNodes
            subst rawStoppedNested
            subst rawStoppedAround
            have targetFuelShape :
                childFuel + 1 + fragment.val.diagram.regionCount =
                  childFuel + fragment.val.diagram.regionCount + 1 := by
              omega
            rw [targetFuelShape]
            simp only [compileRegionFrame?]
            split
            · rename_i same
              exact (targetNotAtScope same).elim
            · simp only [rawStoppedNodesCompiled, hostScopeSelectedFound,
                Option.bind_some]
              change
                (compileRegionFrame? definitions attachment.diagram
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        scope))
                    (childFuel + fragment.val.diagram.regionCount)
                    (attachment.hostRegion
                      (SingletonRemovalSemantics.targetRegion source removed
                        selected))
                    ((InsertionCompilation.NaturalityInternal.hostContext
                      attachment
                      (SingletonRemovalSemantics.targetContext source removed
                        sourceOuter)).extend
                      (attachment.hostRegion
                        (SingletonRemovalSemantics.targetRegion source removed
                          region)))).bind
                    (fun nested =>
                      (compileSiblingFrame? definitions attachment.diagram
                        (childFuel + fragment.val.diagram.regionCount)
                        ((InsertionCompilation.NaturalityInternal.hostContext
                          attachment
                          (SingletonRemovalSemantics.targetContext source
                            removed sourceOuter)).extend
                          (attachment.hostRegion
                            (SingletonRemovalSemantics.targetRegion source
                              removed region)))
                        (attachment.hostRegion
                          (SingletonRemovalSemantics.targetRegion source
                            removed selected))
                        nested
                        (InsertionCompilation.NaturalityInternal.rebaseItemSeq
                          targetContextExact canonicalTargetNodes)
                        (attachment.diagram.childrenOf
                          (attachment.hostRegion
                            (SingletonRemovalSemantics.targetRegion source
                              removed region)))).bind
                        (fun around =>
                          some
                            { visible := around.visible
                              siteBody := around.siteBody
                              context :=
                                bindContextFor attachment.diagram
                                  (InsertionCompilation.NaturalityInternal.hostContext
                                    attachment
                                      (SingletonRemovalSemantics.targetContext
                                        source removed sourceOuter)).ids
                                  (attachment.diagram.wiresAt
                                    (attachment.hostRegion
                                      (SingletonRemovalSemantics.targetRegion
                                        source removed region)))
                                  around.context })) =
                  some targetStoppedAncestor
              rw [rawStoppedNestedCompiled]
              dsimp only [Option.bind]
              rw [rawStoppedAroundCompiled]
              dsimp only [Option.bind]
              rw [RelationJoinStep.rebaseGeneratedFrame_exact
                targetContextExact aroundReceipt.targetStopped]
              unfold targetStoppedAncestor targetBinderContextExact
                targetOuterSigsExact
              rfl

theorem Internal.RelationJoinStep.aboveDyingScopeReceiptOfExplicitBase
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        step.prior step.priorApplication).WellFormed definitions)
    (base : CheckedDiagram definitions)
    (baseExact :
      base =
        singletonErasureBase step.prior step.priorApplication
          candidateWellFormed)
    (site : base.val.RegionId)
    (siteExact :
      site =
        baseExact.symm ▸
          SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.prior.val.nodes step.priorApplication).region)
    (attachment : ConcreteSpliceAttachment base site content)
    (compiled : InsertionCompilation contentCompiled attachment)
    (checkedExact :
      (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
          CheckedDiagram definitions) =
        step.checked)
    (checkedSiteExact :
      checkedExact ▸
          attachment.hostRegion
            (baseExact.symm ▸
              SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage
                  (source.val.wires dying).scope)) =
        step.checkedRegionImage (source.val.wires dying).scope)
    (priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope))
    (checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)) :
    Nonempty
      (RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) := by
  cases baseExact
  cases siteExact
  have removedRegionExact :
      (step.prior.val.nodes step.priorApplication).region =
        step.priorRegionImage step.sourceRegion := by
    rw [step.priorNodeExact]
    rfl
  have priorRootAbove :
      ConcreteElaboration.ContextAbove step.prior.val
        (ConcreteElaboration.WireContext.empty step.prior.val)
        step.prior.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty],
      by
        intro wire member
        simp [ConcreteElaboration.WireContext.empty] at member⟩
  obtain ⟨baseRootFrame, _priorRootAbove, _priorRootGenerated,
      erasureRoot⟩ :=
    SingletonRemovalSemantics.RelationJoinStep.pairedGeneratedFrame step
      (step.prior.val.nodes step.priorApplication).region step.prior.val.root
      (step.prior.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty step.prior.val)
      step.priorSite.frame priorRootAbove (by
        simpa only [removedRegionExact] using
          step.priorSite.frame_generated)
  obtain ⟨baseSiteOuter, _baseSiteFuel, _baseSiteNodes,
      _baseSiteChildren, baseSiteVisible, _baseSiteNodesCompiled,
      _baseSiteChildrenCompiled, _baseSiteBody⟩ :=
    compiled.site.site_origin
  have baseRootAbove :
      ConcreteElaboration.ContextAbove
        (singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val
        (ConcreteElaboration.WireContext.empty
          (singletonErasureBase step.prior step.priorApplication
            candidateWellFormed).val)
        (singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty],
      by
        intro wire member
        simp [ConcreteElaboration.WireContext.empty] at member⟩
  have baseRootFrameExact : baseRootFrame = compiled.site.frame := by
    apply Option.some.inj
    exact erasureRoot.targetGenerated.symm.trans (by
      simpa [singletonErasureBase,
        ConcreteElaboration.WireContext.empty] using
          compiled.site.frame_generated)
  subst baseRootFrame
  obtain ⟨generatedRootFrame, insertionRoot⟩ :=
    InsertionCompilation.pairedGeneratedFrame compiled
      (singletonErasureBase step.prior step.priorApplication
        candidateWellFormed).val.root
      ((singletonErasureBase step.prior step.priorApplication
        candidateWellFormed).val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty
        (singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val)
      baseSiteOuter
      compiled.site.frame baseRootAbove baseSiteVisible baseSiteVisible
      compiled.site.frame_generated
  obtain ⟨reflected, sourceStoppedGenerated, targetStoppedGenerated⟩ :=
    RelationJoinStep.pairedFrameAboveScope.{u} step.prior
      step.priorApplication candidateWellFormed compiled erasureRoot
      insertionRoot.provenance rfl
      (step.priorRegionImage (source.val.wires dying).scope)
      (by
        exact
          of_decide_eq_true
            ((List.all_eq_true.mp
              step.prior.property.all_regions_reach_root)
              (step.priorRegionImage (source.val.wires dying).scope)
              (Data.Finite.mem_allFin _)))
      (by
        simpa only [removedRegionExact] using
          step.prior_dying_scope_encloses_site)
  let reflectedPriorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope) :=
    SiteCompilation.ofFrame reflected.sourceStopped sourceStoppedGenerated
  have reflectedPriorScopeExact :
      reflectedPriorScope = priorScope :=
    SiteCompilation.unique reflectedPriorScope priorScope
  let generatedChecked : CheckedDiagram definitions :=
    ⟨attachment.diagram, compiled.generated_wellFormed⟩
  let rawTargetScope :=
    attachment.hostRegion
      (SingletonRemovalSemantics.targetRegion step.prior
        step.priorApplication
        (step.priorRegionImage (source.val.wires dying).scope))
  have checkedSiteBack :
      (show
        (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
          CheckedDiagram definitions).val.RegionId
        from
          checkedExact.symm ▸
            step.checkedRegionImage (source.val.wires dying).scope) =
        rawTargetScope := by
    apply Fin.ext
    exact
      (transport_checked_region_val checkedExact.symm
        (step.checkedRegionImage
          (source.val.wires dying).scope)).trans
        ((congrArg Fin.val checkedSiteExact).symm.trans
          (transport_checked_region_val checkedExact
            (attachment.hostRegion
              (SingletonRemovalSemantics.targetRegion step.prior
                step.priorApplication
                (step.priorRegionImage
                  (source.val.wires dying).scope)))))
  let rawCheckedScope :
      SiteCompilation generatedChecked rawTargetScope :=
    checkedSiteBack ▸ transportSiteCompilation checkedExact.symm checkedScope
  have fragmentRegionCountLe :
      attachment.fragmentRegions.length ≤
        content.val.diagram.regionCount := by
    unfold ConcreteSpliceAttachment.fragmentRegions
    simpa [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange] using
        List.length_filter_le
          (fun region : content.val.diagram.RegionId =>
            decide (region ≠ content.val.diagram.root))
          (Data.Finite.allFin content.val.diagram.regionCount)
  have targetFuelLe :
      attachment.diagram.regionCount + 1 ≤
        step.prior.val.regionCount + 1 +
          content.val.diagram.regionCount := by
    change
      step.prior.val.regionCount +
            attachment.fragmentRegions.length + 1 ≤
        step.prior.val.regionCount + 1 +
          content.val.diagram.regionCount
    omega
  have rawCheckedAtGeneratedFuel :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions attachment.diagram rawTargetScope
      (attachment.diagram.regionCount + 1)
      (step.prior.val.regionCount + 1 +
        content.val.diagram.regionCount)
      targetFuelLe attachment.diagram.root
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      rawCheckedScope.frame_generated
  have targetStoppedAtGeneratedFuel :
      compileRegionFrame? definitions attachment.diagram rawTargetScope
          (step.prior.val.regionCount + 1 +
            content.val.diagram.regionCount)
          attachment.diagram.root
          (ConcreteElaboration.WireContext.empty attachment.diagram) =
        some reflected.targetStopped := by
    simpa [rawTargetScope, singletonErasureBase,
      ConcreteElaboration.WireContext.empty,
      ConcreteSpliceAttachment.diagram] using targetStoppedGenerated
  have targetStoppedExact :
      reflected.targetStopped = rawCheckedScope.frame :=
    Option.some.inj
      (targetStoppedAtGeneratedFuel.symm.trans rawCheckedAtGeneratedFuel)
  have targetStoppedGeneratedAtRoot :
      compileRegionFrame? definitions attachment.diagram rawTargetScope
          (attachment.diagram.regionCount + 1) attachment.diagram.root
          (ConcreteElaboration.WireContext.empty attachment.diagram) =
        some reflected.targetStopped := by
    rw [targetStoppedExact]
    exact rawCheckedScope.frame_generated
  let reflectedRawCheckedScope :
      SiteCompilation generatedChecked rawTargetScope :=
    SiteCompilation.ofFrame reflected.targetStopped
      targetStoppedGeneratedAtRoot
  have reflectedRawCheckedScopeExact :
      reflectedRawCheckedScope = rawCheckedScope :=
    SiteCompilation.unique reflectedRawCheckedScope rawCheckedScope
  let reflectedCheckedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope) :=
    checkedSiteExact ▸
      transportSiteCompilation checkedExact reflectedRawCheckedScope
  have reflectedCheckedScopeExact :
      reflectedCheckedScope = checkedScope :=
    SiteCompilation.unique reflectedCheckedScope checkedScope
  subst priorScope
  subst checkedScope
  let rawCheckedSiteOuter :=
    InsertionCompilation.NaturalityInternal.hostContext attachment
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication reflected.sourceSiteOuter)
  let checkedSiteOuter :
      ConcreteElaboration.WireContext step.checked.val :=
    transportCheckedContext checkedExact rawCheckedSiteOuter
  have checkedSiteOuterSigs :
      checkedSiteOuter.sigs = rawCheckedSiteOuter.sigs := by
    exact
      transport_checked_context_sigs checkedExact
        rawCheckedSiteOuter
  let checkedAbove :
      DiagramContext definitions checkedSiteOuter.sigs [] :=
    checkedSiteOuterSigs.symm ▸ reflected.targetAbove
  have checkedSiteTransport :
      transportCheckedRegion checkedExact rawTargetScope =
        step.checkedRegionImage (source.val.wires dying).scope := by
    apply Fin.ext
    rw [transportCheckedRegion_val checkedExact
      rawTargetScope]
    have same := congrArg Fin.val checkedSiteExact
    rw [transport_checked_region_val checkedExact] at same
    simpa only [rawTargetScope] using same
  have checkedExtendedSigs :
      (checkedSiteOuter.extend
          (step.checkedRegionImage
            (source.val.wires dying).scope)).sigs =
        (rawCheckedSiteOuter.extend rawTargetScope).sigs := by
    rw [← checkedSiteTransport]
    calc
      _ =
          (transportCheckedContext checkedExact
            (rawCheckedSiteOuter.extend rawTargetScope)).sigs :=
        congrArg ConcreteElaboration.WireContext.sigs
          (transport_checked_extended_context checkedExact
            rawCheckedSiteOuter rawTargetScope)
      _ = _ :=
        transport_checked_context_sigs checkedExact
          (rawCheckedSiteOuter.extend rawTargetScope)
  let checkedBody :
      Region definitions
        (checkedSiteOuter.extend
          (step.checkedRegionImage
            (source.val.wires dying).scope)).sigs :=
    checkedExtendedSigs.symm ▸ reflected.targetBody
  have priorVisibleExact :
      reflectedPriorScope.frame.visible =
        reflected.sourceSiteOuter.extend
          (step.priorRegionImage (source.val.wires dying).scope) := by
    exact reflected.sourceStoppedVisible
  have priorBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs priorVisibleExact ▸
          reflectedPriorScope.frame.siteBody =
        reflected.sourceBody := by
    exact reflected.sourceStoppedBody
  have checkedVisibleExact :
      reflectedCheckedScope.frame.visible =
        checkedSiteOuter.extend
          (step.checkedRegionImage
            (source.val.wires dying).scope) := by
    calc
      _ =
          (transportSiteCompilation checkedExact
            reflectedRawCheckedScope).frame.visible :=
        castSiteCompilation_visible checkedSiteExact
          (transportSiteCompilation checkedExact reflectedRawCheckedScope)
      _ =
          transportCheckedContext checkedExact
            reflectedRawCheckedScope.frame.visible :=
        transportSiteCompilation_visible_checked checkedExact
          reflectedRawCheckedScope
      _ =
          transportCheckedContext checkedExact
            reflected.targetStopped.visible := rfl
      _ =
          transportCheckedContext checkedExact
            (rawCheckedSiteOuter.extend rawTargetScope) :=
        transport_checked_context_eq checkedExact
          reflected.targetStoppedVisible
      _ =
          (transportCheckedContext checkedExact rawCheckedSiteOuter).extend
            (transportCheckedRegion checkedExact rawTargetScope) :=
        (transport_checked_extended_context checkedExact
          rawCheckedSiteOuter rawTargetScope).symm
      _ = _ := congrArg
        (ConcreteElaboration.WireContext.extend
          (transportCheckedContext checkedExact rawCheckedSiteOuter))
        checkedSiteTransport
  have checkedBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs checkedVisibleExact ▸
          reflectedCheckedScope.frame.siteBody =
        checkedBody := by
    have scopeBody :
        HEq reflectedCheckedScope.frame.siteBody
          reflected.targetStopped.siteBody := by
      obtain ⟨bodySigs, bodyTransport⟩ :=
        transportedSiteCompilation_body checkedExact
          reflectedRawCheckedScope checkedSiteExact
      have transported :
          HEq reflectedCheckedScope.frame.siteBody
            (bodySigs ▸
              reflectedRawCheckedScope.frame.siteBody) :=
        heq_of_eq bodyTransport.symm
      have uncast :
          HEq
            (bodySigs ▸
              reflectedRawCheckedScope.frame.siteBody)
            reflectedRawCheckedScope.frame.siteBody :=
        eqRec_heq bodySigs
          reflectedRawCheckedScope.frame.siteBody
      exact transported.trans (uncast.trans (by rfl))
    have rawBody :
        HEq reflected.targetStopped.siteBody reflected.targetBody := by
      let visibleSigs :=
        congrArg ConcreteElaboration.WireContext.sigs
          reflected.targetStoppedVisible
      exact
        (eqRec_heq visibleSigs
          reflected.targetStopped.siteBody).symm.trans
            (heq_of_eq reflected.targetStoppedBody)
    have transportedBody : HEq reflected.targetBody checkedBody := by
      unfold checkedBody
      exact (eqRec_heq _ _).symm
    apply eq_of_heq
    exact
      (eqRec_heq _ _).trans
        (scopeBody.trans (rawBody.trans transportedBody))
  have priorRootFill :
      reflectedPriorScope.checked =
        reflected.sourceAbove.fill
          (ConcreteElaboration.finishRegion step.prior.val
            reflected.sourceSiteOuter
            (step.priorRegionImage (source.val.wires dying).scope)
            reflected.sourceBody) :=
    step.priorSite.frame_fills_checked.symm.trans reflected.sourceFill
  have targetCompiled :
      ConcreteElaboration.compileRegion? definitions attachment.diagram
          (attachment.diagram.regionCount + 1)
          (attachment.hostRegion
            (singletonErasureBase step.prior step.priorApplication
              candidateWellFormed).val.root)
          (ConcreteElaboration.WireContext.empty attachment.diagram) =
        some (elaborate generatedChecked) := by
    have rooted :=
      elaborateWith_compiles definitions attachment.diagram
        compiled.generated_wellFormed
    unfold ConcreteElaboration.compileRoot? at rooted
    simpa [ConcreteSpliceAttachment.diagram] using rooted
  have targetCompiledAtGeneratedFuel :=
    InsertionCompilation.NaturalityInternal.compileRegion_fuel_mono
      definitions attachment.diagram
      (attachment.diagram.regionCount + 1)
      ((singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val.regionCount + 1 +
        content.val.diagram.regionCount)
      (by
        simpa [singletonErasureBase] using targetFuelLe)
      (attachment.hostRegion
        (singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val.root)
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      targetCompiled
  have targetFrameSound :=
    compileRegionFrame?_sound definitions attachment.diagram
      _
      ((singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val.regionCount + 1 +
        content.val.diagram.regionCount)
      (attachment.hostRegion
        (singletonErasureBase step.prior step.priorApplication
          candidateWellFormed).val.root)
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      generatedRootFrame insertionRoot.provenance.targetGenerated
  have targetRootFrameExact :
      generatedRootFrame.context.fill generatedRootFrame.siteBody =
        elaborate generatedChecked :=
    Option.some.inj
      (targetFrameSound.symm.trans targetCompiledAtGeneratedFuel)
  have rawCheckedRoot :
      elaborate generatedChecked =
        reflected.targetAbove.fill
          (ConcreteElaboration.finishRegion attachment.diagram
            rawCheckedSiteOuter rawTargetScope reflected.targetBody) :=
    targetRootFrameExact.symm.trans reflected.targetFill
  have checkedRootFill :
      reflectedCheckedScope.checked =
        checkedAbove.fill
          (ConcreteElaboration.finishRegion step.checked.val
            checkedSiteOuter
            (step.checkedRegionImage
              (source.val.wires dying).scope)
            checkedBody) := by
    change elaborate step.checked = _
    calc
      _ = elaborate generatedChecked :=
        (congrArg elaborate checkedExact).symm
      _ =
          reflected.targetAbove.fill
            (ConcreteElaboration.finishRegion attachment.diagram
              rawCheckedSiteOuter rawTargetScope
              reflected.targetBody) :=
        rawCheckedRoot
      _ = _ := by
        exact
          (transport_checked_root_fill checkedExact rawCheckedSiteOuter
            rawTargetScope
            (step.checkedRegionImage
              (source.val.wires dying).scope)
            checkedSiteTransport checkedSiteOuterSigs checkedExtendedSigs
            reflected.targetAbove reflected.targetBody).symm
  let rawSiteProjection :
      WireRenaming reflected.sourceSiteOuter.sigs
        rawCheckedSiteOuter.sigs :=
    fun {_} value =>
      InsertionCompilation.NaturalityInternal.hostContextRenaming
        attachment
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication reflected.sourceSiteOuter)
        (SingletonRemovalSemantics.contextRenaming step.prior
          step.priorApplication reflected.sourceSiteOuter value)
  let siteProjection :
      WireRenaming reflected.sourceSiteOuter.sigs
        checkedSiteOuter.sigs :=
    transportRenaming rfl checkedSiteOuterSigs rawSiteProjection
  have siteProjectionOrigin :
      ∀ {sig : Sig}
        (value : Var reflected.sourceSiteOuter.sigs sig),
        ConcreteElaboration.WireContext.origin step.checked.val
            checkedSiteOuter.ids (siteProjection value) =
          relationJoinPriorToCheckedWire step
            (ConcreteElaboration.WireContext.origin step.prior.val
              reflected.sourceSiteOuter.ids value) := by
    intro sig value
    unfold siteProjection
    rw [transportRenaming_transportCheckedVariable checkedExact
      rawCheckedSiteOuter reflected.sourceSiteOuter.sigs
      rawSiteProjection value]
    unfold rawSiteProjection
    rw [transportCheckedVariable_origin,
      InsertionCompilation.NaturalityInternal.hostContextRenaming_origin]
    dsimp [singletonErasureBase]
    rw [SingletonRemovalSemantics.contextRenaming_action]
    unfold relationJoinPriorToCheckedWire transportWire
    apply Fin.ext
    rfl
  have outerMapExact :
      (fun (pre : PreModel.{u}) (env : Env pre []) => env) =
        (fun (pre : PreModel.{u}) (env : Env pre []) =>
          Env.comp env
            (fun {_} value =>
              InsertionCompilation.NaturalityInternal.hostContextRenaming
                attachment
                (SingletonRemovalSemantics.targetContext step.prior
                  step.priorApplication
                  (ConcreteElaboration.WireContext.empty step.prior.val))
                (SingletonRemovalSemantics.contextRenaming step.prior
                  step.priorApplication
                  (ConcreteElaboration.WireContext.empty step.prior.val)
                  value))) := by
    funext pre env sig value
    nomatch value
  have composable :
      DiagramContext.ComposableSemanticZipper.{u}
        reflected.sourceAbove checkedAbove
        (fun (_pre : PreModel.{u}) env => env)
        (fun (_pre : PreModel.{u}) env =>
          Env.comp env siteProjection) := by
    rw [outerMapExact]
    unfold checkedAbove siteProjection rawSiteProjection
    exact
      transportComposableSemanticZipperTargetHole checkedSiteOuterSigs
        reflected.sourceAbove reflected.targetAbove
        (fun {_} value =>
          InsertionCompilation.NaturalityInternal.hostContextRenaming
            attachment
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication reflected.sourceSiteOuter)
            (SingletonRemovalSemantics.contextRenaming step.prior
              step.priorApplication reflected.sourceSiteOuter value))
        _ reflected.composable
  exact
    RelationJoinStep.AboveDyingScopeReceipt.ofNormalized
      reflected.sourceSiteOuter checkedSiteOuter reflected.sourceAbove
      checkedAbove reflected.sourceBody checkedBody priorVisibleExact
      checkedVisibleExact reflected.sourceDecomposition
      (by
        exact
          transportCheckedAboveDecomposition checkedExact rawTargetScope
            (step.checkedRegionImage
              (source.val.wires dying).scope)
            checkedSiteExact rawCheckedSiteOuter reflectedRawCheckedScope
            reflected.targetAbove reflected.targetStoppedVisible
            reflected.targetDecomposition checkedVisibleExact)
      priorBodyExact checkedBodyExact
      siteProjection siteProjectionOrigin priorRootFill checkedRootFill
      composable


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
