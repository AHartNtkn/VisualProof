import VisualProof.Diagram.Concrete.WireQuantifierSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoin
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemoval
import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalZipper
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityZipper

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

namespace Internal

structure GeneratedFrameReceipt
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat) where
  site : diagram.RegionId
  region : diagram.RegionId
  outer : ConcreteElaboration.WireContext diagram
  frame : RegionFrame definitions diagram outer
  generated :
    compileRegionFrame? definitions diagram site fuel region outer =
      some frame

private theorem GeneratedFrameReceipt.transport_site_val
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    ((same ▸ receipt).site).val = receipt.site.val := by
  cases same
  rfl

theorem GeneratedFrameReceipt.transport_region_val
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    ((same ▸ receipt).region).val = receipt.region.val := by
  cases same
  rfl

theorem GeneratedFrameReceipt.transport_outer
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    (same ▸ receipt).outer = same ▸ receipt.outer := by
  cases same
  rfl

theorem GeneratedFrameReceipt.transport_frame_visible
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    (same ▸ receipt).frame.visible = same ▸ receipt.frame.visible := by
  cases same
  rfl

private theorem GeneratedFrameReceipt.transport_above
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel)
    (above :
      ConcreteElaboration.ContextAbove left receipt.outer
        receipt.region) :
    ConcreteElaboration.ContextAbove right (same ▸ receipt).outer
      (same ▸ receipt).region := by
  cases same
  exact above

private theorem transport_empty_context
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right) :
    same ▸ ConcreteElaboration.WireContext.empty left =
      ConcreteElaboration.WireContext.empty right := by
  cases same
  rfl

private theorem transport_root
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right) :
    same ▸ left.root = right.root := by
  cases same
  rfl

private theorem transport_root_val
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right) :
    left.root.val = right.root.val := by
  cases same
  rfl

theorem transport_checked_region_val
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    ((same ▸ region : right.val.RegionId)).val = region.val := by
  cases same
  rfl

def transportCheckedContext
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    ConcreteElaboration.WireContext right.val := by
  cases same
  exact context

theorem transport_checked_context_cast_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    same ▸ context = transportCheckedContext same context := by
  cases same
  rfl

def transportCheckedRegion
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    right.val.RegionId := by
  cases same
  exact region

theorem transportCheckedRegion_val
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    (transportCheckedRegion same region).val = region.val := by
  cases same
  rfl

theorem transport_checked_context_sigs
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    (transportCheckedContext same context).sigs = context.sigs := by
  cases same
  rfl

theorem transport_checked_extended_context
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (region : left.val.RegionId) :
    (transportCheckedContext same context).extend
        (transportCheckedRegion same region) =
      transportCheckedContext same (context.extend region) := by
  cases same
  rfl

theorem transport_checked_context_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {first second : ConcreteElaboration.WireContext left.val}
    (exact : first = second) :
    transportCheckedContext same first =
      transportCheckedContext same second := by
  cases same
  exact exact

theorem transport_checked_root_fill
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (outer : ConcreteElaboration.WireContext left.val)
    (site : left.val.RegionId)
    (rightSite : right.val.RegionId)
    (siteExact : transportCheckedRegion same site = rightSite)
    (outerSigs :
      (transportCheckedContext same outer).sigs = outer.sigs)
    (extendedSigs :
      ((transportCheckedContext same outer).extend rightSite).sigs =
        (outer.extend site).sigs)
    (above : DiagramContext definitions outer.sigs [])
    (body : Region definitions (outer.extend site).sigs) :
    (outerSigs.symm ▸ above).fill
        (ConcreteElaboration.finishRegion right.val
          (transportCheckedContext same outer) rightSite
          (extendedSigs.symm ▸ body)) =
      above.fill
        (ConcreteElaboration.finishRegion left.val outer site body) := by
  cases same
  cases siteExact
  rfl

theorem transport_region_val
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (region : left.RegionId) :
    ((same ▸ region : right.RegionId)).val = region.val := by
  cases same
  rfl

def transportSiteCompilation
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site) :
    SiteCompilation right (same ▸ site) := by
  cases same
  exact compiled

private theorem transportSiteCompilation_visible_sigs
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site) :
    (transportSiteCompilation same compiled).frame.visible.sigs =
      compiled.frame.visible.sigs := by
  cases same
  rfl

theorem transportSiteCompilation_visible
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site) :
    (transportSiteCompilation same compiled).frame.visible =
      same ▸ compiled.frame.visible := by
  cases same
  rfl

theorem transportSiteCompilation_visible_checked
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site) :
    (transportSiteCompilation same compiled).frame.visible =
      transportCheckedContext same compiled.frame.visible := by
  cases same
  rfl

private theorem castSiteCompilation_visible_sigs
    {definitions : List (List Sig)}
    {diagram : CheckedDiagram definitions}
    {left right : diagram.val.RegionId}
    (same : left = right)
    (compiled : SiteCompilation diagram left) :
    (same ▸ compiled).frame.visible.sigs =
      compiled.frame.visible.sigs := by
  cases same
  rfl

theorem castSiteCompilation_visible
    {definitions : List (List Sig)}
    {diagram : CheckedDiagram definitions}
    {left right : diagram.val.RegionId}
    (same : left = right)
    (compiled : SiteCompilation diagram left) :
    (same ▸ compiled).frame.visible = compiled.frame.visible := by
  cases same
  rfl

theorem transportCheckedAboveDecomposition
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (leftSite : left.val.RegionId)
    (rightSite : right.val.RegionId)
    (siteExact :
      same ▸ leftSite = rightSite)
    (leftOuter : ConcreteElaboration.WireContext left.val)
    (leftCompiled : SiteCompilation left leftSite)
    (leftAbove :
      DiagramContext definitions leftOuter.sigs [])
    (leftVisibleExact :
      leftCompiled.frame.visible = leftOuter.extend leftSite)
    (leftDecomposition :
      DiagramContext.StopsAboveBindMany
        ((left.val.wiresAt leftSite).map
          (fun wire => (left.val.wires wire).sig))
        leftAbove
        (((congrArg ConcreteElaboration.WireContext.sigs
              leftVisibleExact).trans
            (ConcreteElaboration.WireContext.sigs_extend
              leftOuter leftSite)) ▸
          leftCompiled.frame.context))
    (rightVisibleExact :
      (siteExact ▸
          transportSiteCompilation same leftCompiled).frame.visible =
        (transportCheckedContext same leftOuter).extend rightSite) :
    DiagramContext.StopsAboveBindMany
      ((right.val.wiresAt rightSite).map
        (fun wire => (right.val.wires wire).sig))
      ((transport_checked_context_sigs same leftOuter).symm ▸ leftAbove)
      (((congrArg ConcreteElaboration.WireContext.sigs
            rightVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend
            (transportCheckedContext same leftOuter) rightSite)) ▸
        (siteExact ▸
          transportSiteCompilation same leftCompiled).frame.context) := by
  cases same
  cases siteExact
  have visibleProofExact :
      rightVisibleExact = leftVisibleExact :=
    Subsingleton.elim _ _
  cases visibleProofExact
  exact leftDecomposition

theorem transportedSiteCompilation_body
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site)
    {rightSite : right.val.RegionId}
    (siteExact : same ▸ site = rightSite) :
    ∃ visibleSigsExact :
        compiled.frame.visible.sigs =
          (siteExact ▸ transportSiteCompilation same compiled).frame.visible.sigs,
      visibleSigsExact ▸ compiled.frame.siteBody =
        (siteExact ▸ transportSiteCompilation same compiled).frame.siteBody := by
  cases same
  cases siteExact
  exact ⟨rfl, rfl⟩

private def castRegionFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    RegionFrame definitions diagram right :=
  same ▸ frame

private theorem castRegionFrame_visible
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    (castRegionFrame same frame).visible = frame.visible := by
  cases same
  rfl

theorem regionFrame_siteBody_heq
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {outer : ConcreteElaboration.WireContext diagram}
    {left right : RegionFrame definitions diagram outer}
    (same : left = right) :
    HEq left.siteBody right.siteBody := by
  cases same
  rfl

private theorem compileRegionFrame_cast_outer
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {site region : diagram.RegionId}
    {fuel : Nat}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left)
    (generated :
      compileRegionFrame? definitions diagram site fuel region left =
        some frame) :
    compileRegionFrame? definitions diagram site fuel region right =
      some (castRegionFrame same frame) := by
  cases same
  exact generated

private theorem compileRegionFrame_cast_fuel
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {site region : diagram.RegionId}
    {leftFuel rightFuel : Nat}
    (same : leftFuel = rightFuel)
    (outer : ConcreteElaboration.WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (generated :
      compileRegionFrame? definitions diagram site leftFuel region outer =
        some frame) :
    compileRegionFrame? definitions diagram site rightFuel region outer =
      some frame := by
  cases same
  exact generated

structure GeneratedInnerFrameReceipt
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat) where
  site : diagram.RegionId
  region : diagram.RegionId
  outer : ConcreteElaboration.WireContext diagram
  frame : RegionFrame definitions diagram outer
  generated :
    compileRegionFrame? definitions diagram site fuel region outer =
      some frame
  above : ConcreteElaboration.ContextAbove diagram outer region
  inner :
    DiagramContext definitions frame.visible.sigs
      (outer.extend region).sigs
  decomposition :
    frame.context =
      bindContextFor diagram outer.ids (diagram.wiresAt region) inner

def GeneratedInnerFrameReceipt.toFrameReceipt
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (receipt : GeneratedInnerFrameReceipt definitions diagram fuel) :
    GeneratedFrameReceipt definitions diagram fuel where
  site := receipt.site
  region := receipt.region
  outer := receipt.outer
  frame := receipt.frame
  generated := receipt.generated

private theorem GeneratedInnerFrameReceipt.transport_toFrameReceipt
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedInnerFrameReceipt definitions left fuel) :
    (same ▸ receipt).toFrameReceipt =
      same ▸ receipt.toFrameReceipt := by
  cases same
  rfl

theorem generatedInner_eq_insertionSourceInner
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {fuel : Nat}
    (source : GeneratedInnerFrameReceipt definitions base.val fuel)
    (siteOuter : ConcreteElaboration.WireContext base.val)
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext attachment
          source.outer)}
    (paired :
      InsertionCompilation.PairedInnerFrame compiled source.region
        source.outer siteOuter source.frame targetFrame) :
    source.inner = paired.sourceInner := by
  apply
    bindContextFor_injective base.val source.outer.ids
      (base.val.wiresAt source.region)
  exact source.decomposition.symm.trans paired.sourceDecomposition

/--
Transport the canonical singleton-erasure frame into the checked base owned by
the accepted join step. This is representation alignment only; it performs no
compiler traversal.
-/
def checkedBaseFrameReceipt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (generated :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication site)
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter) =
        some raw) :
    GeneratedFrameReceipt definitions step.base.val fuel :=
  step.base_generated.symm ▸
    { site := SingletonRemovalSemantics.targetRegion step.prior
        step.priorApplication site,
      region := SingletonRemovalSemantics.targetRegion step.prior
        step.priorApplication region,
      outer := SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceOuter,
      frame := raw
      generated := generated }

/--
Transport the paired inner context generated by singleton erasure into the
checked base owned by the accepted step. This extends the existing frame
receipt; it introduces no second compilation or context path.
-/
def checkedBaseInnerFrameReceipt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (generated :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication site)
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter) =
        some raw)
    (above :
      ConcreteElaboration.ContextAbove
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter)
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication region))
    (inner :
      DiagramContext definitions raw.visible.sigs
        ((SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter).extend
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)).sigs)
    (decomposition :
      raw.context =
        bindContextFor
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter).ids
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication).wiresAt
            (SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication region))
          inner) :
    GeneratedInnerFrameReceipt definitions step.base.val fuel :=
  step.base_generated.symm ▸
    { site := SingletonRemovalSemantics.targetRegion step.prior
        step.priorApplication site
      region := SingletonRemovalSemantics.targetRegion step.prior
        step.priorApplication region
      outer := SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceOuter
      frame := raw
      generated := generated
      above := above
      inner := inner
      decomposition := decomposition }

theorem checkedBaseInnerFrameReceipt_toFrame
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (generated :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication site)
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter) =
        some raw)
    (above :
      ConcreteElaboration.ContextAbove
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter)
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication region))
    (inner :
      DiagramContext definitions raw.visible.sigs
        ((SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter).extend
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)).sigs)
    (decomposition :
      raw.context =
        bindContextFor
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter).ids
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication).wiresAt
            (SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication region))
          inner) :
    (checkedBaseInnerFrameReceipt step site region fuel sourceOuter raw
      generated above inner decomposition).toFrameReceipt =
        checkedBaseFrameReceipt step site region fuel sourceOuter raw
          generated := by
  unfold checkedBaseInnerFrameReceipt checkedBaseFrameReceipt
  rw [GeneratedInnerFrameReceipt.transport_toFrameReceipt]
  rfl

private theorem checkedBaseFrameReceipt_site
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (generated :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication site)
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter) =
        some raw) :
    (checkedBaseFrameReceipt step site region fuel sourceOuter raw
        generated).site =
      Fin.cast
        (congrArg ConcreteDiagram.regionCount step.base_generated).symm
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication site) := by
  apply Fin.ext
  exact
    (GeneratedFrameReceipt.transport_site_val
      step.base_generated.symm
      { site := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication site
        region := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication region
        outer := SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter
        frame := raw
        generated := generated }).trans (by simp)

theorem checkedBaseFrameReceipt_region
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (generated :
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication site)
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter) =
        some raw) :
    (checkedBaseFrameReceipt step site region fuel sourceOuter raw
        generated).region =
      Fin.cast
        (congrArg ConcreteDiagram.regionCount step.base_generated).symm
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication region) := by
  apply Fin.ext
  exact
    (GeneratedFrameReceipt.transport_region_val
      step.base_generated.symm
      { site := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication site
        region := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication region
        outer := SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter
        frame := raw
        generated := generated }).trans (by simp)

/--
The erased root frame is the insertion compiler's unique checked base-site
frame. This is the sole frame-alignment fact needed by the step composition.
-/
private theorem checkedBaseSiteFrame_eq
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled :
      InsertionCompilation contentCompiled step.attachment)
    (raw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication
          (ConcreteElaboration.WireContext.empty step.prior.val)))
    (provenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion)
        (step.prior.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty step.prior.val)
        step.prior.val.root step.priorSite.frame raw) :
    let receipt :=
      checkedBaseFrameReceipt step
        (step.priorRegionImage step.sourceRegion)
        step.prior.val.root (step.prior.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty step.prior.val)
        raw provenance.targetGenerated
    ∃ outerExact :
        receipt.outer =
          ConcreteElaboration.WireContext.empty step.base.val,
      castRegionFrame outerExact receipt.frame = compiled.site.frame := by
  let receipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      step.prior.val.root (step.prior.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty step.prior.val)
      raw provenance.targetGenerated
  have siteExact : receipt.site = step.site := by
    exact
      (checkedBaseFrameReceipt_site step
        (step.priorRegionImage step.sourceRegion)
        step.prior.val.root (step.prior.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty step.prior.val)
        raw provenance.targetGenerated).trans
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetSite_eq_site
            step)
  have regionExact : receipt.region = step.base.val.root := by
    apply Fin.ext
    calc
      receipt.region.val =
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication step.prior.val.root).val := by
              exact
                GeneratedFrameReceipt.transport_region_val
                  step.base_generated.symm
                  { site :=
                      SingletonRemovalSemantics.targetRegion step.prior
                        step.priorApplication
                        (step.priorRegionImage step.sourceRegion)
                    region :=
                      SingletonRemovalSemantics.targetRegion step.prior
                        step.priorApplication step.prior.val.root
                    outer :=
                      SingletonRemovalSemantics.targetContext step.prior
                        step.priorApplication
                        (ConcreteElaboration.WireContext.empty step.prior.val)
                    frame := raw
                    generated := provenance.targetGenerated }
      _ = step.prior.val.root.val := by simp
      _ = step.base.val.root.val := by
        simpa [
          ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate] using
            (transport_root_val step.base_generated).symm
  have outerExact :
      receipt.outer =
        ConcreteElaboration.WireContext.empty step.base.val := by
    calc
      receipt.outer =
          step.base_generated.symm ▸
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication
              (ConcreteElaboration.WireContext.empty step.prior.val) := by
                exact
                  GeneratedFrameReceipt.transport_outer
                    step.base_generated.symm
                    { site :=
                        SingletonRemovalSemantics.targetRegion step.prior
                          step.priorApplication
                          (step.priorRegionImage step.sourceRegion)
                      region :=
                        SingletonRemovalSemantics.targetRegion step.prior
                          step.priorApplication step.prior.val.root
                      outer :=
                        SingletonRemovalSemantics.targetContext step.prior
                          step.priorApplication
                          (ConcreteElaboration.WireContext.empty step.prior.val)
                      frame := raw
                      generated := provenance.targetGenerated }
      _ = step.base_generated.symm ▸
            ConcreteElaboration.WireContext.empty
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                step.prior step.priorApplication) := by rfl
      _ = ConcreteElaboration.WireContext.empty step.base.val :=
        transport_empty_context step.base_generated.symm
  have fuelExact :
      step.prior.val.regionCount + 1 =
        step.base.val.regionCount + 1 := by
    have sameCount :=
      congrArg ConcreteDiagram.regionCount step.base_generated
    have countExact :
        step.prior.val.regionCount = step.base.val.regionCount := by
      simpa [
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate] using
          sameCount.symm
    omega
  have generated := receipt.generated
  rw [siteExact, regionExact] at generated
  have generatedAtFuel :=
    compileRegionFrame_cast_fuel fuelExact receipt.outer receipt.frame
      generated
  have generatedAtEmpty :=
    compileRegionFrame_cast_outer outerExact receipt.frame generatedAtFuel
  refine ⟨outerExact, ?_⟩
  exact Option.some.inj
    (generatedAtEmpty.symm.trans compiled.site.frame_generated)

/--
Derive the root-frame alignment entirely from the accepted step and insertion
receipt. Callers provide no site compilation or erasure compiler equation.
-/
private theorem RelationJoinStep.baseSiteAlignment
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled :
      InsertionCompilation contentCompiled step.attachment) :
    ∃ (raw :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication
            (ConcreteElaboration.WireContext.empty step.prior.val)))
      (provenance :
        SingletonRemovalSemantics.ErasureFrameProvenance step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion)
          (step.prior.val.regionCount + 1)
          (ConcreteElaboration.WireContext.empty step.prior.val)
          step.prior.val.root step.priorSite.frame raw),
      let receipt :=
        checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          step.prior.val.root (step.prior.val.regionCount + 1)
          (ConcreteElaboration.WireContext.empty step.prior.val)
          raw provenance.targetGenerated
      ∃ outerExact :
          receipt.outer =
            ConcreteElaboration.WireContext.empty step.base.val,
        castRegionFrame outerExact receipt.frame =
          compiled.site.frame := by
  have sourceAbove :
      ConcreteElaboration.ContextAbove step.prior.val
        (ConcreteElaboration.WireContext.empty step.prior.val)
        step.prior.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty],
      by
        intro wire member
        simp [ConcreteElaboration.WireContext.empty] at member⟩
  have paired :=
    SingletonRemovalSemantics.RelationJoinStep.pairedGeneratedFrame step
      (step.priorRegionImage step.sourceRegion)
      step.prior.val.root (step.prior.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty step.prior.val)
      step.priorSite.frame sourceAbove step.priorSite.frame_generated
  rcases paired with ⟨raw, _sourceAbove, _sourceGenerated, provenance⟩
  exact
    ⟨raw, provenance,
      checkedBaseSiteFrame_eq step contentCompiled compiled raw provenance⟩

private theorem checkedBaseRelativeVisible_eq_site
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled :
      InsertionCompilation contentCompiled step.attachment)
    {sourceOuter :
      ConcreteElaboration.WireContext step.prior.val}
    {sourceFrame :
      RegionFrame definitions step.prior.val sourceOuter}
    (sourceVisible :
      sourceFrame.visible = step.priorSite.frame.visible)
    (region : step.prior.val.RegionId)
    (fuel : Nat)
    (relativeRaw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (relativeProvenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel sourceOuter region
        sourceFrame relativeRaw)
    (rootRaw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication
          (ConcreteElaboration.WireContext.empty step.prior.val)))
    (rootProvenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion)
        (step.prior.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty step.prior.val)
        step.prior.val.root step.priorSite.frame rootRaw)
    (rootOuterExact :
      (checkedBaseFrameReceipt step
        (step.priorRegionImage step.sourceRegion)
        step.prior.val.root (step.prior.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty step.prior.val)
        rootRaw rootProvenance.targetGenerated).outer =
          ConcreteElaboration.WireContext.empty step.base.val)
    (rootFrameExact :
      castRegionFrame rootOuterExact
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          step.prior.val.root (step.prior.val.regionCount + 1)
          (ConcreteElaboration.WireContext.empty step.prior.val)
          rootRaw rootProvenance.targetGenerated).frame =
        compiled.site.frame) :
    (checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion) region fuel sourceOuter
      relativeRaw relativeProvenance.targetGenerated).frame.visible =
        compiled.site.frame.visible := by
  let same := step.base_generated.symm
  let relativeReceipt : GeneratedFrameReceipt definitions step.base.val fuel :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion) region fuel sourceOuter
      relativeRaw relativeProvenance.targetGenerated
  let rootReceipt :
      GeneratedFrameReceipt definitions step.base.val
        (step.prior.val.regionCount + 1) :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      step.prior.val.root (step.prior.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty step.prior.val)
      rootRaw rootProvenance.targetGenerated
  calc
    relativeReceipt.frame.visible =
        same ▸ relativeRaw.visible :=
      GeneratedFrameReceipt.transport_frame_visible same
        { site := SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage step.sourceRegion)
          region := SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication region
          outer := SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter
          frame := relativeRaw
          generated := relativeProvenance.targetGenerated }
    _ = same ▸
        SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible := by
      exact congrArg (fun context => same ▸ context)
        relativeProvenance.targetVisible
    _ = same ▸
        SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication step.priorSite.frame.visible := by
      exact congrArg
        (fun context =>
          same ▸
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication context)
        sourceVisible
    _ = same ▸ rootRaw.visible := by
      exact congrArg (fun context => same ▸ context)
        rootProvenance.targetVisible.symm
    _ = rootReceipt.frame.visible := by
      exact
        (GeneratedFrameReceipt.transport_frame_visible same
          { site := SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
            region := SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication step.prior.val.root
            outer := SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication
              (ConcreteElaboration.WireContext.empty step.prior.val)
            frame := rootRaw
            generated := rootProvenance.targetGenerated }).symm
    _ = (castRegionFrame rootOuterExact rootReceipt.frame).visible := by
      exact (castRegionFrame_visible rootOuterExact rootReceipt.frame).symm
    _ = compiled.site.frame.visible :=
      congrArg RegionFrame.visible rootFrameExact

/--
Derive the pre-binder frame at the dying scope from the accepted application
site. The paired erasure receipt is generated from that same relative frame.
-/
theorem RelationJoinStep.dyingScopeErasure
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    ∃ (scopeCompiled :
        SiteCompilation step.prior
          (step.priorRegionImage (source.val.wires dying).scope))
      (outer : ConcreteElaboration.WireContext step.prior.val)
      (fuel : Nat)
      (relative : RegionFrame definitions step.prior.val outer)
      (relativeVisible :
        relative.visible = step.priorSite.frame.visible)
      (inner :
        DiagramContext definitions relative.visible.sigs
          (outer.extend
            (step.priorRegionImage
              (source.val.wires dying).scope)).sigs)
      (scopeVisible :
        scopeCompiled.frame.visible =
          outer.extend
            (step.priorRegionImage
              (source.val.wires dying).scope)),
      ConcreteElaboration.ContextAbove step.prior.val outer
          (step.priorRegionImage (source.val.wires dying).scope) ∧
        compileRegionFrame? definitions step.prior.val
            (step.priorRegionImage step.sourceRegion) fuel
            (step.priorRegionImage (source.val.wires dying).scope)
            outer =
          some relative ∧
        congrArg ConcreteElaboration.WireContext.sigs relativeVisible ▸
            relative.siteBody =
          step.priorSite.frame.siteBody ∧
        relative.context =
          bindContextFor step.prior.val outer.ids
            (step.prior.val.wiresAt
              (step.priorRegionImage
                (source.val.wires dying).scope))
            inner ∧
        congrArg ConcreteElaboration.WireContext.sigs scopeVisible ▸
            scopeCompiled.frame.siteBody =
          inner.fill relative.siteBody ∧
        SingletonRemovalSemantics.PairedGeneratedFrame step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel outer relative := by
  obtain ⟨scopeCompiled, outer, fuel, relative, relativeVisible,
      inner, scopeVisible, _rootInner, sourceAbove, sourceGenerated,
      relativeBody, relativeContext, scopeBody, _rootBody,
      _replacementBody, _cutDepth⟩ :=
    step.priorSite.factorAt_relative_origin
      (step.priorRegionImage (source.val.wires dying).scope)
      step.prior_dying_scope_encloses_site
  have paired :=
    SingletonRemovalSemantics.RelationJoinStep.pairedGeneratedFrame step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer relative sourceAbove sourceGenerated
  exact
    ⟨scopeCompiled, outer, fuel, relative, relativeVisible, inner,
      scopeVisible, sourceAbove, sourceGenerated, relativeBody,
      relativeContext, scopeBody, paired⟩

/--
Compose the step-owned erasure frame with the accepted insertion compiler at
the still-open dying scope.
-/
theorem RelationJoinStep.pairedInsertionAtDying
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled :
      InsertionCompilation contentCompiled step.attachment)
    {sourceOuter :
      ConcreteElaboration.WireContext step.prior.val}
    {sourceFrame :
      RegionFrame definitions step.prior.val sourceOuter}
    (sourceVisible :
      sourceFrame.visible = step.priorSite.frame.visible)
    {fuel : Nat}
    (pairedErasure :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel sourceOuter sourceFrame) :
    ∃ (relativeRaw :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter))
      (relativeProvenance :
        SingletonRemovalSemantics.ErasureFrameProvenance step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion) fuel sourceOuter
          (step.priorRegionImage (source.val.wires dying).scope)
          sourceFrame relativeRaw)
      (siteOuter : ConcreteElaboration.WireContext step.base.val)
      (targetFrame :
        RegionFrame definitions step.attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel sourceOuter relativeRaw
              relativeProvenance.targetGenerated).outer)),
      InsertionCompilation.PairedGeneratedFrame compiled
        (step.baseRegionImage (source.val.wires dying).scope)
        fuel
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel sourceOuter relativeRaw
          relativeProvenance.targetGenerated).outer
        siteOuter
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel sourceOuter relativeRaw
          relativeProvenance.targetGenerated).frame
        targetFrame := by
  rcases pairedErasure with
    ⟨relativeRaw, sourceAbove, _sourceGenerated, relativeProvenance⟩
  obtain ⟨rootRaw, rootProvenance, rootOuterExact, rootFrameExact⟩ :=
    RelationJoinStep.baseSiteAlignment step contentCompiled compiled
  let receipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel sourceOuter relativeRaw relativeProvenance.targetGenerated
  have siteExact : receipt.site = step.site := by
    exact
      (checkedBaseFrameReceipt_site step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel sourceOuter relativeRaw
        relativeProvenance.targetGenerated).trans
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetSite_eq_site
            step)
  have regionExact :
      receipt.region =
        step.baseRegionImage (source.val.wires dying).scope := by
    exact
      (checkedBaseFrameReceipt_region step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel sourceOuter relativeRaw
        relativeProvenance.targetGenerated).trans
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetRegion_eq_baseRegionImage
            step
              (source.val.wires dying).scope)
  have visibleExact :
      receipt.frame.visible = compiled.site.frame.visible :=
    checkedBaseRelativeVisible_eq_site step contentCompiled compiled
      sourceVisible
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel relativeRaw relativeProvenance rootRaw rootProvenance
      rootOuterExact rootFrameExact
  have rawAbove :=
    SingletonRemovalSemantics.RelationJoinStep.rawTargetContext_above step
      sourceOuter
      (step.priorRegionImage (source.val.wires dying).scope)
      sourceAbove
  have checkedAbove :
      ConcreteElaboration.ContextAbove step.base.val receipt.outer
        receipt.region :=
    GeneratedFrameReceipt.transport_above step.base_generated.symm
      { site := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion)
        region := SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication
          (step.priorRegionImage (source.val.wires dying).scope)
        outer := SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter
        frame := relativeRaw
        generated := relativeProvenance.targetGenerated }
      rawAbove
  have generated := receipt.generated
  rw [regionExact] at checkedAbove
  rw [siteExact, regionExact] at generated
  obtain ⟨siteOuter, _siteFuel, _siteNodes, _siteChildren,
      siteVisible, _siteNodesCompiled, _siteChildrenCompiled,
      _siteBodyExact⟩ :=
    compiled.site.site_origin
  obtain ⟨targetFrame, pairedInsertion⟩ :=
    InsertionCompilation.pairedGeneratedFrame compiled
      (step.baseRegionImage (source.val.wires dying).scope)
      fuel receipt.outer siteOuter receipt.frame checkedAbove siteVisible
      (visibleExact.trans siteVisible) generated
  exact
    ⟨relativeRaw, relativeProvenance, siteOuter, targetFrame,
      pairedInsertion⟩

theorem RelationJoinStep.pairedInsertion_baseVisibleExact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    {sourceOuter : ConcreteElaboration.WireContext step.prior.val}
    {sourceFrame : RegionFrame definitions step.prior.val sourceOuter}
    {fuel : Nat}
    (relativeRaw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (relativeProvenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel sourceOuter
        (step.priorRegionImage (source.val.wires dying).scope)
        sourceFrame relativeRaw)
    {siteOuter : ConcreteElaboration.WireContext step.base.val}
    {targetFrame :
      RegionFrame definitions step.attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext step.attachment
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel sourceOuter relativeRaw
            relativeProvenance.targetGenerated).outer)}
    (paired :
      InsertionCompilation.PairedGeneratedFrame compiled
        (step.baseRegionImage (source.val.wires dying).scope)
        fuel
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel sourceOuter relativeRaw
          relativeProvenance.targetGenerated).outer
        siteOuter
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel sourceOuter relativeRaw
          relativeProvenance.targetGenerated).frame
        targetFrame) :
    step.base_generated.symm ▸
        SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible =
      compiled.site.frame.visible := by
  let receipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel sourceOuter relativeRaw relativeProvenance.targetGenerated
  calc
    step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible =
        step.base_generated.symm ▸ relativeRaw.visible := by
          exact congrArg (fun context => step.base_generated.symm ▸ context)
            relativeProvenance.targetVisible.symm
    _ = receipt.frame.visible :=
      (GeneratedFrameReceipt.transport_frame_visible
        step.base_generated.symm
        { site := SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage step.sourceRegion)
          region := SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope)
          outer := SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceOuter
          frame := relativeRaw
          generated := relativeProvenance.targetGenerated }).symm
    _ = siteOuter.extend step.site := paired.sourceVisible
    _ = compiled.site.frame.visible := paired.siteVisible.symm


end Internal

end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
