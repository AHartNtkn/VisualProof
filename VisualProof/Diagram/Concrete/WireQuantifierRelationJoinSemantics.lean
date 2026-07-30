import VisualProof.Diagram.Concrete.WireQuantifierSemantics
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemoval
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalZipper
import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalZipper
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityZipper

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

private structure GeneratedFrameReceipt
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

private theorem GeneratedFrameReceipt.transport_region_val
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    ((same ▸ receipt).region).val = receipt.region.val := by
  cases same
  rfl

private theorem GeneratedFrameReceipt.transport_outer
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {fuel : Nat}
    (same : left = right)
    (receipt : GeneratedFrameReceipt definitions left fuel) :
    (same ▸ receipt).outer = same ▸ receipt.outer := by
  cases same
  rfl

private theorem GeneratedFrameReceipt.transport_frame_visible
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

private theorem transport_checked_region_val
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    ((same ▸ region : right.val.RegionId)).val = region.val := by
  cases same
  rfl

private def transportCheckedContext
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    ConcreteElaboration.WireContext right.val := by
  cases same
  exact context

private theorem transport_checked_context_cast_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    same ▸ context = transportCheckedContext same context := by
  cases same
  rfl

private def transportCheckedRegion
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    right.val.RegionId := by
  cases same
  exact region

private theorem transportCheckedRegion_val
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (region : left.val.RegionId) :
    (transportCheckedRegion same region).val = region.val := by
  cases same
  rfl

private theorem transport_checked_context_sigs
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val) :
    (transportCheckedContext same context).sigs = context.sigs := by
  cases same
  rfl

private theorem transport_checked_extended_context
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

private theorem transport_checked_context_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {first second : ConcreteElaboration.WireContext left.val}
    (exact : first = second) :
    transportCheckedContext same first =
      transportCheckedContext same second := by
  cases same
  exact exact

private theorem transport_checked_root_fill
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

private theorem transport_region_val
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (region : left.RegionId) :
    ((same ▸ region : right.RegionId)).val = region.val := by
  cases same
  rfl

private def transportSiteCompilation
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

private theorem transportSiteCompilation_visible
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    {site : left.val.RegionId}
    (compiled : SiteCompilation left site) :
    (transportSiteCompilation same compiled).frame.visible =
      same ▸ compiled.frame.visible := by
  cases same
  rfl

private theorem transportSiteCompilation_visible_checked
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

private theorem castSiteCompilation_visible
    {definitions : List (List Sig)}
    {diagram : CheckedDiagram definitions}
    {left right : diagram.val.RegionId}
    (same : left = right)
    (compiled : SiteCompilation diagram left) :
    (same ▸ compiled).frame.visible = compiled.frame.visible := by
  cases same
  rfl

private theorem transportCheckedAboveDecomposition
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

private theorem transportedSiteCompilation_body
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

private theorem regionFrame_siteBody_heq
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

private structure GeneratedInnerFrameReceipt
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

private def GeneratedInnerFrameReceipt.toFrameReceipt
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

private theorem generatedInner_eq_insertionSourceInner
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
private def checkedBaseFrameReceipt
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
private def checkedBaseInnerFrameReceipt
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

private theorem checkedBaseInnerFrameReceipt_toFrame
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

private theorem checkedBaseFrameReceipt_region
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
private theorem RelationJoinStep.dyingScopeErasure
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
private theorem RelationJoinStep.pairedInsertionAtDying
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

private theorem RelationJoinStep.pairedInsertion_baseVisibleExact
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

private theorem castCompiledAtom
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (node : diagram.NodeId)
    (args : List Sig)
    (head : Var left.sigs (.rel args))
    (arguments : Vars left.sigs args)
    (headWire : diagram.WireId)
    (argumentWires : List diagram.WireId)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram left [node] =
        some (.cons (.atom head arguments) .nil))
    (headOrigin :
      ConcreteElaboration.WireContext.origin diagram left.ids head =
        headWire)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins diagram left arguments =
        argumentWires) :
    ∃ (castHead : Var right.sigs (.rel args))
      (castArguments : Vars right.sigs args),
      ConcreteElaboration.compileNodes? definitions diagram right [node] =
        some (.cons (.atom castHead castArguments) .nil) ∧
      ConcreteElaboration.WireContext.origin diagram right.ids castHead =
        headWire ∧
      ConcreteElaboration.variableOrigins diagram right castArguments =
        argumentWires := by
  cases same
  exact ⟨head, arguments, compiled, headOrigin, argumentOrigins⟩

/--
The accepted application remains the same ordered atom in the relative frame
at the dying scope.
-/
private theorem RelationJoinStep.relativeCompiledApplication
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {outer : ConcreteElaboration.WireContext step.prior.val}
    (relative : RegionFrame definitions step.prior.val outer)
    (relativeVisible :
      relative.visible = step.priorSite.frame.visible) :
    ∃ (head : Var relative.visible.sigs (.rel step.relationArgs))
      (arguments : Vars relative.visible.sigs step.relationArgs),
      ConcreteElaboration.compileNodes? definitions step.prior.val
          relative.visible [step.priorApplication] =
        some (.cons (.atom head arguments) .nil) ∧
      ConcreteElaboration.WireContext.origin step.prior.val
          relative.visible.ids head =
        step.priorWireImage dying ∧
      ConcreteElaboration.variableOrigins step.prior.val
          relative.visible arguments =
        step.priorArguments := by
  obtain ⟨applicationOuter, applicationVisible, head, arguments,
      compiled, headOrigin, argumentOrigins⟩ :=
    SingletonRemovalSemantics.RelationJoinStep.compiledApplication step
  exact
    castCompiledAtom
      (applicationVisible.symm.trans relativeVisible.symm)
      step.priorApplication step.relationArgs head arguments
      (step.priorWireImage dying) step.priorArguments
      compiled headOrigin argumentOrigins

/--
Transport the rule-owned source parameter-scope premise through the step's
sole region and wire images. No caller supplies an intermediate scope proof.
-/
private theorem RelationJoinStep.priorParameterScopes
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (parameterScopes :
      ∀ position : Fin step.sourceParameters.length,
        source.val.Encloses
          (source.val.wires
            (step.sourceParameters.get position)).scope
          (source.val.wires dying).scope) :
    ∀ position : Fin step.sourceParameters.length,
      step.prior.val.Encloses
        (step.prior.val.wires
          (step.priorWireImage
            (step.sourceParameters.get position))).scope
        (step.prior.val.wires (step.priorWireImage dying)).scope := by
  intro position
  rw [step.priorWireScopeExact, step.priorWireScopeExact]
  exact
    (step.priorRegionImageEncloses
      (source.val.wires (step.sourceParameters.get position)).scope
      (source.val.wires dying).scope).2
      (parameterScopes position)

private def variableOfMember
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) →
      (wire : diagram.WireId) →
      wire ∈ ids →
      Var (ids.map fun candidate => (diagram.wires candidate).sig)
        (diagram.wires wire).sig
  | [], _, member => False.elim (by simpa using member)
  | head :: tail, wire, member =>
      if same : wire = head then
        same ▸ Var.here
      else
        .there
          (variableOfMember diagram tail wire
            ((List.mem_cons.mp member).resolve_left same))

private theorem variableOfMember_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (variableOfMember diagram ids wire member) =
      wire := by
  induction ids generalizing wire with
  | nil => simp at member
  | cons head tail induction =>
      simp only [variableOfMember]
      split
      · rename_i same
        subst wire
        rfl
      · rename_i different
        exact
          induction wire
            ((List.mem_cons.mp member).resolve_left different)

private def variablesOfMembers
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram) :
    (wires : List diagram.WireId) →
      (∀ wire, wire ∈ wires → wire ∈ context.ids) →
      Vars context.sigs
        (wires.map fun wire => (diagram.wires wire).sig)
  | [], _ => .nil
  | head :: tail, members =>
      .cons
        (variableOfMember diagram context.ids head
          (members head (by simp)))
        (variablesOfMembers diagram context tail
          (fun wire member => members wire (by simp [member])))

private theorem variablesOfMembers_origins
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (wires : List diagram.WireId)
    (members : ∀ wire, wire ∈ wires → wire ∈ context.ids) :
    ConcreteElaboration.variableOrigins diagram context
        (variablesOfMembers diagram context wires members) =
      wires := by
  induction wires generalizing context with
  | nil => rfl
  | cons head tail induction =>
      change
        ConcreteElaboration.WireContext.origin diagram context.ids
              (variableOfMember diagram context.ids head
                (members head (by simp))) ::
            ConcreteElaboration.variableOrigins diagram context
              (variablesOfMembers diagram context tail
                (fun wire member => members wire (by simp [member]))) =
          head :: tail
      rw [variableOfMember_origin]
      exact
        congrArg (List.cons head)
          (induction context
            (fun wire member => members wire (by simp [member])))

private theorem variableOrigins_rename_mapped
    (sourceDiagram : ConcreteDiagram sourceDefinitionCount)
    (targetDiagram : ConcreteDiagram targetDefinitionCount)
    (sourceContext : ConcreteElaboration.WireContext sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext targetDiagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (sourceMap : α → sourceDiagram.WireId)
    (targetMap : α → targetDiagram.WireId)
    (action :
      ∀ (key : α) {sig : Sig}
        (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin sourceDiagram
            sourceContext.ids value = sourceMap key →
          ConcreteElaboration.WireContext.origin targetDiagram
              targetContext.ids (rho value) = targetMap key)
    (variables : Vars sourceContext.sigs args)
    (keys : List α)
    (origins :
      ConcreteElaboration.variableOrigins sourceDiagram sourceContext
          variables =
        keys.map sourceMap) :
    ConcreteElaboration.variableOrigins targetDiagram targetContext
        (Vars.rename rho variables) =
      keys.map targetMap := by
  induction variables generalizing keys with
  | nil =>
      cases keys with
      | nil => rfl
      | cons key keys =>
          simp only [List.map_cons] at origins
          contradiction
  | cons value values induction =>
      cases keys with
      | nil =>
          simp only [List.map_nil] at origins
          contradiction
      | cons key keys =>
          simp only [ConcreteElaboration.variableOrigins, List.map_cons,
            List.cons.injEq] at origins
          change
            ConcreteElaboration.WireContext.origin targetDiagram
                targetContext.ids (rho value) ::
                  ConcreteElaboration.variableOrigins targetDiagram
                    targetContext (Vars.rename rho values) =
              targetMap key :: keys.map targetMap
          rw [action key value origins.1]
          exact congrArg (List.cons (targetMap key))
            (induction keys origins.2)

private theorem RelationJoinStep.baseRegionImage_injective
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    Function.Injective step.baseRegionImage := by
  intro left right same
  rw [step.baseRegionImageExact, step.baseRegionImageExact] at same
  have erasedSame :
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication (step.priorRegionImage left) =
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication
          (step.priorRegionImage right) := by
    exact checkedRegion_injective step.base_generated same
  have priorSame :=
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_injective
      step.prior step.priorApplication erasedSame
  have leftRight :
      source.val.Encloses left right := by
    apply
      (step.priorRegionImageEncloses left right).mp
    simpa [priorSame] using
      step.prior.val.encloses_refl (step.priorRegionImage right)
  have rightLeft :
      source.val.Encloses right left := by
    apply
      (step.priorRegionImageEncloses right left).mp
    simpa [priorSame] using
      step.prior.val.encloses_refl (step.priorRegionImage left)
  exact
    InsertionCompilation.NaturalityInternal.checked_encloses_antisymm
      definitions source.val source.property leftRight rightLeft

private theorem transport_context_sigs
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left) :
    (same ▸ context).sigs = context.sigs := by
  cases same
  rfl

private theorem transport_extended_context_sigs
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (region : left.RegionId) :
    ((same ▸ context).extend (same ▸ region)).sigs =
      (context.extend region).sigs := by
  cases same
  rfl

private theorem transport_extended_context
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (region : left.RegionId) :
    (same ▸ context).extend (same ▸ region) =
      same ▸ context.extend region := by
  cases same
  rfl

private def transportVariables
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (variables : Vars context.sigs args) :
    Vars rightContext.sigs args :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ variables

private def transportVariable
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    Var rightContext.sigs sig :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ value

private theorem transportVariables_cons
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (head : Var context.sigs sig)
    (tail : Vars context.sigs args) :
    transportVariables same context rightContext contextExact
        (.cons head tail) =
      .cons
        (transportVariable same context rightContext contextExact head)
        (transportVariables same context rightContext contextExact tail) := by
  cases same
  cases contextExact
  rfl

private theorem transportVariable_origin
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin right rightContext.ids
        (transportVariable same context rightContext contextExact value) =
      Fin.cast (congrArg ConcreteDiagram.wireCount same)
        (ConcreteElaboration.WireContext.origin left context.ids value) := by
  cases same
  cases contextExact
  rfl

private theorem transportVariable_heq
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    HEq
      (transportVariable same context rightContext contextExact value)
      value := by
  cases same
  cases contextExact
  rfl

private def transportCheckedVariable
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    Var rightContext.sigs sig := by
  cases same
  exact transportVariable rfl context rightContext contextExact value

private theorem transportCheckedVariable_origin
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin right.val rightContext.ids
        (transportCheckedVariable same context rightContext contextExact
          value) =
      Fin.cast
        (congrArg ConcreteDiagram.wireCount
          (congrArg
            (fun checked : CheckedDiagram definitions => checked.val)
            same))
        (ConcreteElaboration.WireContext.origin left.val context.ids
          value) := by
  cases same
  cases contextExact
  rfl

private theorem transportCheckedVariable_heq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    HEq
      (transportCheckedVariable same context rightContext contextExact value)
      value := by
  cases same
  cases contextExact
  rfl

private theorem origin_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {sig : Sig}
    (value : Var left.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem variableOrigins_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (values : Vars left.sigs args) :
    ConcreteElaboration.variableOrigins diagram right
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ values) =
      ConcreteElaboration.variableOrigins diagram left values := by
  cases same
  rfl

private theorem cast_variable_heq
    {left right : List Sig}
    (same : left = right)
    (value : Var left sig) :
    HEq (same ▸ value) value := by
  cases same
  rfl

private theorem cast_renaming_roundtrip
    {left right source : List Sig}
    (same : left = right)
    (rho : WireRenaming source right)
    {sig : Sig}
    (value : Var source sig) :
    same ▸ ((same.symm ▸ rho) value) = rho value := by
  cases same
  rfl

private theorem cast_renaming_variables_heq
    {left right source args : List Sig}
    (same : left = right)
    (rho : WireRenaming source left)
    (values : Vars source args) :
    HEq (Vars.rename (same ▸ rho) values) (Vars.rename rho values) := by
  cases same
  rfl

private theorem cast_variables_heq
    {left right args : List Sig}
    (same : left = right)
    (values : Vars left args) :
    HEq (same ▸ values) values := by
  cases same
  rfl

private theorem cast_environment_variables_denote
    {left right args : List Sig}
    (same : left = right)
    (env : Env pre left)
    (values : Vars left args) :
    Vars.denote (same ▸ env) (same ▸ values) =
      Vars.denote env values := by
  cases same
  rfl

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

private theorem extendedContextRenaming_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    {sig : Sig}
    (value : Var (context.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        ((SingletonRemovalSemantics.targetContext source removed context).extend
          (SingletonRemovalSemantics.targetRegion source removed region)).ids
        (SingletonRemovalSemantics.extendedContextRenaming source removed
          context region value) =
      SingletonRemovalSemantics.targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          (context.extend region).ids value) := by
  unfold SingletonRemovalSemantics.extendedContextRenaming
  rw [origin_cast_renaming
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed)
    (SingletonRemovalSemantics.targetContext_extend source removed
      context region)
    (context.extend region).sigs
    (SingletonRemovalSemantics.contextRenaming source removed
      (context.extend region))]
  exact
    SingletonRemovalSemantics.contextRenaming_action source removed
      (context.extend region) value

private def transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rho : WireRenaming source' target') :
    WireRenaming source target :=
  fun {_} value => targetExact.symm ▸ rho (sourceExact ▸ value)

private theorem transportRenaming_transportCheckedVariable
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (sourceContext : List Sig)
    (rho : WireRenaming sourceContext context.sigs)
    {sig : Sig}
    (value : Var sourceContext sig) :
    transportRenaming rfl
        (transport_checked_context_sigs same context) rho value =
      transportCheckedVariable same context
        (transportCheckedContext same context)
        (transport_checked_context_cast_eq same context)
        (rho value) := by
  cases same
  rfl

private def embedOuterThroughSite
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site) :
    WireRenaming outer.sigs visible.sigs :=
  fun {_} value =>
    (congrArg ConcreteElaboration.WireContext.sigs
      same).symm ▸
        ConcreteElaboration.appendRightVar base.val
          (base.val.wiresAt site) value

/-- Embed the canonical site-outer variables through the site's local block. -/
def aboveScopeEmbedOuter
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    WireRenaming canonical.siteOuter.sigs compiled.frame.visible.sigs :=
  embedOuterThroughSite compiled.frame.visible canonical.siteOuter
    canonical.visibleExact

private theorem embedOuterThroughSite_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site)
    {sig : Sig}
    (value : Var outer.sigs sig) :
    ConcreteElaboration.WireContext.origin base.val visible.ids
        (embedOuterThroughSite visible outer same value) =
      ConcreteElaboration.WireContext.origin base.val outer.ids value := by
  cases same
  simpa [embedOuterThroughSite, ConcreteElaboration.WireContext.extend]
    using
      (ConcreteElaboration.origin_appendRightVar base.val
        (base.val.wiresAt site) value)

private theorem aboveScopeEmbedOuter_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled)
    {sig : Sig}
    (value : Var canonical.siteOuter.sigs sig) :
    ConcreteElaboration.WireContext.origin base.val
        compiled.frame.visible.ids
        (aboveScopeEmbedOuter canonical value) =
      ConcreteElaboration.WireContext.origin base.val
        canonical.siteOuter.ids value := by
  exact
    embedOuterThroughSite_origin compiled.frame.visible
      canonical.siteOuter canonical.visibleExact value

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

private theorem transportRenaming_reindexed_identity
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rawTargetToSource : target' = source')
    (targetToSource : target = source)
    (rho : WireRenaming source' target')
    (rawIdentity :
      (fun {sig} (value : Var source' sig) =>
        rawTargetToSource ▸ rho value) =
        (fun {_} (value : Var source' _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToSource ▸
        transportRenaming sourceExact targetExact rho value) =
      (fun {_} (value : Var source _) => value) := by
  cases sourceExact
  cases targetExact
  have proofExact : targetToSource = rawTargetToSource :=
    Subsingleton.elim _ _
  rw [proofExact]
  exact rawIdentity

private theorem envComp_transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source' = source)
    (targetExact : target' = target)
    (rho : WireRenaming source' target') :
    (fun (pre : PreModel.{u}) (env : Env pre target) =>
      sourceExact ▸ Env.comp (targetExact.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre target) =>
        Env.comp env
          (transportRenaming sourceExact.symm targetExact.symm rho)) := by
  cases sourceExact
  cases targetExact
  rfl

private theorem composeRenaming_reindexed_identity
    {source middle target : List Sig}
    (middleToSource : middle = source)
    (targetToMiddle : target = middle)
    (sourceToMiddle : WireRenaming source middle)
    (middleToTarget : WireRenaming middle target)
    (sourceToMiddleIdentity :
      (fun {sig} (value : Var source sig) =>
        middleToSource ▸ sourceToMiddle value) =
        (fun {_} (value : Var source _) => value))
    (middleToTargetIdentity :
      (fun {sig} (value : Var middle sig) =>
        targetToMiddle ▸ middleToTarget value) =
        (fun {_} (value : Var middle _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToMiddle.trans middleToSource ▸
        middleToTarget (sourceToMiddle value)) =
      (fun {_} (value : Var source _) => value) := by
  cases middleToSource
  cases targetToMiddle
  have sourceExact :
      (sourceToMiddle : WireRenaming source source) =
        ((fun {_} (value : Var source _) => value) :
          WireRenaming source source) :=
    sourceToMiddleIdentity
  have targetExact :
      (middleToTarget : WireRenaming source source) =
        ((fun {_} (value : Var source _) => value) :
          WireRenaming source source) :=
    middleToTargetIdentity
  funext sig value
  have sourcePoint :=
    congrFun (congrFun sourceExact sig) value
  have targetPoint :=
    congrFun (congrFun targetExact sig) value
  simpa using
    (congrArg (fun mapped => middleToTarget mapped) sourcePoint).trans
      targetPoint

private noncomputable def transportComposableSemanticZipperTargetHole
    {definitions : List (List Sig)}
    {sourceHole leftHole rightHole : List Sig}
    (same : leftHole = rightHole)
    (source : DiagramContext definitions sourceHole [])
    (target : DiagramContext definitions rightHole [])
    (rho : WireRenaming sourceHole rightHole)
    (outerMap :
      ∀ pre : PreModel.{u}, Env pre [] → Env pre [])
    (zipper :
      DiagramContext.ComposableSemanticZipper.{u} source target outerMap
        (fun (_pre : PreModel.{u}) env => Env.comp env rho)) :
    DiagramContext.ComposableSemanticZipper.{u} source (same.symm ▸ target)
      outerMap
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (transportRenaming rfl same rho)) := by
  cases same
  exact zipper

private def transportEnvironment
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs) :
    Env pre rightContext.sigs :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ env

private theorem transportEnvironment_apply
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs)
    (value : Var context.sigs sig) :
    transportEnvironment same context rightContext contextExact env sig
        (transportVariable same context rightContext contextExact value) =
      env sig value := by
  cases same
  cases contextExact
  rfl

private theorem transportEnvironment_denote
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs)
    (variables : Vars context.sigs args) :
    Vars.denote
        (transportEnvironment same context rightContext contextExact env)
        (transportVariables same context rightContext contextExact variables) =
      Vars.denote env variables := by
  cases same
  cases contextExact
  rfl

private def untransportRegion
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (body : Region definitions rightContext.sigs) :
    Region definitions context.sigs :=
  transport_context_sigs same context ▸
    congrArg ConcreteElaboration.WireContext.sigs contextExact.symm ▸ body

private theorem untransportRegion_denotes
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (body : Region definitions rightContext.sigs) :
    denoteRegion pre definitionEnv env
        (untransportRegion same context rightContext contextExact body) ↔
      denoteRegion pre definitionEnv
        (transportEnvironment same context rightContext contextExact env)
        body := by
  cases same
  cases contextExact
  rfl

private theorem denoteRegion_transport
    {left right : List Sig}
    (same : left = right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre left)
    (body : Region definitions left) :
    denoteRegion pre definitionEnv env body ↔
      denoteRegion pre definitionEnv
        (same ▸ env) (same ▸ body) := by
  cases same
  rfl

private theorem cast_region_trans
    {left middle right : List Sig}
    (first : left = middle)
    (second : middle = right)
    (body : Region definitions left) :
    (first.trans second) ▸ body =
      second ▸ first ▸ body := by
  cases first
  cases second
  rfl

private theorem cast_region_eq
    {left right : List Sig}
    (same : left = right)
    (body : Region definitions left) :
    same ▸ body =
      cast (congrArg (Region definitions) same) body := by
  cases same
  rfl

private theorem cast_region_heq
    {left right : List Sig}
    (same : left = right)
    (body : Region definitions left) :
    HEq (same ▸ body) body := by
  cases same
  rfl

private theorem cast_env_apply
    {left right : List Sig}
    (same : left = right)
    (env : Env pre left)
    {sig : Sig}
    (value : Var left sig) :
    (same ▸ env) sig (same ▸ value) = env sig value := by
  cases same
  rfl

private theorem transportVariables_origins
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins right rightContext
        (transportVariables same context rightContext contextExact variables) =
      (ConcreteElaboration.variableOrigins left context variables).map
        fun wire =>
          Fin.cast (congrArg ConcreteDiagram.wireCount same) wire := by
  cases same
  cases contextExact
  change
    ConcreteElaboration.variableOrigins left context
        (transportVariables rfl context context rfl variables) =
      (ConcreteElaboration.variableOrigins left context variables).map
        (fun wire => Fin.cast rfl wire)
  rw [show transportVariables rfl context context rfl variables = variables
    by rfl]
  have castIdentity :
      (fun wire : left.WireId => Fin.cast rfl wire) = id := by
    funext wire
    rfl
  rw [castIdentity, List.map_id]

private def RelationJoinStep.baseRenamedVariables
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {args : List Sig}
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (variables : Vars context.sigs args) :
    Vars baseVisible.sigs args :=
  transportVariables step.base_generated.symm
    (SingletonRemovalSemantics.targetContext step.prior
      step.priorApplication context)
    baseVisible visibleExact
    (Vars.rename
        (SingletonRemovalSemantics.contextRenaming step.prior
          step.priorApplication context)
        variables)

private def RelationJoinStep.baseRenamedVariable
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (value : Var context.sigs sig) :
    Var baseVisible.sigs sig :=
  transportVariable step.base_generated.symm
    (SingletonRemovalSemantics.targetContext step.prior
      step.priorApplication context)
    baseVisible visibleExact
    (SingletonRemovalSemantics.contextRenaming step.prior
      step.priorApplication context value)

private theorem RelationJoinStep.baseRenamedVariables_origins
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {args : List Sig}
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins step.base.val baseVisible
        (baseRenamedVariables step context baseVisible visibleExact variables) =
      (ConcreteElaboration.variableOrigins step.prior.val context variables).map
        fun wire =>
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication wire) := by
  rw [baseRenamedVariables, transportVariables_origins]
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.rename, ConcreteElaboration.variableOrigins,
        List.map_cons, List.cons.injEq]
      constructor
      · apply congrArg
          (Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm)
        exact
          SingletonRemovalSemantics.contextRenaming_action step.prior
            step.priorApplication context head
      · exact induction

private theorem siteCompilation_visible_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.visible.ids.Nodup := by
  obtain ⟨scopeCompiled, outer, _fuel, _relative, _relativeVisible,
      _inner, scopeVisible, _rootInner, above, _generated, _relativeBody,
      _relativeContext, _scopeBody, _rootBody, _replacementBody, _cutDepth⟩ :=
    compiled.factorAt_relative_origin site
      (ConcreteDiagram.encloses_refl base.val site)
  have same : scopeCompiled = compiled :=
    SiteCompilation.unique scopeCompiled compiled
  subst scopeCompiled
  rw [scopeVisible]
  exact
    ConcreteElaboration.extend_nodup definitions base.val base.property
      outer site above

private def formalVariables :
    (formals : List Sig) →
      {parameters : List Sig} →
      Vars context (formals ++ parameters) →
      Vars context formals
  | [], _, _ => .nil
  | _ :: rest, _, .cons head tail =>
      .cons head (formalVariables rest tail)

private theorem variableOrigins_eq_map_entries
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins diagram context variables =
      variables.entries.map fun packed =>
        match packed with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin diagram context.ids value := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp only [ConcreteElaboration.variableOrigins, Vars.entries,
        List.map_cons, induction]

private theorem variableOrigins_cast
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {left right : List Sig}
    (same : left = right)
    (variables : Vars context.sigs left) :
    ConcreteElaboration.variableOrigins diagram context (same ▸ variables) =
      ConcreteElaboration.variableOrigins diagram context variables := by
  cases same
  rfl

private theorem variableOrigins_length
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    (ConcreteElaboration.variableOrigins diagram context variables).length =
      args.length := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp only [ConcreteElaboration.variableOrigins, List.length_cons,
        induction]

private theorem List.get_cast_of_eq
    {left right : List α}
    (same : left = right)
    (position : Fin left.length) :
    left.get position =
      right.get (Fin.cast (congrArg List.length same) position) := by
  cases same
  rfl

private theorem variableOrigins_formalVariables
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context.sigs (formals ++ parameters)) :
    ConcreteElaboration.variableOrigins diagram context
        (formalVariables formals variables) =
      (ConcreteElaboration.variableOrigins diagram context variables).take
        formals.length := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons head tail =>
          change
            ConcreteElaboration.WireContext.origin diagram context.ids head ::
                ConcreteElaboration.variableOrigins diagram context
                  (formalVariables rest tail) =
              List.take (rest.length + 1)
                (ConcreteElaboration.WireContext.origin diagram context.ids head ::
                  ConcreteElaboration.variableOrigins diagram context tail)
          rw [show rest.length + 1 = Nat.succ rest.length by omega,
            List.take_succ_cons, induction tail]

private theorem variables_eq_of_origins
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.ids.Nodup)
    (left right : Vars context.sigs args)
    (same :
      ConcreteElaboration.variableOrigins diagram context left =
        ConcreteElaboration.variableOrigins diagram context right) :
    left = right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [ConcreteElaboration.variableOrigins, List.cons.injEq]
            at same
          have headExact :=
            InsertionCompilation.NaturalityInternal.origin_injective
              diagram context.ids nodup same.1
          subst rightHead
          exact congrArg (Vars.cons leftHead) (induction rightTail same.2)

private theorem insertion_target_position_origins
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ConcreteElaboration.variableOrigins base.val compiled.site.frame.visible
        compiled.intrinsicAttachment.positions =
      List.ofFn attachment.target := by
  rw [variableOrigins_eq_map_entries]
  apply List.ext_get
  · simp only [List.length_map, ExtractedBoundaryCompiler.entries_length,
      List.length_ofFn, checkedBoundarySigs, List.length_map]
  · intro position leftBound rightBound
    let boundaryPosition : Fin fragment.val.boundary.length :=
      ⟨position, by simpa using rightBound⟩
    have exactOrigin := compiled.targetPackedAt_origin boundaryPosition
    simpa only [InsertionCompilation.intrinsicAttachment,
      intrinsicAttachmentFromPositions, SpliceAttachment.positions,
      InsertionCompilation.targetPackedAt, VisualProof.targetPackedAt,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn] using exactOrigin

private theorem RelationJoinStep.formalVariables_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments) :
    formalVariables step.relationArgs
        (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
      baseRenamedVariables step context compiled.site.frame.visible
        visibleExact arguments := by
  apply
    variables_eq_of_origins step.base.val compiled.site.frame.visible
      (siteCompilation_visible_nodup compiled.site)
  rw [variableOrigins_formalVariables,
    variableOrigins_cast,
    insertion_target_position_origins compiled,
    RelationJoinStep.baseRenamedVariables_origins,
    argumentOrigins, step.priorArgumentsExact]
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  apply List.ext_get
  · simp only [List.length_take, List.length_ofFn, List.length_map]
    rw [boundaryLength, Nat.min_eq_left (by omega), argumentLength]
  · intro position leftBound rightBound
    have positionSource : position < step.sourceArguments.length := by
      simpa only [List.length_map] using rightBound
    let sourcePosition : Fin step.sourceArguments.length :=
      ⟨position, positionSource⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨position, by
        rw [boundaryLength, ← argumentLength]
        omega⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceArguments.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceArguments.get sourcePosition := by
          have positionAppend :
              position <
                (step.sourceArguments ++ step.sourceParameters).length := by
            simp only [List.length_append]
            omega
          change
            (step.sourceArguments ++
                step.sourceParameters)[position]'positionAppend =
              step.sourceArguments[position]'positionSource
          exact List.getElem_append_left positionSource
    have rawBridge :=
      SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
        step (step.sourceArguments.get sourcePosition)
    have targetFormal :
        step.attachment.target boundaryPosition =
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication
              (step.priorWireImage
                (step.sourceArguments.get sourcePosition))) := by
      exact
        (targetExact.trans
          (congrArg step.baseWireImage attachmentGet)).trans rawBridge.symm
    simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn,
      List.getElem_map, Function.comp_apply] using targetFormal

private def parameterVariables :
    (formals : List Sig) →
      {parameters : List Sig} →
      Vars context (formals ++ parameters) →
      Vars context parameters
  | [], _, variables => variables
  | _ :: rest, _, .cons _ tail =>
      parameterVariables rest tail

private theorem variableOrigins_parameterVariables
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context.sigs (formals ++ parameters)) :
    ConcreteElaboration.variableOrigins diagram context
        (parameterVariables formals variables) =
      (ConcreteElaboration.variableOrigins diagram context variables).drop
        formals.length := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons _ tail =>
          simpa [parameterVariables,
            ConcreteElaboration.variableOrigins] using induction tail

/--
The accepted boundary suffix is exactly the ordered source-parameter image in
the same canonical base visible context as the formal prefix.
-/
private theorem RelationJoinStep.parameterVariables_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments)
    (parameters : Vars context.sigs parameterSigs)
    (parameterOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context parameters =
        step.sourceParameters.map step.priorWireImage) :
    parameterVariables step.relationArgs
        (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
      baseRenamedVariables step context compiled.site.frame.visible
        visibleExact parameters := by
  apply
    variables_eq_of_origins step.base.val compiled.site.frame.visible
      (siteCompilation_visible_nodup compiled.site)
  rw [variableOrigins_parameterVariables, variableOrigins_cast,
    insertion_target_position_origins compiled,
    RelationJoinStep.baseRenamedVariables_origins, parameterOrigins]
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have parameterLength :
      step.sourceParameters.length = parameterSigs.length := by
    have sameLength := congrArg List.length parameterOrigins
    rw [List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  apply List.ext_get
  · simp only [List.length_drop, List.length_ofFn, List.length_map]
    rw [boundaryLength, parameterLength]
    omega
  · intro position leftBound rightBound
    have parameterPosition : position < step.sourceParameters.length := by
      simpa only [List.length_map] using rightBound
    let sourcePosition : Fin step.sourceParameters.length :=
      ⟨position, parameterPosition⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨step.relationArgs.length + position, by
        rw [boundaryLength]
        omega⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceParameters.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceParameters.get sourcePosition := by
          let sourceAppendPosition :
              Fin (step.sourceArguments ++
                step.sourceParameters).length :=
            ⟨step.sourceArguments.length + position, by
              simp only [List.length_append]
              omega⟩
          have indexExact :
              Fin.cast
                  (congrArg List.length step.sourceAttachmentsExact)
                  (Fin.cast step.sourceAttachmentArity.symm
                    boundaryPosition) =
                sourceAppendPosition := by
            apply Fin.ext
            change
              step.relationArgs.length + position =
                step.sourceArguments.length + position
            omega
          rw [indexExact]
          change
            (step.sourceArguments ++ step.sourceParameters).get
                sourceAppendPosition =
              step.sourceParameters.get sourcePosition
          simpa using
            (List.getElem_append_right
              (as := step.sourceArguments) (bs := step.sourceParameters)
              (i := step.sourceArguments.length + position) (by omega))
    have rawBridge :=
      SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
        step (step.sourceParameters.get sourcePosition)
    have targetParameter :
        step.attachment.target boundaryPosition =
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication
              (step.priorWireImage
                (step.sourceParameters.get sourcePosition))) := by
      exact
        (targetExact.trans
          (congrArg step.baseWireImage attachmentGet)).trans rawBridge.symm
    simpa only [List.get_eq_getElem, List.getElem_drop, List.getElem_ofFn,
      List.getElem_map, Function.comp_apply] using targetParameter

private theorem RelationJoinStep.priorParameterSignatures
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments) :
    step.sourceParameters.map
        (fun wire =>
          (step.prior.val.wires (step.priorWireImage wire)).sig) =
      parameterSigs := by
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  have parameterLength :
      step.sourceParameters.length = parameterSigs.length := by
    have attachmentsLength :=
      congrArg List.length step.sourceAttachmentsExact
    rw [List.length_append, step.sourceAttachmentArity,
      boundaryLength, argumentLength] at attachmentsLength
    omega
  apply List.ext_get
  · simpa only [List.length_map] using parameterLength
  · intro position leftBound rightBound
    let sourcePosition : Fin step.sourceParameters.length :=
      ⟨position, by simpa only [List.length_map] using leftBound⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨step.relationArgs.length + position, by
        rw [boundaryLength]
        exact Nat.add_lt_add_left rightBound step.relationArgs.length⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceParameters.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceParameters.get sourcePosition := by
          let appendPosition :
              Fin (step.sourceArguments ++ step.sourceParameters).length :=
            ⟨step.sourceArguments.length + position, by
              simp only [List.length_append]
              omega⟩
          have indexExact :
              Fin.cast
                  (congrArg List.length step.sourceAttachmentsExact)
                  (Fin.cast step.sourceAttachmentArity.symm
                    boundaryPosition) =
                appendPosition := by
            apply Fin.ext
            change
              step.relationArgs.length + position =
                step.sourceArguments.length + position
            omega
          rw [indexExact]
          change
            (step.sourceArguments ++ step.sourceParameters).get
                appendPosition =
              step.sourceParameters.get sourcePosition
          simpa using
            (List.getElem_append_right
              (as := step.sourceArguments) (bs := step.sourceParameters)
              (i := step.sourceArguments.length + position) (by omega))
    have signatureAtTarget := step.attachment.signature boundaryPosition
    rw [targetExact, attachmentGet, ← step.baseWire_signature] at signatureAtTarget
    have signatureBoundary :
        (step.prior.val.wires
            (step.priorWireImage
              (step.sourceParameters.get sourcePosition))).sig =
          (checkedBoundarySigs content).get
            (Fin.cast
              (by simpa only [checkedBoundarySigs, List.length_map])
              boundaryPosition) := by
      simpa only [checkedBoundarySigs, List.get_eq_getElem,
        List.getElem_map] using signatureAtTarget
    have boundaryAt :=
      List.get_cast_of_eq boundaryExact
        (Fin.cast
          (by simpa only [checkedBoundarySigs, List.length_map])
          boundaryPosition)
    let suffixPosition : Fin parameterSigs.length := ⟨position, rightBound⟩
    let appendPosition :
        Fin (step.relationArgs ++ parameterSigs).length :=
      ⟨step.relationArgs.length + position, by
        simp only [List.length_append]
        omega⟩
    have boundaryIndexExact :
        Fin.cast (congrArg List.length boundaryExact)
            (Fin.cast
              (by simpa only [checkedBoundarySigs, List.length_map])
              boundaryPosition) =
          appendPosition := by
      apply Fin.ext
      rfl
    have boundarySuffix :
        (step.relationArgs ++ parameterSigs).get
            (Fin.cast (congrArg List.length boundaryExact)
              (Fin.cast
                (by simpa only [checkedBoundarySigs, List.length_map])
                boundaryPosition)) =
          parameterSigs.get suffixPosition := by
      rw [boundaryIndexExact]
      change
        (step.relationArgs ++ parameterSigs).get appendPosition =
          parameterSigs.get suffixPosition
      simpa using
        (List.getElem_append_right
          (as := step.relationArgs) (bs := parameterSigs)
          (i := step.relationArgs.length + position) (by omega))
    simpa only [List.get_eq_getElem, List.getElem_map, sourcePosition,
      suffixPosition] using
        signatureBoundary.trans (boundaryAt.trans boundarySuffix)

private theorem checkedEncloses_trans
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
      diagram.climb (innerSteps.val + outerSteps.val) inner =
        some outer := by
    rw [IotaJoinSemantics.climb_add, innerClimb]
    exact outerClimb
  have bounded :=
    ConcreteElaboration.successfulClimb_le_count definitions diagram
      wellFormed (innerSteps.val + outerSteps.val) inner outer combined
  exact
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
      ⟨⟨innerSteps.val + outerSteps.val, by omega⟩, combined⟩

private theorem RelationJoinStep.priorParameterVariables
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterScopes :
      ∀ position : Fin step.sourceParameters.length,
        source.val.Encloses
          (source.val.wires
            (step.sourceParameters.get position)).scope
          (source.val.wires dying).scope)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (frame : RegionFrame definitions step.prior.val context)
    (frameVisible : frame.visible = step.priorSite.frame.visible)
    (arguments : Vars frame.visible.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val frame.visible
          arguments =
        step.priorArguments) :
    ∃ parameters : Vars frame.visible.sigs parameterSigs,
      ConcreteElaboration.variableOrigins step.prior.val frame.visible
          parameters =
        step.sourceParameters.map step.priorWireImage := by
  have signatures :=
    RelationJoinStep.priorParameterSignatures step boundaryExact frame.visible
      arguments argumentOrigins
  let wires := step.sourceParameters.map step.priorWireImage
  have members :
      ∀ wire, wire ∈ wires → wire ∈ frame.visible.ids := by
    intro wire member
    obtain ⟨sourceWire, sourceMember, rfl⟩ := List.mem_map.mp member
    have sourcePosition :=
      List.get_of_mem sourceMember
    obtain ⟨position, rfl⟩ := sourcePosition
    have parameterAboveDying :=
      RelationJoinStep.priorParameterScopes step parameterScopes position
    have dyingAboveSite :
        step.prior.val.Encloses
          (step.prior.val.wires (step.priorWireImage dying)).scope
          (step.priorRegionImage step.sourceRegion) := by
      rw [step.priorWireScopeExact]
      exact step.prior_dying_scope_encloses_site
    have parameterAboveSite :=
      checkedEncloses_trans definitions step.prior.val step.prior.property
        parameterAboveDying dyingAboveSite
    rw [frameVisible]
    exact
      step.priorSite.visible_of_encloses
        (step.priorWireImage (step.sourceParameters.get position))
        parameterAboveSite
  let native := variablesOfMembers step.prior.val frame.visible wires members
  let nativeSigs :=
    wires.map fun wire => (step.prior.val.wires wire).sig
  have nativeSigsExact : nativeSigs = parameterSigs := by
    unfold nativeSigs wires
    rw [List.map_map]
    exact signatures
  refine ⟨nativeSigsExact ▸ native, ?_⟩
  rw [variableOrigins_cast]
  exact variablesOfMembers_origins step.prior.val frame.visible wires members

private theorem denote_split_variables
    (env : Env pre context)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context (formals ++ parameters)) :
    Vars.denote env variables =
      WireQuantifierSemantics.appendArgs
        (Vars.denote env (formalVariables formals variables))
        (Vars.denote env (parameterVariables formals variables)) := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons head tail =>
          simp only [Vars.denote_cons, formalVariables, parameterVariables,
            WireQuantifierSemantics.appendArgs]
          exact congrArg (fun value => (env _ head, value)) (induction tail)

private theorem boundary_values_from_formals
    (env : Env pre context)
    {boundary formals parameters : List Sig}
    (boundaryExact : boundary = formals ++ parameters)
    (positions : Vars context boundary)
    (arguments : Vars context formals)
    (formalExact :
      formalVariables formals (boundaryExact ▸ positions) = arguments) :
    Vars.denote env positions =
      boundaryExact.symm ▸
        WireQuantifierSemantics.appendArgs
          (Vars.denote env arguments)
          (Vars.denote env
            (parameterVariables formals (boundaryExact ▸ positions))) := by
  cases boundaryExact
  rw [denote_split_variables, formalExact]

/--
The canonical content relation replaces one compiled application exactly when
the accepted intrinsic boundary tuple is its ordered formal tuple followed by
the fixed parameter tuple.
-/
private theorem application_denotes_intrinsic
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs context : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (env : Env model.toPreModel context)
    (head : Var context (.rel args))
    (arguments : Vars context args)
    (attachment :
      SpliceAttachment contentCompiled.openDiagram context)
    (headValue :
      env (.rel args) head =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (boundaryValues :
      Vars.denote env attachment.positions =
        boundaryExact.symm ▸
          WireQuantifierSemantics.appendArgs
            (Vars.denote env arguments) parameterValues) :
    denoteItem model.toPreModel definitionEnv env (.atom head arguments) ↔
      denoteRegion model.toPreModel definitionEnv env
        (intrinsicSplice contentCompiled.openDiagram attachment) := by
  rw [denote_intrinsicSplice]
  simp only [denoteItem, headValue]
  rw [WireQuantifierSemantics.contentRelation_applies]
  apply iff_of_eq
  apply congrArg
    (denoteOpen model.toPreModel definitionEnv contentCompiled.openDiagram)
  exact boundaryValues.symm

/--
The accepted intrinsic splice is exactly one compiled application once the
formal prefix is fixed and the remaining ordered positions carry the fixed
parameter tuple.
-/
private theorem compiledApplication_denotes_intrinsic
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {attachment : ConcreteSpliceAttachment base site content}
    (compiled : InsertionCompilation contentCompiled attachment)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (env : Env model.toPreModel compiled.site.frame.visible.sigs)
    (head : Var compiled.site.frame.visible.sigs (.rel args))
    (arguments : Vars compiled.site.frame.visible.sigs args)
    (formalExact :
      formalVariables args
          (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
        arguments)
    (headValue :
      env (.rel args) head =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      Vars.denote env
          (parameterVariables args
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    denoteItem model.toPreModel definitionEnv env (.atom head arguments) ↔
      denoteRegion model.toPreModel definitionEnv env
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment) := by
  apply
    application_denotes_intrinsic model definitionEnv contentCompiled
      boundaryExact parameterValues env head arguments
      compiled.intrinsicAttachment headValue
  rw [boundary_values_from_formals env boundaryExact
    compiled.intrinsicAttachment.positions arguments formalExact,
    parameterExact]

/--
Transport the compiler-owned application law back to the raw singleton-erasure
visible context. This is the exact `LocalReplacementAt` payload used by both
scope-geometry branches.
-/
private theorem RelationJoinStep.erasureLocalLaw
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
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (head : Var context.sigs (.rel step.relationArgs))
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments)
    (rawEnv :
      Env model.toPreModel
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication context).sigs)
    (headValue :
      transportEnvironment step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context)
          compiled.site.frame.visible visibleExact rawEnv
          (.rel step.relationArgs)
          (baseRenamedVariable step context compiled.site.frame.visible
            visibleExact head) =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      Vars.denote
          (transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication context)
            compiled.site.frame.visible visibleExact rawEnv)
          (parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    denoteRegion model.toPreModel definitionEnv rawEnv
        (untransportRegion step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context)
          compiled.site.frame.visible visibleExact
          (intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment)) ↔
      denoteItem model.toPreModel definitionEnv
        (Env.comp rawEnv
          (SingletonRemovalSemantics.contextRenaming step.prior
            step.priorApplication context))
        (.atom head arguments) := by
  let baseEnv :=
    transportEnvironment step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication context)
      compiled.site.frame.visible visibleExact rawEnv
  have formalExact :=
    RelationJoinStep.formalVariables_exact step contentCompiled compiled
      boundaryExact context visibleExact arguments argumentOrigins
  have intrinsicLaw :=
    compiledApplication_denotes_intrinsic model definitionEnv contentCompiled
      compiled boundaryExact parameterValues baseEnv
      (baseRenamedVariable step context compiled.site.frame.visible
        visibleExact head)
      (baseRenamedVariables step context compiled.site.frame.visible
        visibleExact arguments)
      formalExact headValue parameterExact
  rw [untransportRegion_denotes]
  constructor
  · intro intrinsicHolds
    have atomHolds := intrinsicLaw.mpr intrinsicHolds
    simpa [baseEnv, denoteItem,
      RelationJoinStep.baseRenamedVariable,
      RelationJoinStep.baseRenamedVariables,
      transportEnvironment_apply,
      transportEnvironment_denote, Vars.denote_rename] using atomHolds
  · intro atomHolds
    apply intrinsicLaw.mp
    simpa [baseEnv, denoteItem,
      RelationJoinStep.baseRenamedVariable,
      RelationJoinStep.baseRenamedVariables,
      transportEnvironment_apply,
      transportEnvironment_denote, Vars.denote_rename] using atomHolds

/--
Cast the canonical erasure law to the actual compiler-generated target frame.
The replacement remains the transported accepted intrinsic splice.
-/
private theorem RelationJoinStep.erasureLocalReplacementAt
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
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    {sourceOuter : ConcreteElaboration.WireContext step.prior.val}
    (sourceFrame : RegionFrame definitions step.prior.val sourceOuter)
    {fuel : Nat}
    (targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (provenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel sourceOuter
        (step.priorRegionImage (source.val.wires dying).scope)
        sourceFrame targetFrame)
    (baseVisibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible =
        compiled.site.frame.visible)
    (head : Var sourceFrame.visible.sigs (.rel step.relationArgs))
    (arguments : Vars sourceFrame.visible.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val
          sourceFrame.visible arguments =
        step.priorArguments)
    (targetEnv : Env model.toPreModel targetFrame.visible.sigs)
    (headValue :
      let canonicalEnv :=
        congrArg ConcreteElaboration.WireContext.sigs
            provenance.targetVisible ▸ targetEnv
      transportEnvironment step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible)
          compiled.site.frame.visible baseVisibleExact canonicalEnv
          (.rel step.relationArgs)
          (baseRenamedVariable step sourceFrame.visible
            compiled.site.frame.visible baseVisibleExact head) =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      let canonicalEnv :=
        congrArg ConcreteElaboration.WireContext.sigs
            provenance.targetVisible ▸ targetEnv
      Vars.denote
          (transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible)
            compiled.site.frame.visible baseVisibleExact canonicalEnv)
          (parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    let canonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let replacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          provenance.targetVisible.symm ▸ canonicalReplacement
    SingletonRemovalSemantics.LocalReplacementAt step.prior
      step.priorApplication sourceFrame.visible targetFrame.visible
      provenance.targetVisible replacement (.atom head arguments)
      model.toPreModel definitionEnv targetEnv := by
  dsimp only
  apply
    SingletonRemovalSemantics.LocalReplacementAt.cast step.prior
      step.priorApplication rfl provenance.targetVisible.symm rfl
      provenance.targetVisible
      (untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment))
      (.atom head arguments) model.toPreModel definitionEnv targetEnv
  exact
    RelationJoinStep.erasureLocalLaw step contentCompiled compiled model
      definitionEnv boundaryExact parameterValues sourceFrame.visible
      baseVisibleExact head arguments argumentOrigins
      (congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible ▸ targetEnv)
      headValue parameterExact

/--
At a strict descendant application, compose the accepted insertion's fixed
pre-binder direction with the enclosing singleton-erasure replacement receipt.
The `HEq` premise records only the checked/raw representation transport between
the two receipts' fixed environments.
-/
private theorem RelationJoinStep.strictDescendantBodyDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions)
    {outer : ConcreteElaboration.WireContext step.prior.val}
    {fuel : Nat}
    {sourceFrame : RegionFrame definitions step.prior.val outer}
    {relativeRaw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication outer)}
    (provenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel outer
        (step.priorRegionImage (source.val.wires dying).scope)
        sourceFrame relativeRaw)
    {siteOuter : ConcreteElaboration.WireContext step.base.val}
    {generatedFrame :
      RegionFrame definitions step.attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext step.attachment
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer relativeRaw provenance.targetGenerated).outer)}
    (pairedErasure :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer sourceFrame)
    (pairedInsertion :
      InsertionCompilation.PairedGeneratedFrame compiled
        (step.baseRegionImage (source.val.wires dying).scope)
        fuel
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel outer relativeRaw provenance.targetGenerated).outer
        siteOuter
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel outer relativeRaw provenance.targetGenerated).frame
        generatedFrame)
    (strictDescendant :
      (source.val.wires dying).scope ≠ step.sourceRegion)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions step.prior.val
          sourceFrame.visible [step.priorApplication] =
        some (.cons removedItem .nil)) :
    let baseVisibleExact :=
      RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
        compiled relativeRaw provenance pairedInsertion
    let canonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let replacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          provenance.targetVisible.symm ▸ canonicalReplacement
    ∃ erasureInner :
        SingletonRemovalSemantics.PairedInnerFrame step.prior
          step.priorApplication
          (step.priorRegionImage (source.val.wires dying).scope)
          outer sourceFrame relativeRaw,
      ∃ insertionInner :
          InsertionCompilation.PairedInnerFrame compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer relativeRaw provenance.targetGenerated).outer
            siteOuter
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer relativeRaw provenance.targetGenerated).frame
            generatedFrame,
        ∀ (generatedFixed :
            Env model.toPreModel
              ((InsertionCompilation.NaturalityInternal.hostContext
                    step.attachment
                    (checkedBaseFrameReceipt step
                      (step.priorRegionImage step.sourceRegion)
                      (step.priorRegionImage
                        (source.val.wires dying).scope)
                      fuel outer relativeRaw
                      provenance.targetGenerated).outer).extend
                (step.attachment.hostRegion
                  (step.baseRegionImage
                    (source.val.wires dying).scope))).sigs)
          (erasedFixed :
            Env model.toPreModel
              ((SingletonRemovalSemantics.targetContext step.prior
                    step.priorApplication outer).extend
                (SingletonRemovalSemantics.targetRegion step.prior
                  step.priorApplication
                  (step.priorRegionImage
                    (source.val.wires dying).scope))).sigs),
          HEq
              (Env.comp generatedFixed
                (InsertionCompilation.enclosingRenaming
                  compiled
                  (step.baseRegionImage
                    (source.val.wires dying).scope)
                  (checkedBaseFrameReceipt step
                    (step.priorRegionImage step.sourceRegion)
                    (step.priorRegionImage
                      (source.val.wires dying).scope)
                    fuel outer relativeRaw
                    provenance.targetGenerated).outer))
              erasedFixed →
            (∀ descendant : Env model.toPreModel relativeRaw.visible.sigs,
              DiagramContext.PreservesOuter erasureInner.targetInner
                  erasedFixed descendant →
                SingletonRemovalSemantics.LocalReplacementAt step.prior
                  step.priorApplication sourceFrame.visible
                  relativeRaw.visible provenance.targetVisible replacement
                  removedItem model.toPreModel definitionEnv descendant) →
              denoteRegion model.toPreModel definitionEnv generatedFixed
                  (insertionInner.targetInner.fill
                    generatedFrame.siteBody) →
                denoteRegion model.toPreModel definitionEnv
                  (Env.comp erasedFixed
                    (SingletonRemovalSemantics.extendedContextRenaming
                      step.prior step.priorApplication outer
                      (step.priorRegionImage
                        (source.val.wires dying).scope)))
                  (erasureInner.sourceInner.fill sourceFrame.siteBody) := by
  dsimp only
  let baseVisibleExact :=
    RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
      compiled relativeRaw provenance pairedInsertion
  let canonicalReplacement :=
    untransportRegion step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceFrame.visible)
      compiled.site.frame.visible baseVisibleExact
      (intrinsicSplice contentCompiled.openDiagram
        compiled.intrinsicAttachment)
  let replacement :=
    congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible.symm ▸ canonicalReplacement
  have insertionNotSite :
      step.baseRegionImage (source.val.wires dying).scope ≠ step.site := by
    intro same
    apply strictDescendant
    apply RelationJoinStep.baseRegionImage_injective step
    exact same.trans step.siteExact
  obtain ⟨insertionInner, insertionLaw⟩ :=
    InsertionCompilation.PairedGeneratedFrame.strictAncestorInsertionDenotation
      pairedInsertion insertionNotSite model.toPreModel definitionEnv
  have pairedAtNode :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.prior.val.nodes step.priorApplication).region
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer sourceFrame := by
    simpa [step.priorNodeExact] using pairedErasure
  obtain ⟨erasedFrame, erasedGenerated, erasedVisible,
      erasedReplacement⟩ :=
    SingletonRemovalSemantics.PairedGeneratedFrame.enclosing_replacement_receipt
      step.prior step.priorApplication
      (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer sourceFrame pairedAtNode removedItem removedCompiled
      model.toPreModel definitionEnv
  have erasedFrameExact : erasedFrame = relativeRaw := by
    apply Option.some.inj
    exact erasedGenerated.symm.trans (by
      simpa [step.priorNodeExact] using provenance.targetGenerated)
  subst erasedFrame
  have erasedVisibleExact :
      erasedVisible = provenance.targetVisible := Subsingleton.elim _ _
  rw [erasedVisibleExact] at erasedReplacement
  obtain ⟨erasureInner, erasureLaw⟩ :=
    erasedReplacement replacement
  refine ⟨erasureInner, insertionInner, ?_⟩
  intro generatedFixed erasedFixed environmentsExact localLaw generatedHolds
  have checkedHolds :=
    (insertionLaw generatedFixed).mp generatedHolds
  have pairedErasureCopy := pairedErasure
  rcases pairedErasureCopy with
    ⟨pairedRaw, sourceAbove, _sourceGenerated, pairedProvenance⟩
  have pairedRawExact : pairedRaw = relativeRaw := by
    apply Option.some.inj
    exact pairedProvenance.targetGenerated.symm.trans
      provenance.targetGenerated
  subst pairedRaw
  have rawAbove :=
    SingletonRemovalSemantics.RelationJoinStep.rawTargetContext_above step
      outer (step.priorRegionImage (source.val.wires dying).scope)
      sourceAbove
  let checkedInner :=
    checkedBaseInnerFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer relativeRaw provenance.targetGenerated rawAbove
      erasureInner.targetInner erasureInner.targetDecomposition
  let baseReceipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer relativeRaw provenance.targetGenerated
  have checkedExact : checkedInner.toFrameReceipt = baseReceipt := by
    exact
      checkedBaseInnerFrameReceipt_toFrame step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer relativeRaw provenance.targetGenerated rawAbove
        erasureInner.targetInner erasureInner.targetDecomposition
  have baseRegionExact :
      baseReceipt.region =
        step.baseRegionImage (source.val.wires dying).scope := by
    exact
      (checkedBaseFrameReceipt_region step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer relativeRaw provenance.targetGenerated).trans
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetRegion_eq_baseRegionImage
            step (source.val.wires dying).scope)
  have alignGeneratedInner :
      ∀ (innerReceipt :
          GeneratedInnerFrameReceipt definitions step.base.val fuel)
        (frameReceipt :
          GeneratedFrameReceipt definitions step.base.val fuel)
        (same : innerReceipt.toFrameReceipt = frameReceipt)
        (region : step.base.val.RegionId)
        (regionExact : frameReceipt.region = region)
        (targetFrame :
          RegionFrame definitions step.attachment.diagram
            (InsertionCompilation.NaturalityInternal.hostContext
              step.attachment frameReceipt.outer))
        (paired :
          InsertionCompilation.PairedInnerFrame compiled region
            frameReceipt.outer siteOuter frameReceipt.frame targetFrame),
        HEq innerReceipt.inner paired.sourceInner := by
    intro innerReceipt frameReceipt same region regionExact targetFrame paired
    subst frameReceipt
    subst region
    rw [
      generatedInner_eq_insertionSourceInner innerReceipt siteOuter paired]
    exact HEq.rfl
  have innerExact :
      HEq checkedInner.inner insertionInner.sourceInner :=
    alignGeneratedInner checkedInner baseReceipt checkedExact
      (step.baseRegionImage (source.val.wires dying).scope)
      baseRegionExact generatedFrame insertionInner
  apply (erasureLaw erasedFixed localLaw).mp
  have checkedContextExact :
      (baseReceipt.outer.extend
          (step.baseRegionImage (source.val.wires dying).scope)).sigs =
        (checkedInner.outer.extend checkedInner.region).sigs := by
    rw [← baseRegionExact, ← checkedExact]
    rfl
  have transportExtendedSigs :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (context : ConcreteElaboration.WireContext left)
        (region : left.RegionId),
        ((same ▸ context).extend (same ▸ region)).sigs =
          (context.extend region).sigs := by
    intro left right same context region
    cases same
    rfl
  have transportInnerOuter :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        (same ▸ receipt).outer = same ▸ receipt.outer := by
    intro left right same receipt
    cases same
    rfl
  have transportInnerRegion :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        (same ▸ receipt).region = same ▸ receipt.region := by
    intro left right same receipt
    cases same
    rfl
  have rawContextExact :
      (checkedInner.outer.extend checkedInner.region).sigs =
        ((SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication outer).extend
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage
              (source.val.wires dying).scope))).sigs := by
    unfold checkedInner checkedBaseInnerFrameReceipt
    rw [transportInnerOuter, transportInnerRegion]
    exact
      transportExtendedSigs step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication outer)
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication
          (step.priorRegionImage (source.val.wires dying).scope))
  have fixedSigsExact := checkedContextExact.trans rawContextExact
  let fixedEnvTypeExact :=
    congrArg (Env model.toPreModel) fixedSigsExact
  have fixedEnvironmentExact :
      cast fixedEnvTypeExact
          (Env.comp generatedFixed
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer)) =
        erasedFixed :=
    eq_of_heq
      ((cast_heq fixedEnvTypeExact
        (Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer))).trans environmentsExact)
  have transportFrameSiteBody :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedFrameReceipt definitions left fuel),
        HEq (same ▸ receipt).frame.siteBody receipt.frame.siteBody := by
    intro left right same receipt
    cases same
    exact HEq.rfl
  have sourceBodyExact :
      HEq baseReceipt.frame.siteBody relativeRaw.siteBody := by
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
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated }
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
            (insertionInner.siteVisible.trans
              insertionInner.sourceVisible.symm) ▸
          intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment)
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment) := by
    apply eqRec_heq
  have baseFrameVisibleExact :
      baseReceipt.frame.visible =
        step.base_generated.symm ▸ relativeRaw.visible := by
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
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated }
  have holeSigsExact :
      baseReceipt.frame.visible.sigs = relativeRaw.visible.sigs :=
    (congrArg ConcreteElaboration.WireContext.sigs
      baseFrameVisibleExact).trans
        (transport_context_sigs step.base_generated.symm
          relativeRaw.visible)
  let holeRegionTypeExact :=
    congrArg (Region definitions) holeSigsExact
  have sourceBodyCast :
      cast holeRegionTypeExact baseReceipt.frame.siteBody =
        relativeRaw.siteBody :=
    eq_of_heq
      ((cast_heq holeRegionTypeExact
        baseReceipt.frame.siteBody).trans sourceBodyExact)
  have insertedCast :
      cast holeRegionTypeExact
          (congrArg ConcreteElaboration.WireContext.sigs
              (insertionInner.siteVisible.trans
                insertionInner.sourceVisible.symm) ▸
            intrinsicSplice contentCompiled.openDiagram
              compiled.intrinsicAttachment) =
        replacement :=
    eq_of_heq
      ((cast_heq holeRegionTypeExact
        (congrArg ConcreteElaboration.WireContext.sigs
            (insertionInner.siteVisible.trans
              insertionInner.sourceVisible.symm) ▸
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
      cast holeRegionTypeExact insertionInner.replacement =
        relativeRaw.siteBody.conjoin replacement := by
    unfold InsertionCompilation.PairedInnerFrame.replacement
    rw [castConjoin holeSigsExact, sourceBodyCast, insertedCast]
  have transportInnerContext :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        HEq (same ▸ receipt).inner receipt.inner := by
    intro left right same receipt
    cases same
    exact HEq.rfl
  have checkedRawInnerExact :
      HEq checkedInner.inner erasureInner.targetInner := by
    unfold checkedInner checkedBaseInnerFrameReceipt
    exact
      transportInnerContext step.base_generated.symm
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
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated
          above := rawAbove
          inner := erasureInner.targetInner
          decomposition := erasureInner.targetDecomposition }
  have sourceRawInnerExact :
      HEq insertionInner.sourceInner erasureInner.targetInner :=
    innerExact.symm.trans checkedRawInnerExact
  let holeInnerTypeExact :=
    congrArg
      (fun hole =>
        DiagramContext definitions hole
          (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs)
      holeSigsExact
  let outerInnerTypeExact :=
    congrArg
      (DiagramContext definitions relativeRaw.visible.sigs)
      fixedSigsExact
  have innerCast :
      cast outerInnerTypeExact
          (cast holeInnerTypeExact insertionInner.sourceInner) =
        erasureInner.targetInner :=
    eq_of_heq
      ((cast_heq outerInnerTypeExact
        (cast holeInnerTypeExact insertionInner.sourceInner)).trans
        ((cast_heq holeInnerTypeExact
          insertionInner.sourceInner).trans sourceRawInnerExact))
  have castFill :
      ∀ {leftHole rightHole leftOuter rightOuter : List Sig}
        (holeExact : leftHole = rightHole)
        (outerExact : leftOuter = rightOuter)
        (context : DiagramContext definitions leftHole leftOuter)
        (body : Region definitions leftHole),
        cast (congrArg (Region definitions) outerExact)
            (context.fill body) =
          (cast
              (congrArg
                (DiagramContext definitions rightHole)
                outerExact)
              (cast
                (congrArg
                  (fun hole =>
                    DiagramContext definitions hole leftOuter)
                  holeExact)
                context)).fill
            (cast (congrArg (Region definitions) holeExact) body) := by
    intro leftHole rightHole leftOuter rightOuter holeExact outerExact
      context body
    cases holeExact
    cases outerExact
    rfl
  let fixedRegionTypeExact :=
    congrArg (Region definitions) fixedSigsExact
  have filledCast :
      cast fixedRegionTypeExact
          (insertionInner.sourceInner.fill insertionInner.replacement) =
        erasureInner.targetInner.fill
          (relativeRaw.siteBody.conjoin replacement) := by
    rw [castFill holeSigsExact fixedSigsExact]
    change
      (cast outerInnerTypeExact
          (cast holeInnerTypeExact insertionInner.sourceInner)).fill
          (cast holeRegionTypeExact insertionInner.replacement) =
        erasureInner.targetInner.fill
          (relativeRaw.siteBody.conjoin replacement)
    rw [innerCast, bodyCast]
    rfl
  have denoteTransport :
      ∀ {left right : List Sig}
        (same : left = right)
        (env : Env model.toPreModel left)
        (body : Region definitions left),
        denoteRegion model.toPreModel definitionEnv env body ↔
          denoteRegion model.toPreModel definitionEnv
            (cast (congrArg (Env model.toPreModel) same) env)
            (cast (congrArg (Region definitions) same) body) := by
    intro left right same env body
    cases same
    rfl
  have rawSameOrder :=
    (denoteTransport fixedSigsExact
      (Env.comp generatedFixed
        (InsertionCompilation.enclosingRenaming compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer))
      (insertionInner.sourceInner.fill
        insertionInner.replacement)).mp checkedHolds
  change
    denoteRegion model.toPreModel definitionEnv
      (cast fixedEnvTypeExact
        (Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer)))
      (cast fixedRegionTypeExact
        (insertionInner.sourceInner.fill
          insertionInner.replacement)) at rawSameOrder
  rw [fixedEnvironmentExact, filledCast] at rawSameOrder
  apply
    (context_equiv erasureInner.targetInner model.toPreModel definitionEnv
      (relativeRaw.siteBody.conjoin replacement)
      (replacement.conjoin relativeRaw.siteBody)
      (fun env => by
        rw [Region.denote_conjoin, Region.denote_conjoin]
        exact and_comm)
      erasedFixed).mp
  exact rawSameOrder

/--
At a co-scoped application, consume the singleton-erasure receipt without
closing the dying-scope binders. The resulting equivalence is exactly between
the replacement-conjoined erased site body and the original site body.
-/
private theorem RelationJoinStep.coScopedErasureBodyDenotation
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
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (coScoped :
      (source.val.wires dying).scope = step.sourceRegion) :
    ∃ (outer : ConcreteElaboration.WireContext step.prior.val)
      (fuel : Nat)
      (sourceFrame : RegionFrame definitions step.prior.val outer)
      (targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication outer))
      (provenance :
        SingletonRemovalSemantics.ErasureFrameProvenance step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion) fuel outer
          (step.priorRegionImage (source.val.wires dying).scope)
          sourceFrame targetFrame)
      (siteOuter : ConcreteElaboration.WireContext step.base.val)
      (generatedFrame :
        RegionFrame definitions step.attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer targetFrame provenance.targetGenerated).outer))
      (pairedInsertion :
        InsertionCompilation.PairedGeneratedFrame compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          fuel
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer targetFrame provenance.targetGenerated).outer
          siteOuter
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer targetFrame provenance.targetGenerated).frame
          generatedFrame)
      (visibleExact :
        targetFrame.visible =
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible)
      (baseVisibleExact :
        step.base_generated.symm ▸
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible =
          compiled.site.frame.visible)
      (head : Var sourceFrame.visible.sigs (.rel step.relationArgs))
      (arguments : Vars sourceFrame.visible.sigs step.relationArgs)
      (replacement : Region definitions targetFrame.visible.sigs),
      compileRegionFrame? definitions step.prior.val
          (step.priorRegionImage step.sourceRegion) fuel
          (step.priorRegionImage (source.val.wires dying).scope) outer =
        some sourceFrame ∧
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage step.sourceRegion))
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope))
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication outer) =
        some targetFrame ∧
      ∀ targetEnv : Env model.toPreModel targetFrame.visible.sigs,
        (let canonicalEnv :=
          congrArg ConcreteElaboration.WireContext.sigs
              visibleExact ▸ targetEnv
         transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible)
            compiled.site.frame.visible
            baseVisibleExact
            canonicalEnv (.rel step.relationArgs)
            (baseRenamedVariable step sourceFrame.visible
              compiled.site.frame.visible baseVisibleExact head) =
          WireQuantifierSemantics.contentRelation model definitionEnv
            contentCompiled boundaryExact parameterValues) →
        (let canonicalEnv :=
          congrArg ConcreteElaboration.WireContext.sigs
              visibleExact ▸ targetEnv
         Vars.denote
            (transportEnvironment step.base_generated.symm
              (SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication sourceFrame.visible)
              compiled.site.frame.visible baseVisibleExact canonicalEnv)
            (parameterVariables step.relationArgs
              (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
          parameterValues) →
        (denoteRegion model.toPreModel definitionEnv targetEnv
              (replacement.conjoin targetFrame.siteBody) ↔
          denoteRegion model.toPreModel definitionEnv
            (Env.comp
              (congrArg ConcreteElaboration.WireContext.sigs
                  visibleExact ▸ targetEnv)
              (SingletonRemovalSemantics.contextRenaming step.prior
                step.priorApplication sourceFrame.visible))
            sourceFrame.siteBody) := by
  obtain ⟨_scopeCompiled, outer, fuel, sourceFrame, sourceVisible,
      _inner, _scopeVisible, _sourceAbove, sourceGenerated,
      _sourceFrameBody, _sourceDecomposition, _scopeBody, pairedErasure⟩ :=
    RelationJoinStep.dyingScopeErasure step
  obtain ⟨head, arguments, applicationCompiled, _headOrigin,
      argumentOrigins⟩ :=
    RelationJoinStep.relativeCompiledApplication step sourceFrame sourceVisible
  obtain ⟨targetFrame, provenance, siteOuter, generatedFrame,
      pairedInsertion⟩ :=
    RelationJoinStep.pairedInsertionAtDying step contentCompiled compiled
      sourceVisible pairedErasure
  have baseVisibleExact :=
    RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
      compiled targetFrame provenance pairedInsertion
  have pairedFixed :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.prior.val.nodes step.priorApplication).region
        (step.prior.val.nodes step.priorApplication).region fuel outer
        sourceFrame := by
    simpa [step.priorNodeExact, coScoped] using pairedErasure
  obtain ⟨fixedTarget, fixedGenerated, fixedVisible, fixedLaw⟩ :=
    SingletonRemovalSemantics.PairedGeneratedFrame.fixedScope_replacement_denotation
      step.prior step.priorApplication
      (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
      fuel outer
      sourceFrame pairedFixed (.atom head arguments) applicationCompiled
      model.toPreModel definitionEnv
  have targetSame : fixedTarget = targetFrame := by
    apply Option.some.inj
    exact fixedGenerated.symm.trans (by
      simpa [step.priorNodeExact, coScoped] using provenance.targetGenerated)
  subst fixedTarget
  let canonicalReplacement :=
    untransportRegion step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceFrame.visible)
      compiled.site.frame.visible baseVisibleExact
      (intrinsicSplice contentCompiled.openDiagram
        compiled.intrinsicAttachment)
  let replacement :=
    congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible.symm ▸ canonicalReplacement
  refine
    ⟨outer, fuel, sourceFrame, targetFrame, provenance, siteOuter,
      generatedFrame, pairedInsertion, provenance.targetVisible,
      baseVisibleExact, head, arguments, replacement, sourceGenerated,
      provenance.targetGenerated, ?_⟩
  intro targetEnv headValue parameterExact
  apply fixedLaw replacement targetEnv
  exact
    RelationJoinStep.erasureLocalReplacementAt step contentCompiled compiled
      model definitionEnv boundaryExact parameterValues sourceFrame
      targetFrame provenance baseVisibleExact head arguments argumentOrigins
      targetEnv headValue parameterExact

/--
One accepted relation application projects the checked dying-scope body back
to the canonical prior dying-scope body before either scope's binders close.
The projection carries the canonical relation variable and the ordered
parameter tuple exactly, so each checked environment determines its canonical
relation value.
-/
private def transportRegion
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (region : left.RegionId) :
    right.RegionId :=
  Fin.cast (congrArg ConcreteDiagram.regionCount same) region

private theorem transportRegion_climb
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (depth : Nat)
    (region : left.RegionId) :
  right.climb depth (transportRegion same region) =
      (left.climb depth region).map (transportRegion same) := by
  cases same
  have transportIdentity :
      ∀ value : left.RegionId,
        transportRegion (Eq.refl left) value = value := by
    intro value
    apply Fin.ext
    rfl
  rw [transportIdentity region]
  cases left.climb depth region with
  | none => rfl
  | some reached =>
      simp only [Option.map_some, transportIdentity]

private theorem transportRegion_root
    {left right : ConcreteDiagram definitionCount}
    (same : left = right) :
    transportRegion same left.root = right.root := by
  cases same
  simp [transportRegion]

private def transportWire
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (wire : left.WireId) :
    right.WireId :=
  Fin.cast (congrArg ConcreteDiagram.wireCount same) wire

def relationJoinPriorToCheckedWire
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    step.checked.val.WireId :=
  transportWire step.checked_generated.symm
    (step.attachment.hostWire
      (transportWire step.base_generated.symm
        (SingletonRemovalSemantics.targetWire
          step.prior step.priorApplication wire)))

def relationJoinPriorToCheckedRegion
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (region : step.prior.val.RegionId) :
    step.checked.val.RegionId :=
  transportRegion step.checked_generated.symm
    (step.attachment.hostRegion
      (transportRegion step.base_generated.symm
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication region)))

theorem relationJoinPriorToCheckedRegion_injective
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    Function.Injective (relationJoinPriorToCheckedRegion step) := by
  intro left right same
  unfold relationJoinPriorToCheckedRegion at same
  have hostSame :
      step.attachment.hostRegion
          (Fin.cast
            (congrArg ConcreteDiagram.regionCount
              step.base_generated).symm
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              step.prior step.priorApplication left)) =
        step.attachment.hostRegion
          (Fin.cast
            (congrArg ConcreteDiagram.regionCount
              step.base_generated).symm
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              step.prior step.priorApplication right)) := by
    apply Fin.ext
    simpa using congrArg Fin.val same
  have baseSame := step.attachment.hostRegion_injective hostSame
  have rawSame :
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication left =
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication right := by
    apply Fin.ext
    simpa using congrArg Fin.val baseSame
  exact
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_injective
      step.prior step.priorApplication rawSame

theorem relationJoinPriorToCheckedRegion_climb
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (depth : Nat)
    (region : step.prior.val.RegionId) :
    step.checked.val.climb depth
        (relationJoinPriorToCheckedRegion step region) =
      (step.prior.val.climb depth region).map
        (relationJoinPriorToCheckedRegion step) := by
  unfold relationJoinPriorToCheckedRegion
  rw [transportRegion_climb,
    ConcreteSpliceAttachment.hostRegion_climb,
    transportRegion_climb,
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_climb]
  cases step.prior.val.climb depth region <;> rfl

theorem relationJoinPriorToCheckedRegion_root
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    relationJoinPriorToCheckedRegion step step.prior.val.root =
      step.checked.val.root := by
  unfold relationJoinPriorToCheckedRegion
  rw [← transportRegion_root step.checked_generated.symm]
  congr 1
  rw [show step.attachment.diagram.root =
      step.attachment.hostRegion step.base.val.root by rfl]
  congr 1
  rw [← transportRegion_root step.base_generated.symm]
  rfl


/--
The canonical structural boundary for one relation-join step. Both contexts
stop strictly before the dying scope's binder block; the complete scope
expressions are therefore hole bodies. This is the only shape in which content
insertion may be transported without pretending that its new local binders
match the retained source binders.
-/
structure RelationJoinStep.AboveDyingScopeReceipt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope))
    (checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)) where
  priorSiteOuter :
    ConcreteElaboration.WireContext step.prior.val
  checkedSiteOuter :
    ConcreteElaboration.WireContext step.checked.val
  priorAbove :
    DiagramContext definitions priorSiteOuter.sigs []
  checkedAbove :
    DiagramContext definitions checkedSiteOuter.sigs []
  priorBody :
    Region definitions
      (priorSiteOuter.extend
        (step.priorRegionImage (source.val.wires dying).scope)).sigs
  checkedBody :
    Region definitions
      (checkedSiteOuter.extend
        (step.checkedRegionImage (source.val.wires dying).scope)).sigs
  priorVisibleExact :
    priorScope.frame.visible =
      priorSiteOuter.extend
        (step.priorRegionImage (source.val.wires dying).scope)
  checkedVisibleExact :
    checkedScope.frame.visible =
      checkedSiteOuter.extend
        (step.checkedRegionImage (source.val.wires dying).scope)
  priorDecomposition :
    DiagramContext.StopsAboveBindMany
      ((step.prior.val.wiresAt
          (step.priorRegionImage
            (source.val.wires dying).scope)).map
        (fun wire => (step.prior.val.wires wire).sig))
      priorAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            priorVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend priorSiteOuter
            (step.priorRegionImage
              (source.val.wires dying).scope))) ▸
        priorScope.frame.context)
  checkedDecomposition :
    DiagramContext.StopsAboveBindMany
      ((step.checked.val.wiresAt
          (step.checkedRegionImage
            (source.val.wires dying).scope)).map
        (fun wire => (step.checked.val.wires wire).sig))
      checkedAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            checkedVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend checkedSiteOuter
            (step.checkedRegionImage
              (source.val.wires dying).scope))) ▸
        checkedScope.frame.context)
  priorBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs priorVisibleExact ▸
        priorScope.frame.siteBody =
      priorBody
  checkedBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs checkedVisibleExact ▸
        checkedScope.frame.siteBody =
      checkedBody
  siteProjection :
    WireRenaming priorSiteOuter.sigs checkedSiteOuter.sigs
  siteProjectionOrigin :
    ∀ {sig : Sig} (value : Var priorSiteOuter.sigs sig),
      ConcreteElaboration.WireContext.origin step.checked.val
          checkedSiteOuter.ids (siteProjection value) =
        relationJoinPriorToCheckedWire step
          (ConcreteElaboration.WireContext.origin step.prior.val
            priorSiteOuter.ids value)
  priorRootFill :
    priorScope.checked =
      priorAbove.fill
        (ConcreteElaboration.finishRegion step.prior.val priorSiteOuter
          (step.priorRegionImage (source.val.wires dying).scope) priorBody)
  checkedRootFill :
    checkedScope.checked =
      checkedAbove.fill
        (ConcreteElaboration.finishRegion step.checked.val checkedSiteOuter
          (step.checkedRegionImage (source.val.wires dying).scope)
          checkedBody)
  composable :
    DiagramContext.ComposableSemanticZipper.{u} priorAbove checkedAbove
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env siteProjection)

def RelationJoinStep.AboveDyingScopeReceipt.priorCanonical
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (receipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :
    SiteCompilation.AboveScopeDecomposition priorScope where
  siteOuter := receipt.priorSiteOuter
  above := receipt.priorAbove
  visibleExact := receipt.priorVisibleExact
  contextDecomposition := receipt.priorDecomposition

def RelationJoinStep.AboveDyingScopeReceipt.checkedCanonical
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (receipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :
    SiteCompilation.AboveScopeDecomposition checkedScope where
  siteOuter := receipt.checkedSiteOuter
  above := receipt.checkedAbove
  visibleExact := receipt.checkedVisibleExact
  contextDecomposition := receipt.checkedDecomposition

private theorem RelationJoinStep.AboveDyingScopeReceipt.ofNormalized
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (priorSiteOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (checkedSiteOuter :
      ConcreteElaboration.WireContext step.checked.val)
    (priorAbove :
      DiagramContext definitions priorSiteOuter.sigs [])
    (checkedAbove :
      DiagramContext definitions checkedSiteOuter.sigs [])
    (priorBody :
      Region definitions
        (priorSiteOuter.extend
          (step.priorRegionImage
            (source.val.wires dying).scope)).sigs)
    (checkedBody :
      Region definitions
        (checkedSiteOuter.extend
          (step.checkedRegionImage
            (source.val.wires dying).scope)).sigs)
    (priorVisibleExact :
      priorScope.frame.visible =
        priorSiteOuter.extend
          (step.priorRegionImage (source.val.wires dying).scope))
    (checkedVisibleExact :
      checkedScope.frame.visible =
        checkedSiteOuter.extend
          (step.checkedRegionImage (source.val.wires dying).scope))
    (priorDecomposition :
      DiagramContext.StopsAboveBindMany
        ((step.prior.val.wiresAt
            (step.priorRegionImage
              (source.val.wires dying).scope)).map
          (fun wire => (step.prior.val.wires wire).sig))
        priorAbove
        (((congrArg ConcreteElaboration.WireContext.sigs
              priorVisibleExact).trans
            (ConcreteElaboration.WireContext.sigs_extend priorSiteOuter
              (step.priorRegionImage
                (source.val.wires dying).scope))) ▸
          priorScope.frame.context))
    (checkedDecomposition :
      DiagramContext.StopsAboveBindMany
        ((step.checked.val.wiresAt
            (step.checkedRegionImage
              (source.val.wires dying).scope)).map
          (fun wire => (step.checked.val.wires wire).sig))
        checkedAbove
        (((congrArg ConcreteElaboration.WireContext.sigs
              checkedVisibleExact).trans
            (ConcreteElaboration.WireContext.sigs_extend checkedSiteOuter
              (step.checkedRegionImage
                (source.val.wires dying).scope))) ▸
          checkedScope.frame.context))
    (priorBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs priorVisibleExact ▸
          priorScope.frame.siteBody =
        priorBody)
    (checkedBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs checkedVisibleExact ▸
          checkedScope.frame.siteBody =
        checkedBody)
    (siteProjection :
      WireRenaming priorSiteOuter.sigs checkedSiteOuter.sigs)
    (siteProjectionOrigin :
      ∀ {sig : Sig} (value : Var priorSiteOuter.sigs sig),
        ConcreteElaboration.WireContext.origin step.checked.val
            checkedSiteOuter.ids (siteProjection value) =
          relationJoinPriorToCheckedWire step
            (ConcreteElaboration.WireContext.origin step.prior.val
              priorSiteOuter.ids value))
    (priorRootFill :
      priorScope.checked =
        priorAbove.fill
          (ConcreteElaboration.finishRegion step.prior.val priorSiteOuter
            (step.priorRegionImage (source.val.wires dying).scope)
            priorBody))
    (checkedRootFill :
      checkedScope.checked =
        checkedAbove.fill
          (ConcreteElaboration.finishRegion step.checked.val checkedSiteOuter
            (step.checkedRegionImage (source.val.wires dying).scope)
            checkedBody))
    (composable :
      DiagramContext.ComposableSemanticZipper.{u} priorAbove checkedAbove
        (fun (_pre : PreModel.{u}) env => env)
        (fun (_pre : PreModel.{u}) env =>
          Env.comp env siteProjection)) :
    Nonempty
      (RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :=
  ⟨{
    priorSiteOuter := priorSiteOuter
    checkedSiteOuter := checkedSiteOuter
    priorAbove := priorAbove
    checkedAbove := checkedAbove
    priorBody := priorBody
    checkedBody := checkedBody
    priorVisibleExact := priorVisibleExact
    checkedVisibleExact := checkedVisibleExact
    priorDecomposition := priorDecomposition
    checkedDecomposition := checkedDecomposition
    priorBodyExact := priorBodyExact
    checkedBodyExact := checkedBodyExact
    siteProjection := siteProjection
    siteProjectionOrigin := siteProjectionOrigin
    priorRootFill := priorRootFill
    checkedRootFill := checkedRootFill
    composable := composable
  }⟩

/--
One selected sibling constructor for the direct relation-join prefix fold.
The two transformation-specific sibling laws meet only at the shared checked
base environment; the resulting zipper is constructed directly between the
prior and checked contexts.
-/
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

private def singletonErasureBase
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions) :
    CheckedDiagram definitions :=
  ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed,
    candidateWellFormed⟩

private theorem RelationJoinStep.erasureRegionLocalSigs_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (outer : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).wiresAt
          (SingletonRemovalSemantics.targetRegion source removed region)).map
        fun wire =>
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).wires wire).sig) =
      (source.val.wiresAt region).map
        (fun wire => (source.val.wires wire).sig) := by
  have extended :=
    SingletonRemovalSemantics.targetContext_sigs source removed
      (outer.extend region)
  have outerExact :=
    SingletonRemovalSemantics.targetContext_sigs source removed outer
  have contextExact :=
    congrArg ConcreteElaboration.WireContext.sigs
      (SingletonRemovalSemantics.targetContext_extend source removed outer
        region)
  rw [contextExact] at extended
  have extended' :
      (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).wiresAt
            (SingletonRemovalSemantics.targetRegion source removed region)).map
          fun wire =>
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).wires wire).sig) ++
          (SingletonRemovalSemantics.targetContext source removed outer).sigs =
        (source.val.wiresAt region).map
            (fun wire => (source.val.wires wire).sig) ++ outer.sigs := by
    simpa only [ConcreteElaboration.WireContext.extend,
      ConcreteElaboration.WireContext.sigs, List.map_append] using extended
  rw [outerExact] at extended'
  exact List.append_cancel_right extended'

private theorem RelationJoinStep.cast_bind
    {sourceOuter targetOuter : List Sig}
    (same : sourceOuter = targetOuter)
    (sig : Sig)
    (inner :
      DiagramContext definitions holeCtx (sig :: sourceOuter)) :
    same ▸
        (DiagramContext.bind sig inner :
          DiagramContext definitions holeCtx sourceOuter) =
      DiagramContext.bind sig
        ((congrArg (List.cons sig) same) ▸ inner) := by
  cases same
  rfl

private theorem RelationJoinStep.bindContextFor_eq_bindMany
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    bindContextFor diagram outerIds localIds inner =
      DiagramContext.bindMany
        (localIds.map fun wire => (diagram.wires wire).sig)
        ((@List.map_append _ _
          (fun wire => (diagram.wires wire).sig)
          localIds outerIds) ▸ inner) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simp only [bindContextFor, List.map_cons,
        DiagramContext.bindMany]
      rw [induction (.bind (diagram.wires head).sig inner)]
      apply congrArg
      exact
        RelationJoinStep.cast_bind
          (@List.map_append _ _
            (fun wire => (diagram.wires wire).sig)
            tail outerIds)
          (diagram.wires head).sig inner

private theorem RelationJoinStep.cast_context_trans
    {left middle right hole : List Sig}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (context : DiagramContext definitions hole left) :
    middleRight ▸ (leftMiddle ▸ context) =
      (leftMiddle.trans middleRight) ▸ context := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem RelationJoinStep.bindMany_reindexBound
    {leftBound rightBound outer hole : List Sig}
    (same : leftBound = rightBound)
    (inner :
      DiagramContext definitions hole (leftBound ++ outer)) :
    DiagramContext.bindMany leftBound inner =
      DiagramContext.bindMany rightBound
        ((congrArg (fun bound => bound ++ outer) same) ▸ inner) := by
  cases same
  rfl

/--
Cross one ancestor binder block for the two transformations at once.  The
erased local-wire environment is used only as the exact middle witness between
the prior and generated extensions; the resulting zipper has the composite
renaming as its single outer authority.
-/
private theorem RelationJoinStep.compileRegionBody_of_frameBranch
    {diagram : ConcreteDiagram definitions.length}
    {site region selected : diagram.RegionId}
    {fuel : Nat}
    {outer : ConcreteElaboration.WireContext diagram}
    {nodes : ItemSeq definitions (outer.extend region).sigs}
    {nested around :
      RegionFrame definitions diagram (outer.extend region)}
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions diagram
          (outer.extend region) (diagram.nodesAt region) =
        some nodes)
    (nestedCompiled :
      compileRegionFrame? definitions diagram site fuel selected
          (outer.extend region) =
        some nested)
    (aroundCompiled :
      compileSiblingFrame? definitions diagram fuel
          (outer.extend region) selected nested nodes
          (diagram.childrenOf region) =
        some around) :
    compileRegionBody? definitions diagram fuel region outer =
      some (around.context.fill around.siteBody) := by
  have nestedBodyCompiled :=
    compileRegionFrame?_sound definitions diagram site fuel selected
      (outer.extend region) nested nestedCompiled
  obtain ⟨children, childrenCompiled, bodyExact⟩ :=
    compileSiblingFrame?_sound definitions diagram fuel
      (outer.extend region) selected nested around nodes
      (diagram.childrenOf region) nestedBodyCompiled aroundCompiled
  simp only [compileRegionBody?, nodesCompiled, childrenCompiled,
    Option.bind_some]
  exact congrArg some bodyExact

private theorem RelationJoinStep.map_map_exact
    (values : List α)
    (first : α → β)
    (second : β → γ) :
    (values.map first).map second =
      values.map (fun value => second (first value)) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (List.cons (second (first head))) induction

private theorem RelationJoinStep.hostClimb_exact
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (steps : Nat) (region : base.val.RegionId),
      attachment.diagram.climb steps (attachment.hostRegion region) =
        (base.val.climb steps region).map attachment.hostRegion
  | 0, _ => rfl
  | steps + 1, region => by
      cases data : base.val.regions region with
      | sheet =>
          simp only [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data,
            RelationJoinStep.hostClimb_exact compiled steps parent]

private theorem RelationJoinStep.hostEncloses_iff_exact
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (ancestor child : base.val.RegionId) :
    attachment.diagram.Encloses
        (attachment.hostRegion ancestor) (attachment.hostRegion child) ↔
      base.val.Encloses ancestor child := by
  rw [ConcreteElaboration.encloses_iff_exists,
    ConcreteElaboration.encloses_iff_exists]
  constructor
  · rintro ⟨steps, climbed⟩
    have mapped := climbed
    rw [RelationJoinStep.hostClimb_exact compiled] at mapped
    cases sourceClimb : base.val.climb steps.val child with
    | none => simp [sourceClimb] at mapped
    | some region =>
        rw [sourceClimb] at mapped
        have regionExact :=
          InsertionCompilation.NaturalityInternal.hostRegion_injective
            attachment (Option.some.inj mapped)
        subst region
        have bounded :=
          ConcreteElaboration.successfulClimb_le_count definitions base.val
            base.property steps.val child ancestor sourceClimb
        exact ⟨⟨steps.val, by omega⟩, sourceClimb⟩
  · rintro ⟨steps, climbed⟩
    let targetSteps : Fin (attachment.diagram.regionCount + 1) :=
      ⟨steps.val, by
        change steps.val < attachment.regionCount + 1
        simp only [ConcreteSpliceAttachment.regionCount]
        omega⟩
    refine ⟨targetSteps, ?_⟩
    rw [RelationJoinStep.hostClimb_exact compiled, climbed]
    rfl

private theorem RelationJoinStep.find?_eq_some_of_unique_true
    (values : List α)
    (selected : α)
    (predicate : α → Bool)
    (selectedMember : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (onlySelected :
      ∀ candidate, candidate ∈ values →
        predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at selectedMember
  | cons head tail induction =>
      by_cases headExact : head = selected
      · subst head
        simp [List.find?, selectedTrue]
      · have selectedTail : selected ∈ tail := by
          have selectedEither : selected = head ∨ selected ∈ tail := by
            simpa only [List.mem_cons] using selectedMember
          exact
            selectedEither.resolve_left
              (fun selectedHead => headExact selectedHead.symm)
        have headFalse : predicate head = false := by
          cases headValue : predicate head with
          | false => rfl
          | true =>
              exact
                (headExact
                  (onlySelected head (by simp) headValue)).elim
        simp only [List.find?_cons, headFalse, Bool.false_eq_true]
        exact
          induction selectedTail
            (fun candidate member =>
              onlySelected candidate (by simp [member]))

private theorem RelationJoinStep.find?_map_exact
    (values : List α)
    (mapping : α → β)
    (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool)
    (predicateExact :
      ∀ value, targetPredicate (mapping value) = sourcePredicate value) :
    (values.map mapping).find? targetPredicate =
      (values.find? sourcePredicate).map mapping := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicateExact head]
      cases sourcePredicate head <;> simp [induction]

/--
The internal result of the simultaneous relation prefix fold before the
checked-diagram equality is transported.  Its source-to-target zipper is built
directly; the erased diagram is only the shared environment at which the two
ordinary sibling laws meet.
-/
private structure RelationJoinStep.PairedAboveScopeReflection
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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
private theorem RelationJoinStep.pairedStopAboveCurrent
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
private theorem RelationJoinStep.pairedSiblingAboveScope
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (ConcreteElaboration.compileRegion? definitions source.val
                fuel)
              (ConcreteElaboration.compileRegion? definitions
                (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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

private theorem RelationJoinStep.aboveDyingScopeReceiptOfExplicitBase
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
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
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

private theorem RelationJoinStep.preBinderDenotation
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
    RelationJoinStep.relativeCompiledApplication step priorFrame priorVisible
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
    RelationJoinStep.priorParameterSignatures step boundaryExact
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
      RelationJoinStep.priorParameterScopes step parameterScopes position
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
      RelationJoinStep.parameterVariables_exact step contentCompiled compiled
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
      RelationJoinStep.baseRenamedVariable step priorFrame.visible
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
      unfold compiledHead RelationJoinStep.baseRenamedVariable
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
                RelationJoinStep.baseRenamedVariable step
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
        RelationJoinStep.baseRenamedVariable step priorFrame.visible
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
        unfold compiledValue RelationJoinStep.baseRenamedVariable
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
                    RelationJoinStep.baseRenamedVariable step
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
        RelationJoinStep.erasureLocalReplacementAt step contentCompiled
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
          RelationJoinStep.baseRenamedVariables step priorFrame.visible
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
          rw [RelationJoinStep.baseRenamedVariables_origins,
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
              (RelationJoinStep.baseRenamedVariable step priorFrame.visible
                compiled.site.frame.visible baseVisibleExact value) =
            checkedEnv sig (frameProjection value) := by
      intro sig value
      let compiledValue :=
        RelationJoinStep.baseRenamedVariable step priorFrame.visible
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
          RelationJoinStep.baseRenamedVariable step priorFrame.visible
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
        unfold compiledValue RelationJoinStep.baseRenamedVariable
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
      RelationJoinStep.strictDescendantBodyDenotation step contentCompiled
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
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire_injective
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
      RelationJoinStep.parameterVariables_exact step contentCompiled compiled
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
            RelationJoinStep.erasureLocalReplacementAt step contentCompiled
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
            simpa [RelationJoinStep.baseRenamedVariable,
              transportEnvironment_apply,
              SingletonRemovalSemantics.erasureVisibleRenaming] using
              canonicalHeadValue
          · rw [canonicalParameterExact]
            dsimp only
            unfold RelationJoinStep.baseRenamedVariables
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

private theorem vars_denote_eq_of_origins_ne
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
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalWireImage finalDying finalScope) :
    (final.val.wires finalDying).scope = finalScope := by
  induction trace with
  | nil => rfl
  | snoc trace step priorExact priorRegionImageExact priorWireImageExact
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

/-- Interpret exactly the structural derivation owned by one trace transport. -/
theorem RelationJoinSemanticTrace.AboveDyingScopeTransport.toSemanticZipper
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (transport :
      RelationJoinSemanticTrace.AboveDyingScopeTransport.{u}
        sourceScope finalScope) :
    DiagramContext.SemanticZipper
      transport.sourceCanonical.above transport.finalCanonical.above
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env transport.outerProjection) :=
  transport.composable.toSemanticZipper

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

theorem RelationJoinSemanticTrace.AboveDyingScopeFold.toSemanticZipper
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope finalScope) :
    DiagramContext.SemanticZipper
      fold.transport.sourceCanonical.above
      fold.transport.finalCanonical.above
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env fold.transport.outerProjection) :=
  fold.transport.toSemanticZipper

/--
Consume an endpoint local law through the interpreter owned by this fold.
Callers close the site's ordered local binders into `sourceBody` and
`finalBody`; this theorem is the sole above-scope integration surface.
-/
theorem
    RelationJoinSemanticTrace.AboveDyingScopeFold.transportEndpointLocalLaw
    {source : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {final : CheckedDiagram definitions}
    {finalSite : final.val.RegionId}
    {finalScope : SiteCompilation final finalSite}
    (fold :
      RelationJoinSemanticTrace.AboveDyingScopeFold.{u}
        sourceScope finalScope)
    (direction : DiagramContext.ContextDirection)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody :
      Region definitions fold.transport.sourceCanonical.siteOuter.sigs)
    (finalBody :
      Region definitions fold.transport.finalCanonical.siteOuter.sigs)
    (fixed : Env pre [])
    (localLaw :
      ∀ descendant :
          Env pre fold.transport.finalCanonical.siteOuter.sigs,
        DiagramContext.PreservesOuter
            fold.transport.finalCanonical.above fixed descendant →
          direction.holds
            (denoteRegion pre definitionEnv descendant finalBody)
            (denoteRegion pre definitionEnv
              (Env.comp descendant fold.transport.outerProjection)
              sourceBody)) :
    (direction.through
        fold.transport.sourceCanonical.above.cutDepth).holds
      (denoteRegion pre definitionEnv fixed
        (fold.transport.finalCanonical.above.fill finalBody))
      (denoteRegion pre definitionEnv fixed
        (fold.transport.sourceCanonical.above.fill sourceBody)) :=
  fold.toSemanticZipper.transport direction pre definitionEnv
    sourceBody finalBody fixed localLaw

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
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalWireImage finalDying finalScope)
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
  | snoc trace step priorExact priorRegionImageExact priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      cases priorExact
      cases eq_of_heq priorRegionImageExact
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
        RelationJoinStep.preBinderDenotation step contentCompiled compiled
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
private theorem RelationJoinSemanticTrace.preBinderDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args parameterSigs : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalWireImage finalDying finalScope)
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
