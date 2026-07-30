import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityGenerated
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrameSupport

namespace VisualProof
namespace InsertionCompilation

universe u

open NaturalityInternal

/-- The paired contexts immediately inside one enclosing region's binders. -/
structure PairedInnerFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val)
    (sourceFrame :
      RegionFrame definitions base.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter))
    extends
      RegionFrame.PairedInner region (attachment.hostRegion region)
        sourceOuter (hostContext attachment sourceOuter) sourceFrame
          targetFrame where
  siteVisible :
    compiled.site.frame.visible = siteOuter.extend site
  sourceVisible :
    sourceFrame.visible = siteOuter.extend site
  targetVisible :
    targetFrame.visible = generatedSiteContext attachment siteOuter

/--
The intrinsic insertion body expressed in the actual retained source frame.
The retained source body comes from that frame; only the intrinsic fragment is
transported from the accepted site's canonical visible context.
-/
def PairedInnerFrame.replacement
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame :
      RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (paired :
      PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
        targetFrame) :
    Region definitions sourceFrame.visible.sigs :=
  Region.conjoin sourceFrame.siteBody
    (congrArg ConcreteElaboration.WireContext.sigs
        (paired.siteVisible.trans paired.sourceVisible.symm) ▸
      intrinsicSplice fragmentCompiled.openDiagram
        compiled.intrinsicAttachment)

/-- Canonical source-to-generated environment map before the enclosing binders. -/
def enclosingRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext base.val) :
    WireRenaming (sourceOuter.extend region).sigs
      ((hostContext attachment sourceOuter).extend
        (attachment.hostRegion region)).sigs := by
  by_cases atSite : region = site
  · subst region
    exact generatedSiteHostRenaming compiled sourceOuter
  · exact hostExtendedRenaming compiled region atSite sourceOuter
      (hostContext attachment sourceOuter)
      (hostContextRenaming attachment sourceOuter)
      (hostContextRenaming_origin attachment sourceOuter)

theorem enclosingRenaming_contextAction
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext base.val)
    {sig : Sig}
    (value : Var (sourceOuter.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        ((hostContext attachment sourceOuter).extend
          (attachment.hostRegion region)).ids
        (enclosingRenaming compiled region sourceOuter value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val
          (sourceOuter.extend region).ids value) := by
  unfold enclosingRenaming
  split
  · subst region
    exact generatedSiteHostRenaming_contextAction compiled sourceOuter value
  · rename_i atSite
    exact
      hostExtendedRenaming_contextAction compiled region atSite sourceOuter
        (hostContext attachment sourceOuter)
        (hostContextRenaming attachment sourceOuter)
        (hostContextRenaming_origin attachment sourceOuter) value

end InsertionCompilation
end VisualProof
