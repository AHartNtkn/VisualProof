import VisualProof.Rule.Vacuity.Assembly
import VisualProof.Diagram.RegionSite

namespace VisualProof.Rule.WholeAssemblyVacuity

open Diagram
open Theory

mutual
  /-- The source region corresponding to the target region in which an added
  identity occurs. This follows only retained cuts; added target items do not
  create source frames. -/
  def IdentityOnlyExtension.AddedIdentity.sourceSite
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {targetRegion : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source targetRegion} :
      (node : extension.AddedIdentity) → source.Site
    | .item node => node.sourceItemSite.toRegionSite _

  def IdentityOnlyItemsExtension.AddedIdentity.sourceItemSite
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {targetItems : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source targetItems} :
      (node : extension.AddedIdentity) → source.RegionSite
    | .atomTail node => node.sourceItemSite.prepend _
    | .identityTail node => node.sourceItemSite.prepend _
    | .cutHead node => .cut .nil _ _ node.sourceSite
    | .cutTail node => node.sourceItemSite.prepend _
    | .here => .here _
    | .addedIdentityTail node => node.sourceItemSite
end

mutual
  /-- The source region corresponding to the owner of one fresh target wire. -/
  def IdentityOnlyExtension.FreshWire.sourceSite
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {targetRegion : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source targetRegion} :
      (wire : extension.FreshWire) → source.Site
    | .local _ => .root _
    | .nested wire => wire.sourceItemSite.toRegionSite _

  def IdentityOnlyItemsExtension.FreshWire.sourceItemSite
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {targetItems : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source targetItems} :
      (wire : extension.FreshWire) → source.RegionSite
    | .atomTail wire => wire.sourceItemSite.prepend _
    | .identityTail wire => wire.sourceItemSite.prepend _
    | .cutHead wire => .cut .nil _ _ wire.sourceSite
    | .cutTail wire => wire.sourceItemSite.prepend _
    | .addedIdentityTail wire => wire.sourceItemSite
end

end VisualProof.Rule.WholeAssemblyVacuity
