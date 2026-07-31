import VisualProof.Diagram.Concrete.WirePrimitive.Content
import VisualProof.Diagram.Concrete.WirePrimitive.UniformSiteFactorization

namespace VisualProof

namespace ConcreteWirePrimitive

open WirePrimitive
open WirePrimitive.ConcreteFactorization

private def appliedNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  sites.sites.map AppliedSite.node

private def appliedRegions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.RegionId :=
  sites.sites.map AppliedSite.region

namespace CutWrapResult

/--
Erase every source atom and the old witness wire; independently erase every
generated single-atom cut and the new witness wire. The remaining checked
diagrams must be concretely isomorphic.
-/
def checkCommonCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) :
    Option (CommonCoreReceipt source result.checked) := do
  let targetSites ←
    checkAllAppliedSites result.checked result.targetWire
  ConcreteFactorization.checkCommonCore source result.checked
    [] (appliedNodes result.sites) [wire]
    (appliedRegions targetSites) (appliedNodes targetSites)
    [result.targetWire]

end CutWrapResult

namespace ParallelSplitResult

/--
Erase every source atom and old witness wire; independently erase the two
ordered target atoms per logical position and both generated witness wires.
-/
def checkCommonCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) :
    Option (CommonCoreReceipt source result.checked) := do
  let firstSites ←
    checkAllAppliedSites result.checked result.firstWire
  let secondSites ←
    checkAllAppliedSites result.checked result.secondWire
  ConcreteFactorization.checkCommonCore source result.checked
    [] (appliedNodes result.sites) [wire]
    [] (appliedNodes firstSites ++ appliedNodes secondSites)
    [result.firstWire, result.secondWire]

end ParallelSplitResult

namespace EndsDeleteResult

/--
Erase every source application while retaining its now endpoint-free witness
wire. The executable deletion target itself is the independently checked core.
-/
def checkCommonCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    Option (CommonCoreReceipt source result.checked) :=
  ConcreteFactorization.checkCommonCore source result.checked
    [] (appliedNodes result.sites) []
    [] [] []

end EndsDeleteResult

end ConcreteWirePrimitive

end VisualProof
