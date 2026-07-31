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

/-- The common-core isomorphism identifies two retained source regions. -/
private def regionsCorrespond
    {source target : CheckedDiagram definitions}
    (core : CommonCoreReceipt source target)
    (sourceRegion : source.val.RegionId)
    (targetRegion : target.val.RegionId) : Bool :=
  match core.sourceErasure.regionImage? sourceRegion,
      core.targetErasure.regionImage? targetRegion with
  | some sourceImage, some targetImage =>
      decide (core.coreIso.regions sourceImage = targetImage)
  | _, _ => false

/-- The common-core isomorphism identifies two retained source wires. -/
private def wiresCorrespond
    {source target : CheckedDiagram definitions}
    (core : CommonCoreReceipt source target)
    (sourceWire : source.val.WireId)
    (targetWire : target.val.WireId) : Bool :=
  match core.sourceErasure.wireImage? sourceWire,
      core.targetErasure.wireImage? targetWire with
  | some sourceImage, some targetImage =>
      decide (core.coreIso.wires sourceImage = targetImage)
  | _, _ => false

/-- Ordered argument tuples cross the exact common-core wire transport. -/
private def argumentsCorrespond
    {source target : CheckedDiagram definitions}
    (core : CommonCoreReceipt source target)
    (sourceArguments : List source.val.WireId)
    (targetArguments : List target.val.WireId) : Bool :=
  sourceArguments.length == targetArguments.length &&
    (List.zip sourceArguments targetArguments).all fun pair =>
      wiresCorrespond core pair.1 pair.2

/-- A generated wrap site contributes its cut's retained parent to the core. -/
private def cutParent?
    {target : CheckedDiagram definitions}
    {wire : target.val.WireId}
    (site : AppliedSite target wire) :
    Option target.val.RegionId :=
  match target.val.regions site.region with
  | .sheet => none
  | .cut parent => some parent

/-- Every free region and ordered argument wire of one site survives erasure. -/
private def sourceBoundaryRetained
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (core : CommonCoreReceipt source target)
    (site : AppliedSite source wire) : Bool :=
  (core.sourceErasure.regionImage? site.region).isSome &&
    site.arguments.all fun argument =>
      (core.sourceErasure.wireImage? argument).isSome

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

/--
Exact positional ledger for cut wrapping. Besides equal cardinality, every
source site is paired with a generated target cut whose retained parent and
ordered argument tuple cross the checked common-core isomorphism.
-/
def SitesCorrespond
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (core : CommonCoreReceipt source result.checked) : Prop :=
  result.sites.sites.length = targetSites.sites.length ∧
    (List.zip result.sites.sites targetSites.sites).all (fun pair =>
      match cutParent? pair.2 with
      | none => false
      | some targetParent =>
          regionsCorrespond core pair.1.region targetParent &&
            argumentsCorrespond core pair.1.arguments pair.2.arguments) =
      true

/-- Sealed checker-owned wrap-site correspondence and exact common core. -/
structure SiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) where
  private mk ::
  targetSites : AllAppliedSites result.checked result.targetWire
  commonCore : CommonCoreReceipt source result.checked
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  targetScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope
  private sites_correspond :
    SitesCorrespond result targetSites commonCore
  private scope_corresponds :
    regionsCorrespond commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.targetWire).scope = true
  private cut_depth_exact :
    sourceScope.frame.context.cutDepth =
      targetScope.frame.context.cutDepth

/-- Check the complete positional wrap ledger; no caller supplies a pairing. -/
def checkSiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) :
    Option (SiteLedger result) := do
  let targetSites ←
    checkAllAppliedSites result.checked result.targetWire
  let commonCore ← result.checkCommonCore
  let sourceScope ←
    compileSite? source (source.val.wires wire).scope
  let targetScope ←
    compileSite? result.checked
      (result.checked.val.wires result.targetWire).scope
  if exact :
      result.sites.sites.length = targetSites.sites.length ∧
        (List.zip result.sites.sites targetSites.sites).all (fun pair =>
          match cutParent? pair.2 with
          | none => false
          | some targetParent =>
              regionsCorrespond commonCore pair.1.region targetParent &&
                argumentsCorrespond commonCore pair.1.arguments
                  pair.2.arguments) =
        true then
    if scopeExact :
        regionsCorrespond commonCore (source.val.wires wire).scope
              (result.checked.val.wires result.targetWire).scope = true ∧
          sourceScope.frame.context.cutDepth =
            targetScope.frame.context.cutDepth then
      pure
        ⟨targetSites, commonCore, sourceScope, targetScope, exact,
          scopeExact.1, scopeExact.2⟩
    else
      none
  else
    none

namespace SiteLedger

/-- The retained wrap ledger covers the source and target sites positionally. -/
theorem correspondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    (ledger : SiteLedger result) :
    SitesCorrespond result ledger.targetSites ledger.commonCore :=
  ledger.sites_correspond

/-- The checker identifies the acted binder scope through the common core. -/
theorem scopeCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    (ledger : SiteLedger result) :
    regionsCorrespond ledger.commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.targetWire).scope = true :=
  ledger.scope_corresponds

/-- Wrap source and target binder contexts have one exact outer cut depth. -/
theorem cutDepth
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    (ledger : SiteLedger result) :
    ledger.sourceScope.frame.context.cutDepth =
      ledger.targetScope.frame.context.cutDepth :=
  ledger.cut_depth_exact

end SiteLedger

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

/--
Exact positional ledger for parallel splitting. Each source site is paired
with one site on each generated wire at the same transported region and with
the same transported ordered argument tuple.
-/
def SitesCorrespond
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (firstSites : AllAppliedSites result.checked result.firstWire)
    (secondSites : AllAppliedSites result.checked result.secondWire)
    (core : CommonCoreReceipt source result.checked) : Prop :=
  result.sites.sites.length = firstSites.sites.length ∧
    result.sites.sites.length = secondSites.sites.length ∧
    (List.zip result.sites.sites
      (List.zip firstSites.sites secondSites.sites)).all (fun pair =>
        regionsCorrespond core pair.1.region pair.2.1.region &&
          regionsCorrespond core pair.1.region pair.2.2.region &&
          argumentsCorrespond core pair.1.arguments pair.2.1.arguments &&
          argumentsCorrespond core pair.1.arguments pair.2.2.arguments) =
      true

/-- Sealed checker-owned split-site correspondence and exact common core. -/
structure SiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) where
  private mk ::
  firstSites : AllAppliedSites result.checked result.firstWire
  secondSites : AllAppliedSites result.checked result.secondWire
  commonCore : CommonCoreReceipt source result.checked
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  firstScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.firstWire).scope
  secondScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.secondWire).scope
  private sites_correspond :
    SitesCorrespond result firstSites secondSites commonCore
  private first_scope_corresponds :
    regionsCorrespond commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.firstWire).scope = true
  private second_scope_corresponds :
    regionsCorrespond commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.secondWire).scope = true
  private first_cut_depth_exact :
    sourceScope.frame.context.cutDepth =
      firstScope.frame.context.cutDepth
  private second_cut_depth_exact :
    sourceScope.frame.context.cutDepth =
      secondScope.frame.context.cutDepth

/-- Check the complete positional split ledger; no caller supplies a pairing. -/
def checkSiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) :
    Option (SiteLedger result) := do
  let firstSites ←
    checkAllAppliedSites result.checked result.firstWire
  let secondSites ←
    checkAllAppliedSites result.checked result.secondWire
  let commonCore ← result.checkCommonCore
  let sourceScope ←
    compileSite? source (source.val.wires wire).scope
  let firstScope ←
    compileSite? result.checked
      (result.checked.val.wires result.firstWire).scope
  let secondScope ←
    compileSite? result.checked
      (result.checked.val.wires result.secondWire).scope
  if exact :
      result.sites.sites.length = firstSites.sites.length ∧
        result.sites.sites.length = secondSites.sites.length ∧
        (List.zip result.sites.sites
          (List.zip firstSites.sites secondSites.sites)).all (fun pair =>
            regionsCorrespond commonCore pair.1.region pair.2.1.region &&
              regionsCorrespond commonCore pair.1.region pair.2.2.region &&
              argumentsCorrespond commonCore pair.1.arguments
                pair.2.1.arguments &&
              argumentsCorrespond commonCore pair.1.arguments
                pair.2.2.arguments) =
          true then
    if scopeExact :
        regionsCorrespond commonCore (source.val.wires wire).scope
              (result.checked.val.wires result.firstWire).scope = true ∧
          regionsCorrespond commonCore (source.val.wires wire).scope
              (result.checked.val.wires result.secondWire).scope = true ∧
          sourceScope.frame.context.cutDepth =
              firstScope.frame.context.cutDepth ∧
          sourceScope.frame.context.cutDepth =
              secondScope.frame.context.cutDepth then
      pure
        ⟨firstSites, secondSites, commonCore, sourceScope, firstScope,
          secondScope, exact, scopeExact.1, scopeExact.2.1,
          scopeExact.2.2.1, scopeExact.2.2.2⟩
    else
      none
  else
    none

namespace SiteLedger

/-- The retained split ledger covers all three site collections positionally. -/
theorem correspondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : SiteLedger result) :
    SitesCorrespond result ledger.firstSites ledger.secondSites
      ledger.commonCore :=
  ledger.sites_correspond

/-- The first generated binder occupies the transported acted scope. -/
theorem firstScopeCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : SiteLedger result) :
    regionsCorrespond ledger.commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.firstWire).scope = true :=
  ledger.first_scope_corresponds

/-- The second generated binder occupies the transported acted scope. -/
theorem secondScopeCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : SiteLedger result) :
    regionsCorrespond ledger.commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.secondWire).scope = true :=
  ledger.second_scope_corresponds

/-- Source and first generated binder contexts have equal outer cut depth. -/
theorem firstCutDepth
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : SiteLedger result) :
    ledger.sourceScope.frame.context.cutDepth =
      ledger.firstScope.frame.context.cutDepth :=
  ledger.first_cut_depth_exact

/-- Source and second generated binder contexts have equal outer cut depth. -/
theorem secondCutDepth
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : SiteLedger result) :
    ledger.sourceScope.frame.context.cutDepth =
      ledger.secondScope.frame.context.cutDepth :=
  ledger.second_cut_depth_exact

end SiteLedger

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

/-- Every deleted source cell retains its free region and ordered arguments. -/
def SitesRetained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire)
    (core : CommonCoreReceipt source result.checked) : Prop :=
  result.sites.sites.all (sourceBoundaryRetained core) = true

/-- Sealed checker-owned deletion-site boundary and exact common core. -/
structure SiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) where
  private mk ::
  commonCore : CommonCoreReceipt source result.checked
  erasureTrace : AppliedSiteErasure.Result source wire
  erasureIso :
    ConcreteIso erasureTrace.target.val result.checked.val
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  targetScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope
  private sites_retained : SitesRetained result commonCore
  private scope_corresponds :
    regionsCorrespond commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.targetWire).scope = true
  private cut_depth_exact :
    sourceScope.frame.context.cutDepth =
      targetScope.frame.context.cutDepth

/-- Check every deleted site's retained free boundary. -/
def checkSiteLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    Option (SiteLedger result) := do
  let commonCore ← result.checkCommonCore
  let erasureTrace ← AppliedSiteErasure.check source wire
  let erasureIso ←
    ConcreteIsoSearch.findConcreteIso? erasureTrace.target.val
      result.checked.val
  let sourceScope ←
    compileSite? source (source.val.wires wire).scope
  let targetScope ←
    compileSite? result.checked
      (result.checked.val.wires result.targetWire).scope
  if exact :
      result.sites.sites.all (sourceBoundaryRetained commonCore) = true then
    if scopeExact :
        regionsCorrespond commonCore (source.val.wires wire).scope
              (result.checked.val.wires result.targetWire).scope = true ∧
          sourceScope.frame.context.cutDepth =
            targetScope.frame.context.cutDepth then
      pure
        ⟨commonCore, erasureTrace, erasureIso, sourceScope, targetScope,
          exact, scopeExact.1, scopeExact.2⟩
    else
      none
  else
    none

namespace SiteLedger

/-- Every recorded deletion site has a complete retained free boundary. -/
theorem retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : EndsDeleteResult source wire}
    (ledger : SiteLedger result) :
    SitesRetained result ledger.commonCore :=
  ledger.sites_retained

/--
The checker-owned singleton fold removes every acted endpoint and lands on
the executable batch deletion target up to checked concrete isomorphism.
-/
def erasureLanding
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : EndsDeleteResult source wire}
    (ledger : SiteLedger result) :
    ConcreteIso ledger.erasureTrace.target.val result.checked.val :=
  ledger.erasureIso

/-- The retained acted binder occupies the transported source scope. -/
theorem scopeCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : EndsDeleteResult source wire}
    (ledger : SiteLedger result) :
    regionsCorrespond ledger.commonCore (source.val.wires wire).scope
      (result.checked.val.wires result.targetWire).scope = true :=
  ledger.scope_corresponds

/-- Deletion source and target binder contexts have equal outer cut depth. -/
theorem cutDepth
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : EndsDeleteResult source wire}
    (ledger : SiteLedger result) :
    ledger.sourceScope.frame.context.cutDepth =
      ledger.targetScope.frame.context.cutDepth :=
  ledger.cut_depth_exact

end SiteLedger

end EndsDeleteResult

end ConcreteWirePrimitive

end VisualProof
