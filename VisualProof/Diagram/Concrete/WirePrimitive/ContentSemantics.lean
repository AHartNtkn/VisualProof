import VisualProof.Diagram.Concrete.WirePrimitive.Content
import VisualProof.Diagram.Concrete.WirePrimitive.UniformSiteFactorization
import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalZipper
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityZipper

namespace VisualProof

namespace ConcreteWirePrimitive

open WirePrimitive
open WirePrimitive.ConcreteFactorization
open ConcreteWireQuantifier.SingletonRemovalSemantics

universe u

/-- Canonical first occurrence of one checked visible wire. -/
private def visibleVariable
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId) :
    (ids : List diagram.WireId) →
      wire ∈ ids →
        Var (ids.map fun id => (diagram.wires id).sig)
          (diagram.wires wire).sig
  | [], member => by simp at member
  | head :: tail, member =>
      if same : wire = head then
        same ▸ .here
      else
        .there
          (visibleVariable diagram wire tail (by
            simpa [same] using member))

@[simp] private theorem visibleVariable_origin
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (ids : List diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (visibleVariable diagram wire ids member) =
      wire := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      unfold visibleVariable
      split
      · rename_i same
        subst head
        rfl
      · simp only [ConcreteElaboration.WireContext.origin]
        exact induction _

/-- Every canonical checked site context has distinct visible wire ids. -/
private theorem site_visible_nodup
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.visible.ids.Nodup := by
  obtain ⟨scopeCompiled, outer, _fuel, _relative, _relativeVisible,
      _inner, scopeVisible, _rootInner, above, _generated, _relativeBody,
      _relativeContext, _scopeBody, _rootBody, _replacementBody,
      _cutDepth⟩ :=
    compiled.factorAt_relative_origin site
      (ConcreteDiagram.encloses_refl base.val site)
  have same : scopeCompiled = compiled :=
    SiteCompilation.unique scopeCompiled compiled
  subst scopeCompiled
  rw [scopeVisible]
  exact
    ConcreteElaboration.extend_nodup definitions base.val base.property
      outer site above

/--
An environment assigns the acted relation wire the universal relation whenever
that wire is visible in the supplied checked context.
-/
def AssignsUniversal
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (context : ConcreteElaboration.WireContext source.val)
    (pre : PreModel.{u})
    (env : Env pre context.sigs) : Prop :=
  ∀ (arguments : List Sig)
    (head : Var context.sigs (.rel arguments)),
    ConcreteElaboration.WireContext.origin source.val context.ids head =
        wire →
      ∀ values : PreModel.Args pre.Domain arguments,
        pre.apply (env _ head) values

/--
Sealed semantic transport between the unbound bodies at one acted wire scope.
The compiler-selected scopes and typed renaming remain existential proof data,
so the proposition composes across a trace without becoming a second
construction API.
-/
def UniversalScopeTransport
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (target : CheckedDiagram definitions)
    (targetWire : target.val.WireId) : Prop :=
  ∃ (sourceScope :
      SiteCompilation source (source.val.wires wire).scope)
    (targetScope :
      SiteCompilation target (target.val.wires targetWire).scope)
    (map :
      WireRenaming sourceScope.frame.visible.sigs
        targetScope.frame.visible.sigs),
    (∀ {signature : Sig}
      (value : Var sourceScope.frame.visible.sigs signature),
      ConcreteElaboration.WireContext.origin source.val
          sourceScope.frame.visible.ids value =
          wire →
        ConcreteElaboration.WireContext.origin target.val
            targetScope.frame.visible.ids (map value) =
          targetWire) ∧
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (targetEnv : Env pre targetScope.frame.visible.sigs),
      AssignsUniversal targetWire targetScope.frame.visible pre targetEnv →
        (denoteRegion pre definitionEnv targetEnv
              targetScope.frame.siteBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv map) sourceScope.frame.siteBody)

private def embedOuterThroughScope
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

/--
Embed the variables strictly outside a compiled scope through that scope's
local wire block into the full visible context.
-/
def scopeEmbedOuter
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    WireRenaming canonical.siteOuter.sigs compiled.frame.visible.sigs :=
  embedOuterThroughScope compiled.frame.visible canonical.siteOuter
    canonical.visibleExact

private theorem embedOuterThroughScope_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site)
    {signature : Sig}
    (value : Var outer.sigs signature) :
    ConcreteElaboration.WireContext.origin base.val visible.ids
        (embedOuterThroughScope visible outer same value) =
      ConcreteElaboration.WireContext.origin base.val outer.ids value := by
  cases same
  simpa [embedOuterThroughScope,
    ConcreteElaboration.WireContext.extend]
    using
      (ConcreteElaboration.origin_appendRightVar base.val
        (base.val.wiresAt site) value)

@[simp] theorem scopeEmbedOuter_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled)
    {signature : Sig}
    (value : Var canonical.siteOuter.sigs signature) :
    ConcreteElaboration.WireContext.origin base.val
        compiled.frame.visible.ids
        (scopeEmbedOuter canonical value) =
      ConcreteElaboration.WireContext.origin base.val
        canonical.siteOuter.ids value := by
  exact
    embedOuterThroughScope_origin compiled.frame.visible
      canonical.siteOuter canonical.visibleExact value

/-- Reindex one coherent decomposition across proof-independent compilation. -/
def reindexAboveScopeDecomposition
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {left right : SiteCompilation base site}
    (same : left = right)
    (canonical : SiteCompilation.AboveScopeDecomposition left) :
    SiteCompilation.AboveScopeDecomposition right :=
  same ▸ canonical

@[simp] theorem reindexAboveScopeDecomposition_siteOuter
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {left right : SiteCompilation base site}
    (same : left = right)
    (canonical : SiteCompilation.AboveScopeDecomposition left) :
    (reindexAboveScopeDecomposition same canonical).siteOuter =
      canonical.siteOuter := by
  cases same
  rfl

@[simp] theorem reindexAboveScopeDecomposition_above
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {left right : SiteCompilation base site}
    (same : left = right)
    (canonical : SiteCompilation.AboveScopeDecomposition left) :
    congrArg ConcreteElaboration.WireContext.sigs
        (reindexAboveScopeDecomposition_siteOuter same canonical) ▸
      (reindexAboveScopeDecomposition same canonical).above =
        canonical.above := by
  cases same
  rfl

/-- Reindex a typed wire renaming across equal source and target signatures. -/
def reindexWireRenaming
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (map : WireRenaming source' target') :
    WireRenaming source target :=
  fun {_} value =>
    targetExact.symm ▸ map (sourceExact ▸ value)

private noncomputable def reindexComposableSemanticZipperHoles
    {definitions : List (List Sig)}
    {sourceHole sourceHole' targetHole targetHole' : List Sig}
    (sourceExact : sourceHole = sourceHole')
    (targetExact : targetHole = targetHole')
    (source : DiagramContext definitions sourceHole [])
    (source' : DiagramContext definitions sourceHole' [])
    (sourceContextExact : sourceExact ▸ source = source')
    (target : DiagramContext definitions targetHole [])
    (target' : DiagramContext definitions targetHole' [])
    (targetContextExact : targetExact ▸ target = target')
    (outerMap :
      ∀ pre : PreModel.{u}, Env pre [] → Env pre [])
    (map : WireRenaming sourceHole' targetHole')
    (zipper :
      DiagramContext.ComposableSemanticZipper source' target' outerMap
        (fun (_pre : PreModel.{u}) env => Env.comp env map)) :
    DiagramContext.ComposableSemanticZipper source target outerMap
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env
          (reindexWireRenaming sourceExact targetExact map)) := by
  cases sourceExact
  cases targetExact
  cases sourceContextExact
  cases targetContextExact
  exact zipper

/--
Coherent universal transport at the acted binder scope and strictly above it.
The full-visible projection extends the site-outer projection, so the local
body equivalence and constructor-preserving outer trace close through one
authoritative binder environment.
-/
structure UniversalOuterTransport
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (target : CheckedDiagram definitions)
    (targetWire : target.val.WireId) : Type (u + 1) where
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  targetSite : target.val.RegionId
  targetSite_eq :
    targetSite = (target.val.wires targetWire).scope
  targetScope :
    SiteCompilation target targetSite
  sourceCanonical :
    SiteCompilation.AboveScopeDecomposition sourceScope
  targetCanonical :
    SiteCompilation.AboveScopeDecomposition targetScope
  outerProjection :
    WireRenaming sourceCanonical.siteOuter.sigs
      targetCanonical.siteOuter.sigs
  visibleProjection :
    WireRenaming sourceScope.frame.visible.sigs
      targetScope.frame.visible.sigs
  visibleExtendsOuter :
    ∀ {signature : Sig}
      (value : Var sourceCanonical.siteOuter.sigs signature),
      visibleProjection (scopeEmbedOuter sourceCanonical value) =
        scopeEmbedOuter targetCanonical (outerProjection value)
  visibleMapsWire :
    ∀ {signature : Sig}
      (value : Var sourceScope.frame.visible.sigs signature),
      ConcreteElaboration.WireContext.origin source.val
          sourceScope.frame.visible.ids value =
          wire →
        ConcreteElaboration.WireContext.origin target.val
            targetScope.frame.visible.ids (visibleProjection value) =
          targetWire
  body :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (targetEnv : Env pre targetScope.frame.visible.sigs),
      AssignsUniversal targetWire targetScope.frame.visible pre targetEnv →
        (denoteRegion pre definitionEnv targetEnv
              targetScope.frame.siteBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv visibleProjection)
            sourceScope.frame.siteBody)
  composable :
    DiagramContext.ComposableSemanticZipper
      sourceCanonical.above targetCanonical.above
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env outerProjection)

namespace UniversalOuterTransport

/-- Identity structural transport at one checked acted scope. -/
noncomputable def identity
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    UniversalOuterTransport.{u} source wire source wire := by
  let scope : SiteCompilation source (source.val.wires wire).scope :=
    Classical.choice (by
      obtain ⟨scope, _compiled⟩ :=
        compileSite_complete source (source.val.wires wire).scope
      exact ⟨scope⟩)
  let canonical :
      SiteCompilation.AboveScopeDecomposition scope :=
    Classical.choice scope.aboveScopeDecomposition
  exact
    {
      sourceScope := scope
      targetSite := (source.val.wires wire).scope
      targetSite_eq := rfl
      targetScope := scope
      sourceCanonical := canonical
      targetCanonical := canonical
      outerProjection := fun {_} value => value
      visibleProjection := fun {_} value => value
      visibleExtendsOuter := fun _ => rfl
      visibleMapsWire := by
        intro _ value origin
        exact origin
      body := by
        intro _pre _definitionEnv _targetEnv _assigned
        exact Iff.rfl
      composable :=
        DiagramContext.ComposableSemanticZipper.identity canonical.above
    }

/-- Structural transports compose through proof-independent site compilation. -/
noncomputable def compose
    {source middle target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {middleWire : middle.val.WireId}
    {targetWire : target.val.WireId}
    (first :
      UniversalOuterTransport.{u} source wire middle middleWire)
    (second :
      UniversalOuterTransport.{u} middle middleWire target targetWire) :
    UniversalOuterTransport.{u} source wire target targetWire := by
  cases first with
  | mk sourceScope middleSite middleSiteEq middleScope sourceCanonical
      middleCanonical firstProjection firstVisibleProjection
      firstVisibleExtendsOuter firstVisibleMapsWire firstBody
      firstComposable =>
      cases middleSiteEq
      cases second with
      | mk secondMiddleScope targetSite targetSiteEq targetScope
          secondMiddleCanonical targetCanonical secondProjection
          secondVisibleProjection secondVisibleExtendsOuter
          secondVisibleMapsWire secondBody secondComposable =>
          have sameScope :
              middleScope = secondMiddleScope :=
            SiteCompilation.unique middleScope secondMiddleScope
          cases sameScope
          let aligned :=
            middleCanonical.alignment secondMiddleCanonical
          cases middleCanonical with
          | mk middleOuter middleAbove middleVisible middleDecomposition =>
              cases secondMiddleCanonical with
              | mk secondOuter secondAbove secondVisible
                  secondDecomposition =>
                    cases aligned with
                    | mk outerExact aboveExact =>
                        cases outerExact
                        cases aboveExact
                        exact
                          {
                            sourceScope := sourceScope
                            targetSite := targetSite
                            targetSite_eq := targetSiteEq
                            targetScope := targetScope
                            sourceCanonical := sourceCanonical
                            targetCanonical := targetCanonical
                            outerProjection :=
                              fun {_} value =>
                                secondProjection (firstProjection value)
                            visibleProjection :=
                              fun {_} value =>
                                secondVisibleProjection
                                  (firstVisibleProjection value)
                            visibleExtendsOuter := by
                              intro signature value
                              rw [firstVisibleExtendsOuter,
                                secondVisibleExtendsOuter]
                            visibleMapsWire := by
                              intro signature value origin
                              exact
                                secondVisibleMapsWire
                                  (firstVisibleProjection value)
                                  (firstVisibleMapsWire value origin)
                            body := by
                              intro pre definitionEnv targetEnv universal
                              have middleUniversal :
                                  AssignsUniversal middleWire
                                    middleScope.frame.visible pre
                                    (Env.comp targetEnv
                                      secondVisibleProjection) := by
                                intro arguments head origin values
                                exact
                                  universal arguments
                                    (secondVisibleProjection head)
                                    (secondVisibleMapsWire head origin)
                                    values
                              exact
                                (secondBody pre definitionEnv targetEnv
                                  universal).trans
                                  (firstBody pre definitionEnv
                                    (Env.comp targetEnv
                                      secondVisibleProjection)
                                    middleUniversal)
                            composable :=
                              DiagramContext.ComposableSemanticZipper.compose
                                firstComposable secondComposable
                          }

/-- Forget the coherent outer trace while retaining its universal body law. -/
theorem toScopeTransport
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {targetWire : target.val.WireId}
    (transport :
      UniversalOuterTransport.{u} source wire target targetWire) :
    UniversalScopeTransport.{u} source wire target targetWire := by
  cases transport with
  | mk sourceScope targetSite targetSiteEq targetScope sourceCanonical
      targetCanonical outerProjection visibleProjection
      visibleExtendsOuter visibleMapsWire body composable =>
      cases targetSiteEq
      exact
        ⟨sourceScope, targetScope, visibleProjection, visibleMapsWire,
          body⟩

end UniversalOuterTransport

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

private theorem compileNodes_atom_transport
    {source : CheckedDiagram definitions}
    {left right : ConcreteElaboration.WireContext source.val}
    (same : left = right)
    (node : source.val.NodeId)
    (head : Var right.sigs (.rel arguments))
    (values : Vars right.sigs arguments)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val right [node] =
        some (.cons (.atom head values) .nil)) :
    ConcreteElaboration.compileNodes? definitions source.val left [node] =
      some
        (.cons
          (.atom
            (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ head)
            (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ values))
          .nil) := by
  cases same
  exact compiled

private theorem origin_transport
    {source : CheckedDiagram definitions}
    {left right : ConcreteElaboration.WireContext source.val}
    (same : left = right)
    (value : Var right.sigs sig) :
    ConcreteElaboration.WireContext.origin source.val left.ids
        (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ value) =
      ConcreteElaboration.WireContext.origin source.val right.ids value := by
  cases same
  rfl

private theorem origin_transport_forward
    {diagram : ConcreteDiagram definitionCount}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (value : Var left.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem origin_transport_renaming
    {diagram : ConcreteDiagram definitionCount}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {sourceSignatures : List Sig}
    (map : WireRenaming sourceSignatures right.sigs)
    (value : Var sourceSignatures sig) :
    ConcreteElaboration.WireContext.origin diagram left.ids
        ((congrArg ConcreteElaboration.WireContext.sigs same.symm ▸
          map) value) =
      ConcreteElaboration.WireContext.origin diagram right.ids
        (map value) := by
  cases same
  rfl

private theorem scope_environment_coherence
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (outer : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceScope :
      ConcreteElaboration.WireContext source.val)
    (targetScope :
      ConcreteElaboration.WireContext
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed))
    (sourceExact : sourceScope = outer.extend region)
    (targetExact :
      targetScope =
        (targetContext source removed outer).extend
          (targetRegion source removed region))
    (scopeTargetExact :
      targetScope = targetContext source removed sourceScope)
    (pre : PreModel)
    (targetEnv : Env pre targetScope.sigs) :
    Env.comp
        (congrArg ConcreteElaboration.WireContext.sigs targetExact ▸
          targetEnv)
        (extendedContextRenaming source removed outer region) =
      congrArg ConcreteElaboration.WireContext.sigs sourceExact ▸
        Env.comp targetEnv
          (congrArg ConcreteElaboration.WireContext.sigs
              scopeTargetExact.symm ▸
            contextRenaming source removed sourceScope) := by
  subst sourceScope
  subst targetScope
  have exactProof :
      scopeTargetExact =
        (targetContext_extend source removed outer region).symm :=
    Subsingleton.elim _ _
  rw [exactProof]
  rfl

private theorem transported_environment_apply
    {diagram : ConcreteDiagram definitionCount}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (pre : PreModel)
    (env : Env pre left.sigs)
    {sig : Sig}
    (value : Var left.sigs sig) :
    (congrArg ConcreteElaboration.WireContext.sigs same ▸ env) sig
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      env sig value := by
  cases same
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

private theorem compileRegionFrame_site_inner_liftOuter_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (inner :
      DiagramContext definitions frame.visible.sigs
        (outer.extend site).sigs)
    (compiled :
      compileRegionFrame? definitions diagram site fuel site outer =
        some frame)
    (decomposition :
      frame.context =
        bindContextFor diagram outer.ids (diagram.wiresAt site) inner) :
    ∀ {sig : Sig} (value : Var (outer.extend site).sigs sig),
      ConcreteElaboration.WireContext.origin diagram frame.visible.ids
          (DiagramContext.liftOuter inner value) =
        ConcreteElaboration.WireContext.origin diagram
          (outer.extend site).ids value := by
  cases fuel with
  | zero =>
      simp [compileRegionFrame?] at compiled
  | succ childFuel =>
      unfold compileRegionFrame? at compiled
      simp only [↓reduceDIte] at compiled
      obtain ⟨body, _bodyCompiled, frameEquation⟩ :=
        Option.bind_eq_some_iff.mp compiled
      have frameExact :
          ({ visible := outer.extend site
             siteBody := body
             context :=
               bindContextFor diagram outer.ids
                 (diagram.wiresAt site) .hole } :
            RegionFrame definitions diagram outer) =
            frame :=
        Option.some.inj frameEquation
      subst frame
      have innerExact :
          (.hole :
            DiagramContext definitions (outer.extend site).sigs
              (outer.extend site).sigs) =
            inner := by
        apply
          bindContextFor_injective diagram outer.ids
            (diagram.wiresAt site)
        exact decomposition
      subst inner
      intro sig value
      rfl

namespace AppliedSite

/--
One checker-owned applied site induces the generic singleton-replacement
denotation law. The returned atom is compiled from the selected concrete node,
its head is proved to be the acted wire, and the target frame is generated by
the canonical checked erasure provenance. Rule-specific semantics need only
prove that their replacement denotes this exact atom.
-/
theorem replacement_denotation
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ (removedHead :
        Var site.frame.frame.visible.sigs
          (.rel site.argumentSignatures))
      (removedArguments :
        Vars site.frame.frame.visible.sigs site.argumentSignatures)
      (targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source site.node)
          (targetContext source site.node
            (ConcreteElaboration.WireContext.empty source.val)))
      (visibleExact :
        targetFrame.visible =
          targetContext source site.node site.frame.frame.visible),
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source site.node)
          (targetRegion source site.node
            (source.val.nodes site.node).region)
          (source.val.regionCount + 1)
          (targetRegion source site.node source.val.root)
          (targetContext source site.node
            (ConcreteElaboration.WireContext.empty source.val)) =
        some targetFrame ∧
      ConcreteElaboration.compileNodes? definitions source.val
          site.frame.frame.visible [site.node] =
        some (.cons (.atom removedHead removedArguments) .nil) ∧
      ConcreteElaboration.WireContext.origin source.val
          site.frame.frame.visible.ids removedHead =
        wire ∧
      ∀ replacement : Region definitions targetFrame.visible.sigs,
        (∀ targetVisibleEnv : Env pre targetFrame.visible.sigs,
          denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
            denoteItem pre definitionEnv
              (Env.comp
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleExact ▸ targetVisibleEnv)
                (contextRenaming source site.node
                  site.frame.frame.visible))
              (.atom removedHead removedArguments)) →
        ∀ targetOuterEnv :
            Env pre
              (targetContext source site.node
                (ConcreteElaboration.WireContext.empty source.val)).sigs,
          denoteRegion pre definitionEnv targetOuterEnv
              (targetFrame.context.fill
                (replacement.conjoin targetFrame.siteBody)) ↔
            denoteChecked pre definitionEnv source := by
  obtain ⟨sourceOuter, visibleExact, head, arguments, removedCompiled,
      headOrigin⟩ :=
    site.compiled_atom
  let removedHead :
      Var site.frame.frame.visible.sigs
        (.rel site.argumentSignatures) :=
    congrArg ConcreteElaboration.WireContext.sigs visibleExact.symm ▸
      head
  let removedArguments :
      Vars site.frame.frame.visible.sigs site.argumentSignatures :=
    congrArg ConcreteElaboration.WireContext.sigs visibleExact.symm ▸
      arguments
  have removedCompiledAtFrame :
      ConcreteElaboration.compileNodes? definitions source.val
          site.frame.frame.visible [site.node] =
        some (.cons (.atom removedHead removedArguments) .nil) :=
    compileNodes_atom_transport visibleExact site.node head arguments
      removedCompiled
  have removedHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val
          site.frame.frame.visible.ids removedHead =
        wire :=
    (origin_transport visibleExact head).trans headOrigin
  let empty := ConcreteElaboration.WireContext.empty source.val
  have rootAbove :
      ConcreteElaboration.ContextAbove source.val empty source.val.root := by
    exact
      ⟨by simp [empty, ConcreteElaboration.WireContext.empty],
        by simp [empty, ConcreteElaboration.WireContext.empty]⟩
  have paired :
      PairedGeneratedFrame source site.node
        (source.val.nodes site.node).region source.val.root
        (source.val.regionCount + 1) empty site.frame.frame := by
    simpa [site.node_data] using
      pairedGeneratedFrame source site.node erasure site.region source.val.root
        (source.val.regionCount + 1) empty site.frame.frame rootAbove
        site.frame.frame_generated
  obtain ⟨targetFrame, targetGenerated, visibleTarget, replacementLaw⟩ :=
    paired.replacement_denotation source site.node erasure source.val.root
      (source.val.regionCount + 1) empty site.frame.frame
      (.atom removedHead removedArguments) removedCompiledAtFrame pre
      definitionEnv
  refine
    ⟨removedHead, removedArguments, targetFrame, visibleTarget,
      targetGenerated, removedCompiledAtFrame, removedHeadOrigin, ?_⟩
  intro replacement localLaw targetOuterEnv
  have result := replacementLaw replacement localLaw targetOuterEnv
  rw [elaborate_denotes_checked]
  change
    denoteRegion pre definitionEnv targetOuterEnv
          (targetFrame.context.fill
            (replacement.conjoin targetFrame.siteBody)) ↔
      denoteRegion pre definitionEnv Env.empty (elaborate source)
  have sourceFills :
      site.frame.frame.context.fill site.frame.frame.siteBody =
        elaborate source := by
    simpa [SiteCompilation.checked] using site.frame.frame_fills_checked
  rw [← sourceFills]
  have emptyEnv :
      Env.comp targetOuterEnv (contextRenaming source site.node empty) =
        Env.empty := by
    funext sig value
    nomatch value
  rw [emptyEnv] at result
  exact result

private theorem fin_heq_of_val_eq
    {leftBound rightBound : Nat}
    (bounds : leftBound = rightBound)
    (left : Fin leftBound)
    (right : Fin rightBound)
    (values : left.val = right.val) :
    HEq left right := by
  subst rightBound
  exact heq_of_eq (Fin.ext values)

private noncomputable def cast_outer_transport
    {source left right : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {leftWire : left.val.WireId}
    {rightWire : right.val.WireId}
    (same : left = right)
    (wireSame : HEq leftWire rightWire)
    (transport :
      UniversalOuterTransport.{u} source wire left leftWire) :
    UniversalOuterTransport.{u} source wire right rightWire := by
  cases same
  cases eq_of_heq wireSame
  exact transport

/--
Erasing one checker-selected applied head preserves the acted binder body
when that binder is assigned the universal relation. Both the co-scoped and
strict-enclosure compiler cases discharge through the same replacement
zipper; no caller supplies a semantic premise.
-/
private theorem canonical_scope_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node) :
    let target : CheckedDiagram definitions :=
      ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source site.node,
        erasure.candidate_wellFormed⟩
    Nonempty
      (UniversalOuterTransport.{u} source wire target
        (targetWire source site.node wire)) := by
  let target : CheckedDiagram definitions :=
    ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source site.node,
      erasure.candidate_wellFormed⟩
  have encloses :
      source.val.Encloses (source.val.wires wire).scope site.region := by
    have scopeProof :=
      ConcreteElaboration.Internal.endpoint_scope definitions source.val
        source.property site.endpoint wire site.endpoint_owner
    simpa [AppliedSite.endpoint, site.node_data] using scopeProof
  obtain ⟨sourceScope, sourceOuter, fuel, sourceRelative,
      sourceRelativeVisible, sourceInner, sourceScopeVisible,
      _sourceRootInner, sourceAbove, sourceRelativeGenerated,
      _sourceRelativeBody, sourceRelativeDecomposition, sourceScopeBody,
      _sourceRootBody, _sourceReplacementBody, _sourceCutDepth⟩ :=
    site.frame.factorAt_relative_origin
      (source.val.wires wire).scope encloses
  have paired :
      PairedGeneratedFrame source site.node site.region
        (source.val.wires wire).scope fuel sourceOuter sourceRelative := by
    simpa [site.node_data] using
      pairedGeneratedFrame source site.node erasure site.region
        (source.val.wires wire).scope fuel sourceOuter sourceRelative
        sourceAbove sourceRelativeGenerated
  rcases paired with
    ⟨targetRelative, _pairedAbove, _pairedSourceGenerated, provenance⟩
  have provenanceAtNode :
      ErasureFrameProvenance source site.node
        (source.val.nodes site.node).region fuel sourceOuter
        (source.val.wires wire).scope sourceRelative targetRelative := by
    simpa [site.node_data] using provenance
  have zippers :
      ErasureFrameZippers source site.node (PUnit : Type u)
        (source.val.wires wire).scope sourceOuter sourceRelative
        targetRelative :=
    provenanceAtNode.zippers erasure.candidate_wellFormed
  rcases zippers with
    ⟨pairedInner, targetRelativeVisible, bodyLaw, innerZipper,
      _fullZipper⟩
  have sourceInnerExact : pairedInner.sourceInner = sourceInner := by
    apply
      bindContextFor_injective source.val sourceOuter.ids
        (source.val.wiresAt (source.val.wires wire).scope)
    exact
      pairedInner.sourceDecomposition.symm.trans
        sourceRelativeDecomposition
  let empty := ConcreteElaboration.WireContext.empty source.val
  have rootAbove :
      ConcreteElaboration.ContextAbove source.val empty source.val.root := by
    exact
      ⟨by simp [empty, ConcreteElaboration.WireContext.empty],
        by simp [empty, ConcreteElaboration.WireContext.empty]⟩
  have rootPaired :
      PairedGeneratedFrame source site.node site.region source.val.root
        (source.val.regionCount + 1) empty site.frame.frame := by
    simpa [site.node_data] using
      pairedGeneratedFrame source site.node erasure site.region source.val.root
        (source.val.regionCount + 1) empty site.frame.frame rootAbove
        site.frame.frame_generated
  rcases rootPaired with
    ⟨rootTargetFrame, _rootPairedAbove, _rootSourceGenerated,
      rootProvenance⟩
  obtain ⟨targetSite, _targetSiteCompiled⟩ :=
    compileSite_complete target (targetRegion source site.node site.region)
  have targetSiteFrameExact : targetSite.frame = rootTargetFrame := by
    apply Option.some.inj
    exact targetSite.frame_generated.symm.trans (by
      simpa [target, ConcreteElaboration.WireContext.empty,
        targetRegion_eq] using rootProvenance.targetGenerated)
  have targetSiteVisible :
      targetSite.frame.visible =
        targetContext source site.node site.frame.frame.visible := by
    rw [targetSiteFrameExact]
    exact rootProvenance.targetVisible
  have targetEncloses :
      target.val.Encloses
        (targetRegion source site.node (source.val.wires wire).scope)
        (targetRegion source site.node site.region) := by
    exact
      (target_encloses source site.node
        (source.val.wires wire).scope site.region).mpr encloses
  obtain ⟨targetScope, targetOuter, targetFuel, targetRelative',
      targetRelativeVisible', targetFactorInner, targetScopeVisible,
      _targetRootInner, _targetAbove, targetRelativeGenerated,
      _targetRelativeBody, targetRelativeDecomposition, targetScopeBody,
      _targetRootBody, _targetReplacementBody, _targetCutDepth⟩ :=
    targetSite.factorAt_relative_origin
      (targetRegion source site.node (source.val.wires wire).scope)
      targetEncloses
  have targetRelativeVisibleExact :
      targetRelative'.visible = targetRelative.visible := by
    exact
      targetRelativeVisible'.trans
        (targetSiteVisible.trans
          ((congrArg (targetContext source site.node)
              sourceRelativeVisible.symm).trans
            provenance.targetVisible.symm))
  have targetOuterExact :
      targetOuter = targetContext source site.node sourceOuter := by
    apply
      InsertionCompilation.compileRegionFrame?_outer_of_visible
        definitions target.val
        (targetRegion source site.node site.region)
        targetFuel fuel
        (targetRegion source site.node (source.val.wires wire).scope)
        targetOuter (targetContext source site.node sourceOuter)
        targetRelative' targetRelative
        targetRelativeGenerated
    · simpa [target] using provenance.targetGenerated
    · exact targetRelativeVisibleExact
  subst targetOuter
  let commonFuel := targetFuel + fuel
  have targetRelativeAtCommon :
      compileRegionFrame? definitions target.val
          (targetRegion source site.node site.region) commonFuel
          (targetRegion source site.node (source.val.wires wire).scope)
          (targetContext source site.node sourceOuter) =
        some targetRelative' :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions target.val
        (targetRegion source site.node site.region)
        targetFuel commonFuel (by
          unfold commonFuel
          omega)
        (targetRegion source site.node (source.val.wires wire).scope)
        (targetContext source site.node sourceOuter)
        targetRelativeGenerated
  have targetRelativeAtCommon' :
      compileRegionFrame? definitions target.val
          (targetRegion source site.node site.region) commonFuel
          (targetRegion source site.node (source.val.wires wire).scope)
          (targetContext source site.node sourceOuter) =
        some targetRelative :=
    InsertionCompilation.NaturalityInternal.compileRegionFrame_fuel_mono
      definitions target.val
        (targetRegion source site.node site.region)
        fuel commonFuel (by
          unfold commonFuel
          omega)
        (targetRegion source site.node (source.val.wires wire).scope)
        (targetContext source site.node sourceOuter)
        (by simpa [target] using provenance.targetGenerated)
  have targetRelativeExact : targetRelative' = targetRelative :=
    Option.some.inj
      (targetRelativeAtCommon.symm.trans targetRelativeAtCommon')
  subst targetRelative'
  have targetInnerExact :
      targetFactorInner = pairedInner.targetInner := by
    apply
      bindContextFor_injective target.val
        (targetContext source site.node sourceOuter).ids
        (target.val.wiresAt
          (targetRegion source site.node (source.val.wires wire).scope))
    exact
      targetRelativeDecomposition.symm.trans
        pairedInner.targetDecomposition
  subst targetFactorInner
  have scopeTargetVisible :
      targetScope.frame.visible =
        targetContext source site.node sourceScope.frame.visible :=
    targetScopeVisible.trans
      ((targetContext_extend source site.node sourceOuter
        (source.val.wires wire).scope).symm.trans
        (congrArg (targetContext source site.node)
          sourceScopeVisible).symm)
  let scopeMap :
      WireRenaming sourceScope.frame.visible.sigs
        targetScope.frame.visible.sigs :=
    congrArg ConcreteElaboration.WireContext.sigs
        scopeTargetVisible.symm ▸
      contextRenaming source site.node sourceScope.frame.visible
  have scopeMapWire :
      ∀ {signature : Sig}
        (value : Var sourceScope.frame.visible.sigs signature),
        ConcreteElaboration.WireContext.origin source.val
            sourceScope.frame.visible.ids value =
            wire →
          ConcreteElaboration.WireContext.origin target.val
              targetScope.frame.visible.ids (scopeMap value) =
            targetWire source site.node wire := by
    intro signature value origin
    unfold scopeMap
    rw [origin_transport_renaming scopeTargetVisible
      (contextRenaming source site.node sourceScope.frame.visible) value]
    exact (contextRenaming_action source site.node
      sourceScope.frame.visible value).trans (congrArg _ origin)
  obtain ⟨siteOuter, siteVisible, siteHead, siteArguments,
      siteCompiled, siteHeadOrigin⟩ := site.compiled_atom
  let relativeSiteVisible :
      sourceRelative.visible = siteOuter.extend site.region :=
    sourceRelativeVisible.trans siteVisible
  let removedHead :
      Var sourceRelative.visible.sigs (.rel site.argumentSignatures) :=
    congrArg ConcreteElaboration.WireContext.sigs
        relativeSiteVisible.symm ▸
      siteHead
  let removedArguments :
      Vars sourceRelative.visible.sigs site.argumentSignatures :=
    congrArg ConcreteElaboration.WireContext.sigs
        relativeSiteVisible.symm ▸
      siteArguments
  have removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceRelative.visible [site.node] =
        some (.cons (.atom removedHead removedArguments) .nil) := by
    exact
      compileNodes_atom_transport relativeSiteVisible site.node
        siteHead siteArguments siteCompiled
  have removedHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val
          sourceRelative.visible.ids removedHead =
        wire := by
    unfold removedHead
    exact
      (origin_transport relativeSiteVisible siteHead).trans
        siteHeadOrigin
  have sourceScopeHeadMember :
      wire ∈ sourceScope.frame.visible.ids :=
    sourceScope.visible_of_encloses wire
      (ConcreteDiagram.encloses_refl source.val
        (source.val.wires wire).scope)
  have relationSignature :
      (source.val.wires wire).sig =
        .rel site.argumentSignatures := by
    exact
      (congrArg (fun candidate => (source.val.wires candidate).sig)
        removedHeadOrigin.symm).trans
        (ConcreteElaboration.WireContext.origin_signature source.val
          sourceRelative.visible.ids removedHead)
  let sourceScopeHead :
      Var sourceScope.frame.visible.sigs
        (.rel site.argumentSignatures) :=
    InsertionCompilation.NaturalityInternal.castVar relationSignature
      (visibleVariable source.val wire
        sourceScope.frame.visible.ids sourceScopeHeadMember)
  have sourceScopeHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val
          sourceScope.frame.visible.ids sourceScopeHead =
        wire := by
    unfold sourceScopeHead
    exact
      (InsertionCompilation.NaturalityInternal.origin_castVar
        source.val sourceScope.frame.visible.ids relationSignature
        (visibleVariable source.val wire
          sourceScope.frame.visible.ids sourceScopeHeadMember)).trans
        (visibleVariable_origin source.val wire
          sourceScope.frame.visible.ids sourceScopeHeadMember)
  let sourceOuterHead :
      Var
        (sourceOuter.extend (source.val.wires wire).scope).sigs
        (.rel site.argumentSignatures) :=
    congrArg ConcreteElaboration.WireContext.sigs sourceScopeVisible ▸
      sourceScopeHead
  have sourceOuterHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val
          (sourceOuter.extend (source.val.wires wire).scope).ids
          sourceOuterHead =
        wire := by
    unfold sourceOuterHead
    exact
      (origin_transport_forward sourceScopeVisible
        sourceScopeHead).trans sourceScopeHeadOrigin
  have sourceRelativeNodup : sourceRelative.visible.ids.Nodup := by
    rw [sourceRelativeVisible]
    exact site_visible_nodup site.frame
  have targetRelativeNodup : targetRelative.visible.ids.Nodup := by
    rw [targetRelativeVisible']
    exact site_visible_nodup targetSite
  have rootProvenanceAtNode :
      ErasureFrameProvenance source site.node
        (source.val.nodes site.node).region
        (source.val.regionCount + 1) empty source.val.root
        site.frame.frame rootTargetFrame := by
    simpa [site.node_data] using rootProvenance
  have rootScope :
      source.val.Encloses source.val.root
        (source.val.wires wire).scope :=
    of_decide_eq_true
      ((List.all_eq_true.mp source.property.all_regions_reach_root)
        (source.val.wires wire).scope
        (Data.Finite.mem_allFin (source.val.wires wire).scope))
  have enclosesNode :
      source.val.Encloses (source.val.wires wire).scope
        (source.val.nodes site.node).region := by
    simpa [site.node_data] using encloses
  obtain ⟨aboveReceipt, sourceStoppedGenerated, targetStoppedGenerated⟩ :=
    rootProvenanceAtNode.aboveScope erasure.candidate_wellFormed
      (source.val.wires wire).scope rootScope enclosesNode
  let stoppedSourceScope :
      SiteCompilation source (source.val.wires wire).scope :=
    SiteCompilation.ofFrame aboveReceipt.sourceStopped (by
      simpa [empty, ConcreteElaboration.WireContext.empty] using
        sourceStoppedGenerated)
  have sourceScopeExact : stoppedSourceScope = sourceScope :=
    SiteCompilation.unique stoppedSourceScope sourceScope
  let stoppedTargetScope :
      SiteCompilation target
        (targetRegion source site.node (source.val.wires wire).scope) :=
    SiteCompilation.ofFrame aboveReceipt.targetStopped (by
      simpa [target, empty, ConcreteElaboration.WireContext.empty,
        targetRegion_eq] using targetStoppedGenerated)
  have targetScopeExact : stoppedTargetScope = targetScope :=
    SiteCompilation.unique stoppedTargetScope targetScope
  let stoppedSourceCanonical :
      SiteCompilation.AboveScopeDecomposition stoppedSourceScope :=
    {
      siteOuter := aboveReceipt.sourceSiteOuter
      above := aboveReceipt.sourceAbove
      visibleExact := aboveReceipt.sourceStoppedVisible
      contextDecomposition := aboveReceipt.sourceDecomposition
    }
  let sourceCanonical :
      SiteCompilation.AboveScopeDecomposition sourceScope :=
    reindexAboveScopeDecomposition sourceScopeExact stoppedSourceCanonical
  let stoppedTargetCanonical :
      SiteCompilation.AboveScopeDecomposition stoppedTargetScope :=
    {
      siteOuter :=
        targetContext source site.node aboveReceipt.sourceSiteOuter
      above := aboveReceipt.targetAbove
      visibleExact := aboveReceipt.targetStoppedVisible
      contextDecomposition := aboveReceipt.targetDecomposition
    }
  let targetCanonical :
      SiteCompilation.AboveScopeDecomposition targetScope :=
    reindexAboveScopeDecomposition targetScopeExact stoppedTargetCanonical
  have sourceOuterExact :
      sourceCanonical.siteOuter = aboveReceipt.sourceSiteOuter := by
    simpa [sourceCanonical, stoppedSourceCanonical] using
      (reindexAboveScopeDecomposition_siteOuter sourceScopeExact
        stoppedSourceCanonical)
  have targetOuterRawExact :
      targetCanonical.siteOuter =
        targetContext source site.node aboveReceipt.sourceSiteOuter := by
    simpa [targetCanonical, stoppedTargetCanonical] using
      (reindexAboveScopeDecomposition_siteOuter targetScopeExact
        stoppedTargetCanonical)
  have sourceAboveExact :
      congrArg ConcreteElaboration.WireContext.sigs sourceOuterExact ▸
          sourceCanonical.above =
        aboveReceipt.sourceAbove := by
    have proofExact :
        sourceOuterExact =
          reindexAboveScopeDecomposition_siteOuter sourceScopeExact
            stoppedSourceCanonical :=
      Subsingleton.elim _ _
    rw [proofExact]
    exact
      reindexAboveScopeDecomposition_above sourceScopeExact
        stoppedSourceCanonical
  have targetAboveRawExact :
      congrArg ConcreteElaboration.WireContext.sigs targetOuterRawExact ▸
          targetCanonical.above =
        aboveReceipt.targetAbove := by
    have proofExact :
        targetOuterRawExact =
          reindexAboveScopeDecomposition_siteOuter targetScopeExact
            stoppedTargetCanonical :=
      Subsingleton.elim _ _
    rw [proofExact]
    exact
      reindexAboveScopeDecomposition_above targetScopeExact
        stoppedTargetCanonical
  let outerProjection :
      WireRenaming sourceCanonical.siteOuter.sigs
        targetCanonical.siteOuter.sigs :=
    reindexWireRenaming
      (congrArg ConcreteElaboration.WireContext.sigs sourceOuterExact)
      (congrArg ConcreteElaboration.WireContext.sigs targetOuterRawExact)
      (contextRenaming source site.node aboveReceipt.sourceSiteOuter)
  have visibleExtendsOuter :
      ∀ {signature : Sig}
        (value : Var sourceCanonical.siteOuter.sigs signature),
        scopeMap (scopeEmbedOuter sourceCanonical value) =
          scopeEmbedOuter targetCanonical
            (outerProjection value) := by
    intro signature value
    apply
      InsertionCompilation.NaturalityInternal.origin_injective target.val
        targetScope.frame.visible.ids
        (site_visible_nodup targetScope)
    unfold scopeMap outerProjection
    rw [origin_transport_renaming scopeTargetVisible
      (contextRenaming source site.node sourceScope.frame.visible)
      (scopeEmbedOuter sourceCanonical value)]
    rw [contextRenaming_action, scopeEmbedOuter_origin,
      scopeEmbedOuter_origin]
    unfold reindexWireRenaming
    rw [origin_transport targetOuterRawExact, contextRenaming_action,
      origin_transport_forward sourceOuterExact]
  refine
    ⟨{
      sourceScope := sourceScope
      targetSite :=
        targetRegion source site.node (source.val.wires wire).scope
      targetSite_eq := by
        symm
        simpa [target] using targetWire_scope source site.node wire
      targetScope := targetScope
      sourceCanonical := sourceCanonical
      targetCanonical := targetCanonical
      outerProjection := outerProjection
      visibleProjection := scopeMap
      visibleExtendsOuter := visibleExtendsOuter
      visibleMapsWire := scopeMapWire
      body := ?_
      composable := by
        have outerMapEquality :
            (fun (pre : PreModel.{u}) (env : Env pre []) =>
              Env.comp env
                (contextRenaming source site.node
                  (ConcreteElaboration.WireContext.empty source.val))) =
            (fun (pre : PreModel.{u}) (env : Env pre []) => env) := by
          funext pre env sig value
          nomatch value
        rw [← outerMapEquality]
        exact
          reindexComposableSemanticZipperHoles
            (congrArg ConcreteElaboration.WireContext.sigs
              sourceOuterExact)
            (congrArg ConcreteElaboration.WireContext.sigs
              targetOuterRawExact)
            sourceCanonical.above aboveReceipt.sourceAbove
            sourceAboveExact targetCanonical.above
            aboveReceipt.targetAbove targetAboveRawExact
            (fun (pre : PreModel.{u}) (env : Env pre []) =>
              Env.comp env
                (contextRenaming source site.node
                  (ConcreteElaboration.WireContext.empty source.val)))
            (contextRenaming source site.node
              aboveReceipt.sourceSiteOuter)
            aboveReceipt.composable
    }⟩
  intro pre definitionEnv targetEnv universal
  have sourceLiftHeadExact :
      DiagramContext.liftOuter pairedInner.sourceInner sourceOuterHead =
        removedHead := by
    by_cases coScoped :
        (source.val.wires wire).scope = site.region
    · have sourceGeneratedAtScope :
          compileRegionFrame? definitions source.val
              (source.val.wires wire).scope fuel
              (source.val.wires wire).scope sourceOuter =
            some sourceRelative := by
        simpa only [coScoped] using sourceRelativeGenerated
      rw [sourceInnerExact]
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          source.val sourceRelative.visible.ids sourceRelativeNodup
      rw [
        compileRegionFrame_site_inner_liftOuter_origin definitions
          source.val (source.val.wires wire).scope fuel sourceOuter
          sourceRelative sourceInner sourceGeneratedAtScope
          sourceRelativeDecomposition sourceOuterHead,
        sourceOuterHeadOrigin, removedHeadOrigin]
    · rw [sourceInnerExact]
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          source.val sourceRelative.visible.ids sourceRelativeNodup
      rw [
        compileRegionFrame?_strict_inner_liftOuter_origin definitions
          source.val site.region fuel (source.val.wires wire).scope
          sourceOuter sourceRelative sourceInner coScoped
          sourceRelativeGenerated sourceRelativeDecomposition,
        sourceOuterHeadOrigin, removedHeadOrigin]
  have targetLiftHeadExact :
      DiagramContext.liftOuter pairedInner.targetInner
          (extendedContextRenaming source site.node sourceOuter
            (source.val.wires wire).scope sourceOuterHead) =
        erasureVisibleRenaming site.node sourceRelative
          targetRelativeVisible removedHead := by
    by_cases coScoped :
        (source.val.wires wire).scope = site.region
    · have targetCoScoped :
          targetRegion source site.node (source.val.wires wire).scope =
            targetRegion source site.node site.region :=
        congrArg (targetRegion source site.node) coScoped
      have targetGeneratedAtScope :
          compileRegionFrame? definitions target.val
              (targetRegion source site.node
                (source.val.wires wire).scope)
              fuel
              (targetRegion source site.node
                (source.val.wires wire).scope)
              (targetContext source site.node sourceOuter) =
            some targetRelative := by
        simpa only [targetCoScoped] using provenance.targetGenerated
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          target.val targetRelative.visible.ids targetRelativeNodup
      calc
        _ =
            ConcreteElaboration.WireContext.origin target.val
              ((targetContext source site.node sourceOuter).extend
                (targetRegion source site.node
                  (source.val.wires wire).scope)).ids
              (extendedContextRenaming source site.node sourceOuter
                (source.val.wires wire).scope sourceOuterHead) := by
              simpa [target] using
                compileRegionFrame_site_inner_liftOuter_origin
                  definitions target.val
                  (targetRegion source site.node
                    (source.val.wires wire).scope)
                  fuel (targetContext source site.node sourceOuter)
                  targetRelative pairedInner.targetInner
                  targetGeneratedAtScope targetRelativeDecomposition
                  (extendedContextRenaming source site.node sourceOuter
                    (source.val.wires wire).scope sourceOuterHead)
        _ = targetWire source site.node wire := by
              simpa [target] using
                (extendedContextRenaming_origin source site.node sourceOuter
                  (source.val.wires wire).scope sourceOuterHead).trans
                  (congrArg (targetWire source site.node)
                    sourceOuterHeadOrigin)
        _ =
            ConcreteElaboration.WireContext.origin target.val
              targetRelative.visible.ids
              (erasureVisibleRenaming site.node sourceRelative
                targetRelativeVisible removedHead) := by
              symm
              simpa [target] using
                (erasureVisibleRenaming_origin site.node sourceRelative
                  targetRelativeVisible removedHead).trans
                  (congrArg (targetWire source site.node)
                    removedHeadOrigin)
    · rw [← sourceLiftHeadExact]
      exact
        pairedInner.liftOuter_erasureVisibleRenaming site.node site.region
          (source.val.wires wire).scope fuel sourceOuter sourceRelative
          targetRelative coScoped sourceRelativeGenerated
          (by simpa [target] using provenance.targetGenerated)
          targetRelativeVisible targetRelativeNodup sourceOuterHead

  let fixedTargetEnv :
      Env pre
        ((targetContext source site.node sourceOuter).extend
          (targetRegion source site.node
            (source.val.wires wire).scope)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs
        targetScopeVisible ▸
      targetEnv
  have sourceEnvironmentExact :
      Env.comp fixedTargetEnv
          (extendedContextRenaming source site.node sourceOuter
            (source.val.wires wire).scope) =
        congrArg ConcreteElaboration.WireContext.sigs
            sourceScopeVisible ▸
          Env.comp targetEnv scopeMap := by
    exact
      scope_environment_coherence source site.node sourceOuter
        (source.val.wires wire).scope sourceScope.frame.visible
        targetScope.frame.visible sourceScopeVisible targetScopeVisible
        scopeTargetVisible pre targetEnv
  have localLaw :
      ∀ descendant : Env pre targetRelative.visible.sigs,
        DiagramContext.PreservesOuter pairedInner.targetInner
            fixedTargetEnv descendant →
          (denoteRegion pre definitionEnv descendant
              targetRelative.siteBody ↔
            denoteRegion pre definitionEnv
              (Env.comp descendant
                (erasureVisibleRenaming site.node sourceRelative
                  targetRelativeVisible))
              sourceRelative.siteBody) := by
    intro descendant preserves
    have targetHeadValue :
        descendant (.rel site.argumentSignatures)
            (erasureVisibleRenaming site.node sourceRelative
              targetRelativeVisible removedHead) =
          targetEnv (.rel site.argumentSignatures)
            (scopeMap sourceScopeHead) := by
      calc
        _ =
            descendant (.rel site.argumentSignatures)
              (DiagramContext.liftOuter pairedInner.targetInner
                (extendedContextRenaming source site.node sourceOuter
                  (source.val.wires wire).scope sourceOuterHead)) := by
              rw [targetLiftHeadExact]
        _ =
            fixedTargetEnv (.rel site.argumentSignatures)
              (extendedContextRenaming source site.node sourceOuter
                (source.val.wires wire).scope sourceOuterHead) := by
              exact
                congrFun
                  (congrFun preserves
                    (.rel site.argumentSignatures))
                  (extendedContextRenaming source site.node sourceOuter
                    (source.val.wires wire).scope sourceOuterHead)
        _ =
            (congrArg ConcreteElaboration.WireContext.sigs
                  sourceScopeVisible ▸
              Env.comp targetEnv scopeMap)
                (.rel site.argumentSignatures) sourceOuterHead := by
              exact
                congrFun
                  (congrFun sourceEnvironmentExact
                    (.rel site.argumentSignatures))
                  sourceOuterHead
        _ =
            targetEnv (.rel site.argumentSignatures)
              (scopeMap sourceScopeHead) := by
              unfold sourceOuterHead
              exact
                transported_environment_apply sourceScopeVisible
                  pre (Env.comp targetEnv scopeMap) sourceScopeHead
    have targetScopeHeadOrigin :
        ConcreteElaboration.WireContext.origin target.val
            targetScope.frame.visible.ids (scopeMap sourceScopeHead) =
          targetWire source site.node wire :=
      scopeMapWire sourceScopeHead sourceScopeHeadOrigin
    have atomHolds :
        denoteItem pre definitionEnv
          (Env.comp descendant
            (erasureVisibleRenaming site.node sourceRelative
              targetRelativeVisible))
          (.atom removedHead removedArguments) := by
      change
        pre.apply
          (descendant (.rel site.argumentSignatures)
            (erasureVisibleRenaming site.node sourceRelative
              targetRelativeVisible removedHead))
          (Vars.denote
            (Env.comp descendant
              (erasureVisibleRenaming site.node sourceRelative
                targetRelativeVisible))
            removedArguments)
      rw [targetHeadValue]
      exact
        universal site.argumentSignatures (scopeMap sourceScopeHead)
          targetScopeHeadOrigin
          (Vars.denote
            (Env.comp descendant
              (erasureVisibleRenaming site.node sourceRelative
                targetRelativeVisible))
            removedArguments)
    have localAt :
        LocalReplacementAt source site.node sourceRelative.visible
          targetRelative.visible targetRelativeVisible
          (blank : Region definitions targetRelative.visible.sigs)
          (.atom removedHead removedArguments) pre definitionEnv
          descendant := by
      unfold LocalReplacementAt
      have environments :=
        env_comp_cast_renaming
          (congrArg ConcreteElaboration.WireContext.sigs
            targetRelativeVisible.symm)
          (contextRenaming source site.node sourceRelative.visible)
          pre descendant
      constructor
      · intro _blankHolds
        exact environments ▸ atomHolds
      · intro _atomHolds
        exact denoteRegion_blank pre definitionEnv descendant
    have bodyEquivalence :=
      bodyLaw (.atom removedHead removedArguments) removedCompiled pre
        definitionEnv
        (blank : Region definitions targetRelative.visible.sigs)
        descendant localAt
    simpa using bodyEquivalence
  have filledEquivalence :=
    innerZipper.equivalence pre definitionEnv sourceRelative.siteBody
      targetRelative.siteBody fixedTargetEnv localLaw
  have targetTransport :=
    denoteRegion_transport
      (congrArg ConcreteElaboration.WireContext.sigs targetScopeVisible)
      pre definitionEnv targetEnv targetScope.frame.siteBody
  have sourceTransport :=
    denoteRegion_transport
      (congrArg ConcreteElaboration.WireContext.sigs sourceScopeVisible)
      pre definitionEnv (Env.comp targetEnv scopeMap)
      sourceScope.frame.siteBody
  rw [targetScopeBody] at targetTransport
  rw [sourceScopeBody] at sourceTransport
  rw [sourceInnerExact] at filledEquivalence
  have sourceDenotationExact :
      denoteRegion pre definitionEnv
          (Env.comp fixedTargetEnv
            (extendedContextRenaming source site.node sourceOuter
              (source.val.wires wire).scope))
          (sourceInner.fill sourceRelative.siteBody) =
        denoteRegion pre definitionEnv
          (congrArg ConcreteElaboration.WireContext.sigs
              sourceScopeVisible ▸
            Env.comp targetEnv scopeMap)
          (sourceInner.fill sourceRelative.siteBody) :=
    congrArg
      (fun env =>
        denoteRegion pre definitionEnv env
          (sourceInner.fill sourceRelative.siteBody))
      sourceEnvironmentExact
  have normalizedFilled :
      denoteRegion pre definitionEnv fixedTargetEnv
          (pairedInner.targetInner.fill targetRelative.siteBody) ↔
        denoteRegion pre definitionEnv
          (congrArg ConcreteElaboration.WireContext.sigs
              sourceScopeVisible ▸
            Env.comp targetEnv scopeMap)
          (sourceInner.fill sourceRelative.siteBody) := by
    constructor
    · intro targetHolds
      exact sourceDenotationExact ▸ filledEquivalence.mp targetHolds
    · intro sourceHolds
      exact filledEquivalence.mpr
        (sourceDenotationExact.symm ▸ sourceHolds)
  exact targetTransport.trans (normalizedFilled.trans sourceTransport.symm)

private noncomputable def canonical_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node) :
    let target : CheckedDiagram definitions :=
      ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source site.node,
        erasure.candidate_wellFormed⟩
    UniversalOuterTransport.{u} source wire target
      (targetWire source site.node wire) :=
  Classical.choice (canonical_scope_transport site erasure)

private noncomputable def normalize_outer_erasure
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node)
    (canonicalTransport :
      let canonical : CheckedDiagram definitions :=
        ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source site.node,
          erasure.candidate_wellFormed⟩
      UniversalOuterTransport.{u} source wire canonical
        (targetWire source site.node wire)) :
    UniversalOuterTransport.{u} source wire erasure.target
      (erasure.wireImage wire) := by
  let canonical : CheckedDiagram definitions :=
    ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source site.node,
      erasure.candidate_wellFormed⟩
  have targetExact : canonical = erasure.target := by
    apply Subtype.ext
    exact erasure.generated.symm
  change
    UniversalOuterTransport.{u} source wire canonical
      (targetWire source site.node wire) at canonicalTransport
  refine
    cast_outer_transport
      (leftWire := targetWire source site.node wire)
      (rightWire := erasure.wireImage wire)
      targetExact ?_ canonicalTransport
  · have counts :
        canonical.val.wireCount = erasure.target.val.wireCount :=
      congrArg ConcreteDiagram.wireCount
        (congrArg Subtype.val targetExact)
    exact fin_heq_of_val_eq counts _ _ rfl

/-- Public one-step transport normalized to the exact checked erasure target. -/
theorem universal_scope_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node) :
    UniversalScopeTransport.{u} source wire erasure.target
      (erasure.wireImage wire) :=
  (normalize_outer_erasure site erasure
    (canonical_transport site erasure)).toScopeTransport

/-- Public one-step constructor-preserving transport above the acted scope. -/
noncomputable def universal_outer_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (erasure : CheckedErasure source site.node) :
    UniversalOuterTransport.{u} source wire erasure.target
      (erasure.wireImage wire) :=
  normalize_outer_erasure site erasure
    (canonical_transport site erasure)

end AppliedSite

end ConcreteWirePrimitive

namespace WirePrimitive.AppliedSiteErasure.Result

open ConcreteWirePrimitive

/--
The sealed all-applied-site trace composes the constructor-preserving prefix
strictly above the acted binder scope.
-/
private theorem universal_outer_transport_nonempty
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : AppliedSiteErasure.Result source wire) :
    Nonempty
      (UniversalOuterTransport.{u} source wire result.target
        result.targetWire) :=
  result.inductionOn
    (fun source wire target targetWire =>
      Nonempty
        (UniversalOuterTransport.{u} source wire target targetWire))
    (fun source wire _empty =>
      ⟨UniversalOuterTransport.identity source wire⟩)
    (fun {source} {wire} site erasure {target} {targetWire} tail =>
      ⟨UniversalOuterTransport.compose
          (ConcreteWirePrimitive.AppliedSite.universal_outer_transport
            site erasure)
          (Classical.choice tail)⟩)

noncomputable def universal_outer_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : AppliedSiteErasure.Result source wire) :
    UniversalOuterTransport.{u} source wire result.target
      result.targetWire :=
  Classical.choice (universal_outer_transport_nonempty result)

/--
The universal scope law is the binder-local projection of the one coherent
constructor-preserving trace.
-/
theorem universal_scope_transport
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : AppliedSiteErasure.Result source wire) :
    UniversalScopeTransport.{u} source wire result.target
      result.targetWire :=
  (universal_outer_transport result).toScopeTransport

end WirePrimitive.AppliedSiteErasure.Result

end VisualProof
