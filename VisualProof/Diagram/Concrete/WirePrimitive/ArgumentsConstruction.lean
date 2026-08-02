import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsConstructionCore

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

local notation "siteNodes" => argumentSiteNodes

/-- Opaque checked result shared by the seven argument transformations. -/
structure ArgumentResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  spec : ReplacementSpec source wire sites
  plan : ReplacementPlan source wire sites spec
  source_removed_exhausted :
    ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
      ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
        endpoint.node ∈ siteNodes sites
  generated : checked.val = replacementCandidate plan
  targetWire : checked.val.WireId
  targetWire_exact :
    targetWire =
      Internal.checkedWire generated (replacementCandidateWire plan)
  private target_sites : AllAppliedSites checked targetWire

namespace ArgumentResult

/-- The checker-produced target diagram. -/
def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    CheckedDiagram definitions :=
  result.checked

/-- The checker-selected target relation argument vector. -/
def targetArguments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List Sig :=
  result.spec.targetArguments

/-- Canonical image of a source region in the checked replacement.  Argument
replacement never deletes regions; the two explicit transports account only
for dense construction and checked-target indexing. -/
def regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated (retainedRegion source region)

/-- Argument replacement removes no region: its checked target has exactly
the source region carrier cardinality. -/
theorem regionCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    source.val.regionCount = result.checked.val.regionCount := by
  have generated := congrArg ConcreteDiagram.regionCount result.generated
  rw [generated]
  change source.val.regionCount = (replacementBase result.plan).regionCount
  unfold replacementBase Internal.batchRemovalCandidate
  change source.val.regionCount = (Internal.retainedRegions source []).length
  simpa [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
    congrArg List.length (Internal.retainedRegions_nil source)

/-- Canonical source-to-target region equivalence for every checked argument
replacement. -/
def regionEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Data.Finite.FiniteEquiv source.val.RegionId result.checked.val.RegionId :=
  finEquivOfEq result.regionCount_exact

/-- The construction-level `regionImage` is exactly the canonical region
equivalence, not a second region transport. -/
theorem regionImage_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.regionImage region = result.regionEquiv region := by
  apply Fin.ext
  unfold regionImage regionEquiv finEquivOfEq
  unfold Internal.checkedRegion
  change (retainedRegion source region).val = region.val
  unfold retainedRegion Internal.retainedRegionIndex
  have retainedExact := Internal.retainedRegions_nil source
  let sourcePosition : Fin source.val.regionsList.length :=
    Fin.cast (by
      simp [ConcreteDiagram.regionsList,
        Data.Finite.allFin_eq_finRange]) region
  let position : Fin (Internal.retainedRegions source []).length :=
    Fin.cast (congrArg List.length retainedExact).symm sourcePosition
  have getExact :
      (Internal.retainedRegions source []).get position = region := by
    rw [get_of_list_eq retainedExact sourcePosition]
    exact allFin_get region
  have indexExact : retainedRegion source region = position := by
    unfold retainedRegion Internal.retainedRegionIndex
    rw [← getExact]
    exact DenseList.index_get _
      (by rw [retainedExact]; exact Data.Finite.allFin_nodup _)
      position
  exact congrArg Fin.val indexExact

/-- The canonical region equivalence preserves and reflects the complete
checked enclosure order. -/
theorem regionImage_encloses
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer inner : source.val.RegionId) :
    result.checked.val.Encloses
        (result.regionImage outer) (result.regionImage inner) ↔
      source.val.Encloses outer inner := by
  unfold regionImage
  rw [Internal.checkedRegion_encloses]
  unfold replacementCandidate
  rw [Internal.assigned_encloses]
  exact Internal.replacementSkeleton_encloses result.plan outer inner

/-- The target root is the canonical image of the source root. -/
theorem targetRoot_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  calc
    result.checked.val.root =
        Internal.checkedRegion result.generated
          (replacementCandidate result.plan).root :=
      Internal.checkedRoot_transport result.generated
    _ = Internal.checkedRegion result.generated
          (retainedRegion source source.val.root) := by
      congr 1

/-- Region constructors and cut parents are transported exactly by the
canonical region equivalence. -/
theorem regionImage_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionEquiv region) =
      (source.val.regions region).rename result.regionEquiv := by
  have skeletonData :
      (replacementSkeleton result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source) := by
    change
      (replacementBase result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source)
    unfold replacementBase
    rw [retainedRegion_eq_noRegionRemovalEquiv,
      show
        (Internal.batchRemovalCandidate result.plan.removal).regions
            (Internal.noRegionRemovalEquiv source region) =
          Internal.batchRegionTable result.plan.removal
            (Internal.noRegionRemovalEquiv source region) from rfl,
      Internal.batchRegionTable_noRegions]
  have candidateData :
      (replacementCandidate result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source) := by
    exact skeletonData
  rw [← result.regionImage_exact]
  unfold regionImage
  change
    result.checked.val.regions
        (Internal.checkedRegionEquiv result.generated
          (retainedRegion source region)) =
      (source.val.regions region).rename result.regionEquiv
  rw [Internal.checkedRegion_data_equiv, candidateData]
  cases data : source.val.regions region with
  | sheet => rfl
  | cut parent =>
      simp only [CRegion.rename]
      congr 1
      rw [← retainedRegion_eq_noRegionRemovalEquiv]
      exact result.regionImage_exact parent

/-- Canonical checked image of a source node retained by argument replacement. -/
def retainedNodeImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd result.sites.sites.length
      (Internal.retainedNodeIndex source (siteNodes result.sites) node (by
        unfold Internal.retainedNodes
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)))

/-- Retained node constructors and payloads are transported exactly through
the canonical region equivalence. -/
theorem retainedNodeImage_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (source.val.nodes node).rename result.regionEquiv := by
  unfold retainedNodeImage
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node]
  let member : node ∈ Internal.retainedNodes source
      (siteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩
  let retainedIndex :=
    Internal.retainedNodeIndex source (siteNodes result.sites) node member
  simp only [replacementSkeleton, Fin.addCases_left]
  change
    Internal.checkedNodeData result.generated
        (Internal.batchNodeTable result.plan.removal retainedIndex) =
      (source.val.nodes node).rename result.regionEquiv
  rw [Internal.batchNodeTable_noRegions]
  have sourceExact :
      Internal.sourceRetainedNode source (siteNodes result.sites)
          retainedIndex = node :=
    Internal.sourceRetainedNode_retainedNodeIndex source
      (siteNodes result.sites) node member
  rw [sourceExact]
  cases data : source.val.nodes node <;>
    simp only [CNode.rename, Internal.checkedNodeData]
  all_goals
    rw [← retainedRegion_eq_noRegionRemovalEquiv]
    congr 1
    exact result.regionImage_exact _

/-- Canonical checked node generated for one ordered source application. -/
def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (replacementNode result.plan site)

/-- Generated replacement-node payloads are exact, including their canonical
source-region images and checker-selected target argument vectors. -/
theorem targetNode_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.targetNode site) =
      .atom (result.regionImage (result.sites.sites.get site).region)
        result.targetArguments := by
  unfold targetNode regionImage targetArguments
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node, replacementSkeleton_replacementNode]
  rfl

/-- Canonical checked operation-local wire at one replacement-local index. -/
def targetLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (replacementCandidateLocalWire result.plan fresh)

/-- Source wires deleted by the simultaneous replacement, including its head. -/
def sourceRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List source.val.WireId :=
  wire :: result.spec.removedWires

/-- Canonical checked image of a source wire retained by argument replacement. -/
def retainedWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd (1 + result.spec.localCount)
      (Internal.retainedWireIndex source result.sourceRemovedWires sourceWire
        (by
          unfold Internal.retainedWires
          apply List.mem_filter.mpr
          exact ⟨Data.Finite.mem_allFin sourceWire,
            decide_eq_true retained⟩)))

/-- Retained wire signatures are unchanged. -/
theorem retainedWireImage_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
        (result.retainedWireImage sourceWire retained)).sig =
      (source.val.wires sourceWire).sig := by
  unfold retainedWireImage
  rw [Internal.checkedWire_signature_transport]
  unfold replacementCandidate
  rw [assigned_wire_signature,
    replacementSkeleton_retained_wire_signature]
  exact congrArg (fun candidate => (source.val.wires candidate).sig)
    (Internal.sourceRetainedWire_retainedWireIndex source
      result.sourceRemovedWires sourceWire (by
        unfold Internal.retainedWires
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin sourceWire,
          decide_eq_true retained⟩))

/-- Retained wire scopes are transported by the canonical region image. -/
theorem retainedWireImage_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
        (result.retainedWireImage sourceWire retained)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold retainedWireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  unfold replacementCandidate
  rw [assigned_wire_scope, replacementSkeleton_retained_wire_scope]
  simp only [sourceRemovedWires]
  rw [Internal.sourceRetainedWire_retainedWireIndex]

/-- Fresh target-local argument wires introduced by arity shift. -/
def targetLocalWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  (Data.Finite.allFin result.spec.localCount).map fun fresh =>
    Internal.checkedWire result.generated
      (replacementCandidateLocalWire result.plan fresh)

/-- Target wires deleted to expose the exact retained common core. -/
def targetRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  result.targetWire :: result.targetLocalWires

/-- Every accepted replacement consumes every applied end of the source. -/
theorem siteCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.sites.sites.length =
      (source.val.wires wire).endpoints.length :=
  result.sites.length

/-- The fresh replacement head has the checker-selected relation signature. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).sig =
      .rel result.targetArguments := by
  rw [result.targetWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  unfold replacementCandidate replacementCandidateWire
  rw [assigned_wire_signature]
  unfold replacementSkeleton replacementHeadWire
  simp only [Fin.addCases_right]
  rfl

/-- The fresh replacement head remains scoped at the exact image of the
source head's scope.  Argument replacement removes no regions, so this is the
construction-owned region transport used by semantic factorization. -/
theorem targetWire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).scope =
      Internal.checkedRegion result.generated
        (retainedRegion source (source.val.wires wire).scope) := by
  rw [result.targetWire_exact,
    Internal.checkedWire_scope_transport]
  unfold replacementCandidateWire replacementCandidate
  rw [assigned_wire_scope]
  exact congrArg (Internal.checkedRegion result.generated)
    (replacementSkeleton_head_wire_scope result.plan)

@[simp]
theorem targetWire_scope_regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).scope =
      result.regionImage (source.val.wires wire).scope :=
  result.targetWire_scope

/-- Generated replacement nodes stay at the exact images of their ordered
source application regions. -/
theorem targetNode_region
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    (result.checked.val.nodes (result.targetNode site)).region =
      result.regionImage (result.sites.sites.get site).region := by
  unfold targetNode regionImage
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node]
  exact replacementSkeleton_replacementNode result.plan site ▸ rfl

/-- Every operation-local argument wire has its construction-selected
signature in the checked target. -/
theorem targetLocalWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    (result.checked.val.wires (result.targetLocalWire fresh)).sig =
      result.spec.localSignature fresh := by
  unfold targetLocalWire
  rw [Internal.checkedWire_signature_transport]
  unfold replacementCandidate
  rw [assigned_wire_signature]
  exact Internal.replacementSkeleton_local_wire_signature result.plan fresh

/-- Every operation-local argument wire is bound at the exact checked image
of its construction-selected source scope. -/
theorem targetLocalWire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    (result.checked.val.wires (result.targetLocalWire fresh)).scope =
      result.regionImage (result.spec.localScope fresh) := by
  unfold targetLocalWire regionImage
  rw [Internal.checkedWire_scope_transport]
  unfold replacementCandidate
  rw [assigned_wire_scope]
  exact congrArg (Internal.checkedRegion result.generated)
    (replacementSkeleton_local_wire_scope result.plan fresh)

/-- The exhaustive generated target sites retained by every accepted argument
replacement. -/
def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    AllAppliedSites result.checked result.targetWire :=
  result.target_sites

end ArgumentResult

def replaceAppliedEnds
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ siteNodes sites) :
    Except ArgumentError (ArgumentResult source wire) := by
  match Internal.checkBatchRemovalPlan?
      source [] (siteNodes sites) (wire :: spec.removedWires) with
  | none => exact .error .invalidRemoval
  | some removal =>
      let plan : ReplacementPlan source wire sites spec := ⟨removal⟩
      let candidate := replacementCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error => exact .error (.malformedTarget error)
      | .ok checked =>
          have generated : checked.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          let targetWire :=
            Internal.checkedWire generated (replacementCandidateWire plan)
          match checkAllAppliedSites checked targetWire with
          | none => exact .error .nonAppliedEndpoint
          | some targetSites =>
              exact .ok
                (ArgumentResult.mk sites checked spec plan
                  sourceRemovedExhausted generated targetWire rfl targetSites)

theorem replaceAppliedEnds_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (valid : ReplacementValid spec) :
    ∃ result,
      replaceAppliedEnds source wire sites spec valid.removedExhausted =
        .ok result := by
  obtain ⟨removal, removalAccepted⟩ :=
    Internal.checkBatchRemovalPlan_noRegions source
      (siteNodes sites) (wire :: spec.removedWires)
  let plan : ReplacementPlan source wire sites spec := ⟨removal⟩
  have wellFormed :
      (replacementCandidate plan).WellFormed definitions :=
    Internal.replacementCandidate_wellFormed plan valid
  unfold replaceAppliedEnds
  rw [removalAccepted]
  simp only
  split
  · rename_i error rejected
    have accepted := ConcreteDiagram.checkWellFormed_complete wellFormed
    rw [rejected] at accepted
    contradiction
  · rename_i checked accepted
    have generated : checked.val = replacementCandidate plan :=
      ConcreteDiagram.checkWellFormed_preserves_input accepted
    obtain ⟨targetSites, targetSitesAccepted⟩ :=
      Internal.checkedReplacementHead_sites_complete plan valid checked generated
    rw [targetSitesAccepted]
    exact ⟨_, rfl⟩

theorem replaceAppliedEnds_complete_with_targetSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (valid : ReplacementValid spec) :
    ∃ result,
      replaceAppliedEnds source wire sites spec valid.removedExhausted =
          .ok result ∧
        ∃ targetSites,
          checkAllAppliedSites result.checked result.targetWire =
            some targetSites := by
  obtain ⟨result, accepted⟩ :=
    replaceAppliedEnds_complete source wire sites spec valid
  refine ⟨result, accepted, result.targetSites, ?_⟩
  exact result.targetSites.checked

/-- A successful replacement retains the caller's exact ordered source-wire
removal list; the checker does not substitute a second operation model. -/
theorem replaceAppliedEnds_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.sourceRemovedWires = wire :: spec.removedWires := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the caller's exact target argument
vector.  Later semantic receipts may use this construction-owned equation
without reopening the opaque result or rediscovering the replacement spec. -/
theorem replaceAppliedEnds_targetArguments_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.targetArguments = spec.targetArguments := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the exact exhaustive source-site
receipt supplied to the construction. -/
theorem replaceAppliedEnds_sites_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.sites = sites := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

def checkedArgumentSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (AllAppliedSites source wire) :=
  match checkAllAppliedSites source wire with
  | none => .error .nonAppliedEndpoint
  | some sites => .ok sites

def checkedRelationArguments
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (List Sig) :=
  match relationArguments? source wire with
  | none => .error .expectedRelation
  | some arguments => .ok arguments

def existingReferences
    {source : CheckedDiagram definitions}
    {localCount : Nat}
    (arguments : List source.val.WireId) :
    List (ArgumentReference source localCount) :=
  arguments.map .existing

def arityShiftSpec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig) : ReplacementSpec source wire sites :=
  { targetArguments := relationArguments ++ [newArgument]
    removedWires := []
    localCount := sites.sites.length
    localSignature := fun _ => newArgument
    localScope := fun site => (sites.sites.get site).region
    arguments := fun site =>
      existingReferences (sites.sites.get site).arguments ++
        [.local site] }

theorem appliedSite_arguments_eq_relationArguments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (relationArguments : List Sig)
    (sourceSignature : (source.val.wires wire).sig = .rel relationArguments)
    (site : AppliedSite source wire) :
    site.argumentSignatures = relationArguments := by
  exact Sig.rel.inj (site.head_signature.symm.trans sourceSignature)

theorem allAppliedSites_removed_exhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires wire).endpoints) :
    endpoint.node ∈ siteNodes sites := by
  rw [← sites.exhaustive] at member
  rcases List.mem_map.mp member with ⟨site, siteMember, endpointExact⟩
  unfold argumentSiteNodes
  apply List.mem_map.mpr
  refine ⟨site, siteMember, ?_⟩
  exact congrArg CEndpoint.node endpointExact


end ConcreteWirePrimitive

end VisualProof
