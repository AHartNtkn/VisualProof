import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsConstruction

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

private theorem map_allFin_add
    (m n : Nat) (f : Fin (m + n) → α) :
    (Data.Finite.allFin (m + n)).map f =
      (Data.Finite.allFin m).map
          (fun index => f (Fin.castAdd n index)) ++
        (Data.Finite.allFin n).map
          (fun index => f (Fin.natAdd m index)) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn, List.map_ofFn, List.map_ofFn, List.ofFn_add]
  congr 1

private theorem allFin_add (m n : Nat) :
    Data.Finite.allFin (m + n) =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) := by
  have split := map_allFin_add m n (fun value => value)
  change
    (Data.Finite.allFin (m + n)).map id =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) at split
  simpa only [List.map_id] using split

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem map_map_apply
    (values : List α) (first : α → β) (second : β → γ) :
    (values.map first).map second =
      values.map (fun value => second (first value)) := by
  induction values with
  | nil => rfl
  | cons head tail induction => simp [induction]

private theorem map_allFin_finEquivOfEq
    {left right : Nat}
    (exact : left = right) :
    (Data.Finite.allFin left).map (finEquivOfEq exact) =
      Data.Finite.allFin right := by
  subst right
  apply List.ext_get
  · simp
  · intro position leftBound rightBound
    apply Fin.ext
    simp [Data.Finite.allFin_eq_finRange, finEquivOfEq]

/-- Batch removal preserves the exact order of every retained local wire.
The left side uses the dense target identifiers, while the right side is the
source local context with precisely the removed identifiers filtered out. -/
theorem batchRemovalCandidate_wiresAt_sources
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : Internal.BatchRemovalPlan source [] removedNodes removedWires)
    (region : source.val.RegionId) :
    ((Internal.batchRemovalCandidate plan).wiresAt
        (Internal.noRegionRemovalEquiv source region)).map
          (Internal.sourceRetainedWire source removedWires) =
      (source.val.wiresAt region).filter
        (fun wire => decide (wire ∉ removedWires)) := by
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  have targetFilter :
      (Data.Finite.allFin
        (Internal.batchRemovalCandidate plan).wireCount).filter
          (fun wire =>
            ((Internal.batchRemovalCandidate plan).wires wire).scope ==
              Internal.noRegionRemovalEquiv source region) =
        (Data.Finite.allFin
          (Internal.batchRemovalCandidate plan).wireCount).filter
          ((fun candidate =>
            (source.val.wires candidate).scope == region) ∘
              Internal.sourceRetainedWire source removedWires) := by
    apply List.filter_congr
    intro retained _member
    apply decide_eq_decide.mpr
    constructor
    · intro same
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← same]
      exact Internal.batchRemovalCandidate_wire_scope_noRegions
        plan retained
    · intro same
      rw [Internal.batchRemovalCandidate_wire_scope_noRegions, same]
  rw [targetFilter, ← List.filter_map]
  have allSources :
      (Data.Finite.allFin
          (Internal.batchRemovalCandidate plan).wireCount).map
          (Internal.sourceRetainedWire source removedWires) =
        Internal.retainedWires source removedWires := by
    simpa [Internal.batchRemovalCandidate] using
      map_get_allFin (Internal.retainedWires source removedWires)
  rw [allSources]
  simp only [Internal.retainedWires, List.filter_filter]
  apply List.filter_congr
  intro candidate _member
  simpa using
    (Bool.and_comm
      ((source.val.wires candidate).scope == region)
      (decide (candidate ∉ removedWires)))

/-- Batch removal preserves the exact order of every retained local node. -/
theorem batchRemovalCandidate_nodesAt_sources
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : Internal.BatchRemovalPlan source [] removedNodes removedWires)
    (region : source.val.RegionId) :
    ((Internal.batchRemovalCandidate plan).nodesAt
        (Internal.noRegionRemovalEquiv source region)).map
          (Internal.sourceRetainedNode source removedNodes) =
      (source.val.nodesAt region).filter
        (fun node => decide (node ∉ removedNodes)) := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  have targetFilter :
      (Data.Finite.allFin
        (Internal.batchRemovalCandidate plan).nodeCount).filter
          (fun node =>
            ((Internal.batchRemovalCandidate plan).nodes node).region ==
              Internal.noRegionRemovalEquiv source region) =
        (Data.Finite.allFin
          (Internal.batchRemovalCandidate plan).nodeCount).filter
          ((fun candidate =>
            (source.val.nodes candidate).region == region) ∘
              Internal.sourceRetainedNode source removedNodes) := by
    apply List.filter_congr
    intro retained _member
    apply decide_eq_decide.mpr
    constructor
    · intro same
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← same]
      exact (Internal.batchRemovalCandidate_node_region_noRegions
        plan retained).symm
    · intro same
      rw [Internal.batchRemovalCandidate_node_region_noRegions, same]
  rw [targetFilter, ← List.filter_map]
  have allSources :
      (Data.Finite.allFin
          (Internal.batchRemovalCandidate plan).nodeCount).map
          (Internal.sourceRetainedNode source removedNodes) =
        Internal.retainedNodes source removedNodes := by
    simpa [Internal.batchRemovalCandidate] using
      map_get_allFin (Internal.retainedNodes source removedNodes)
  rw [allSources]
  simp only [Internal.retainedNodes, List.filter_filter]
  apply List.filter_congr
  intro candidate _member
  simpa using
    (Bool.and_comm
      ((source.val.nodes candidate).region == region)
      (decide (candidate ∉ removedNodes)))

/-- Argument replacement appends exactly one head and the operation-local
wires after the retained common-core wire block. -/
theorem replacementCandidate_wireCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementCandidate plan).wireCount =
      (replacementBase plan).wireCount + (1 + spec.localCount) := rfl

/-- Argument replacement retains source nodes in dense order and appends one
replacement node per ordered applied site. -/
theorem replacementCandidate_nodesAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (region : source.val.RegionId) :
    (replacementCandidate plan).nodesAt (retainedRegion source region) =
      ((replacementBase plan).nodesAt (retainedRegion source region)).map
          (Fin.castAdd sites.sites.length) ++
        ((Data.Finite.allFin sites.sites.length).filter fun site =>
          retainedRegion source (sites.sites.get site).region ==
            retainedRegion source region).map
          (replacementNode plan) := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin
        ((replacementBase plan).nodeCount + sites.sites.length)).filter
        (fun candidate =>
          ((replacementCandidate plan).nodes candidate).region ==
            retainedRegion source region) = _
  rw [allFin_add]
  refine (List.filter_append
    ((Data.Finite.allFin (replacementBase plan).nodeCount).map
      (Fin.castAdd sites.sites.length))
    ((Data.Finite.allFin sites.sites.length).map
      (Fin.natAdd (replacementBase plan).nodeCount))).trans ?_
  rw [List.filter_map, List.filter_map]
  congr 1
  · apply congrArg (List.map (Fin.castAdd sites.sites.length))
    apply List.filter_congr
    intro retained _member
    simp only [Function.comp_apply]
    unfold replacementCandidate
    rw [assigned_node]
    have skeletonRegion :=
      replacementSkeleton_retained_node_region
        (sites := sites) (spec := spec) plan retained
    have baseRegion :
        ((replacementBase plan).nodes retained).region =
          retainedRegion source
            (source.val.nodes
              (Internal.sourceRetainedNode source
                (argumentSiteNodes sites) retained)).region := by
      unfold replacementBase
      rw [Internal.batchRemovalCandidate_node_region_noRegions,
        retainedRegion_eq_noRegionRemovalEquiv]
    exact congrArg
      (fun candidate => candidate == retainedRegion source region)
      (skeletonRegion.trans baseRegion.symm)
  · apply congrArg (List.map (Fin.natAdd
      (replacementBase plan).nodeCount))
    apply List.filter_congr
    intro site _member
    simp only [Function.comp_apply]
    unfold replacementCandidate
    rw [assigned_node]
    change
      (((replacementSkeleton plan).nodes
          (replacementNode plan site)).region ==
        retainedRegion source region) = _
    rw [replacementSkeleton_replacementNode
      (sites := sites) (spec := spec) plan site]
    rfl

/-- Exact ordered local-wire decomposition of a replacement candidate.  The
Boolean filters deliberately mirror `ConcreteDiagram.wiresAt`; later laws
can simplify them using operation-specific scope facts without reopening the
dense allocation proof. -/
theorem replacementCandidate_wiresAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (region : source.val.RegionId) :
    (replacementCandidate plan).wiresAt (retainedRegion source region) =
      ((replacementBase plan).wiresAt (retainedRegion source region)).map
          (fun retained =>
            show (replacementCandidate plan).WireId from
              Fin.castAdd (1 + spec.localCount) retained) ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              replacementCandidateWire plan) ++
        ((Data.Finite.allFin spec.localCount).filter fun fresh =>
          retainedRegion source (spec.localScope fresh) ==
            retainedRegion source region).map
            (replacementCandidateLocalWire plan) := by
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change
    (Data.Finite.allFin
        ((replacementBase plan).wireCount + (1 + spec.localCount))).filter
        (fun candidate =>
          ((replacementSkeleton plan).wires candidate).scope ==
            retainedRegion source region) = _
  rw [allFin_add]
  refine (List.filter_append
    ((Data.Finite.allFin (replacementBase plan).wireCount).map
      (Fin.castAdd (1 + spec.localCount)))
    ((Data.Finite.allFin (1 + spec.localCount)).map
      (Fin.natAdd (replacementBase plan).wireCount))).trans ?_
  rw [List.filter_map, List.filter_map, List.append_assoc]
  congr 1
  · apply congrArg (List.map (Fin.castAdd (1 + spec.localCount)))
    apply List.filter_congr
    intro retained _member
    simp [replacementSkeleton]
    rfl
  · rw [allFin_add]
    rw [List.filter_append, List.map_append,
      List.filter_map, List.filter_map]
    simp only [List.map_map]
    simp [Function.comp_def, replacementCandidateWire,
      replacementCandidateLocalWire,
      replacementHeadWire, replacementLocalWire, replacementSkeleton,
      replacementSkeleton_head_wire_scope,
      replacementSkeleton_local_wire_scope]
    congr 1
    apply List.map_congr_left
    intro head _member
    have headZero : head = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst head
    rfl

/-- Checked argument results retain the candidate's exact ordered local-wire
decomposition; this is the context order consumed by structural compilation. -/
theorem ArgumentResult.wiresAt_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.wiresAt (result.regionImage region) =
      ((replacementBase result.plan).wiresAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedWire result.generated
              (Fin.castAdd (1 + result.spec.localCount) retained)) ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              result.targetWire) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map result.targetLocalWire := by
  unfold ArgumentResult.regionImage
  rw [Internal.checkedWiresAt_transport,
    replacementCandidate_wiresAt]
  simp only [List.map_append, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro head _member
  exact result.targetWire_exact.symm

/-- Checked argument results retain the candidate's exact ordered local-node
decomposition: retained source nodes first, then one replacement per applied
site in site order. -/
theorem ArgumentResult.nodesAt_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.nodesAt (result.regionImage region) =
      ((replacementBase result.plan).nodesAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) ++
        ((Data.Finite.allFin result.sites.sites.length).filter fun site =>
          retainedRegion source (result.sites.sites.get site).region ==
            retainedRegion source region).map result.targetNode := by
  unfold ArgumentResult.regionImage
  rw [Internal.checkedNodesAt_transport,
    replacementCandidate_nodesAt]
  calc
    _ =
        (((replacementBase result.plan).nodesAt
            (retainedRegion source region)).map
              (Fin.castAdd result.sites.sites.length)).map
            (Internal.checkedNode result.generated) ++
          (((Data.Finite.allFin result.sites.sites.length).filter fun site =>
            retainedRegion source (result.sites.sites.get site).region ==
              retainedRegion source region).map
            (replacementNode result.plan)).map
              (Internal.checkedNode result.generated) := List.map_append
    _ = _ := by
      congr 1
      · exact map_map_apply _ _ _
      · exact map_map_apply _ _ _

/-- The source node selected by a dense replacement-base index maps back to
that exact retained candidate position in the checked target. -/
theorem ArgumentResult.retainedNodeImage_sourceRetainedNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (retained : (replacementBase result.plan).NodeId) :
    result.retainedNodeImage
        (Internal.sourceRetainedNode source
          (argumentSiteNodes result.sites) retained)
        (sourceRetainedNode_not_removed result.sites retained) =
      Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length retained) := by
  unfold ArgumentResult.retainedNodeImage
  apply congrArg (Internal.checkedNode result.generated)
  apply Fin.ext
  simp only [Fin.val_castAdd]
  exact congrArg Fin.val
    (Internal.retainedNodeIndex_sourceRetainedNode source
      (argumentSiteNodes result.sites) retained)

/-- A wire owning a required port of a retained source node is itself
retained.  Exhaustiveness rules out every removed wire because each endpoint
of such a wire belongs to an acted site. -/
theorem ArgumentResult.ownerOfRetainedNode_not_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (nodeRetained : node ∉ argumentSiteNodes result.sites)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (sourceOwner :
      source.val.endpointOwner? ⟨node, port⟩ = some sourceWire) :
    sourceWire ∉ result.sourceRemovedWires := by
  intro removed
  have incident := ConcreteDiagram.endpointOwner?_incident source.val
    ⟨node, port⟩ sourceWire sourceOwner
  have removedNode := result.source_removed_exhausted sourceWire removed
    ⟨node, port⟩ incident
  exact nodeRetained removedNode

/-- Endpoint ownership at a retained node is transported through the exact
retained node and wire images. -/
theorem ArgumentResult.retainedNodeImage_endpointOwner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (nodeRetained : node ∉ argumentSiteNodes result.sites)
    (port : CPort)
    (required : port ∈ source.val.requiredPorts node)
    (sourceWire : source.val.WireId)
    (sourceOwner :
      source.val.endpointOwner? ⟨node, port⟩ = some sourceWire) :
    result.checked.val.endpointOwner?
        ⟨result.retainedNodeImage node nodeRetained, port⟩ =
      some (result.retainedWireImage sourceWire
        (result.ownerOfRetainedNode_not_removed node nodeRetained port
          sourceWire sourceOwner)) := by
  let nodeMember : node ∈ Internal.retainedNodes source
      (argumentSiteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true nodeRetained⟩
  let retainedNode := Internal.retainedNodeIndex source
    (argumentSiteNodes result.sites) node nodeMember
  have sourceNodeExact :
      Internal.sourceRetainedNode source
          (argumentSiteNodes result.sites) retainedNode = node :=
    Internal.sourceRetainedNode_retainedNodeIndex source
      (argumentSiteNodes result.sites) node nodeMember
  have skeletonRequired :
      port ∈ (replacementSkeleton result.plan).requiredPorts
        (Fin.castAdd result.sites.sites.length retainedNode) := by
    rw [replacementSkeleton_retained_requiredPorts]
    rw [sourceNodeExact]
    exact required
  have candidateRequired :
      port ∈ (replacementCandidate result.plan).requiredPorts
        (Fin.castAdd result.sites.sites.length retainedNode) := by
    unfold replacementCandidate
    rw [assigned_requiredPorts]
    exact skeletonRequired
  let wireNotRemoved := result.ownerOfRetainedNode_not_removed node
    nodeRetained port sourceWire sourceOwner
  let wireMember : sourceWire ∈
      Internal.retainedWires source result.sourceRemovedWires := by
    unfold Internal.retainedWires
    exact List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin sourceWire, decide_eq_true wireNotRemoved⟩
  let retainedWire := Internal.retainedWireIndex source
    result.sourceRemovedWires sourceWire wireMember
  have candidateOwner :
      (replacementCandidate result.plan).endpointOwner?
          ⟨Fin.castAdd result.sites.sites.length retainedNode, port⟩ =
        some (Fin.castAdd (1 + result.spec.localCount) retainedWire) := by
    calc
      _ = some (replacementOwner result.plan
            ⟨Fin.castAdd result.sites.sites.length retainedNode, port⟩) :=
        assigned_endpointOwner_required
          (replacementSkeleton result.plan) (replacementOwner result.plan)
          (Fin.castAdd result.sites.sites.length retainedNode) port
          candidateRequired
      _ = _ := by
        congr 1
        unfold replacementOwner
        simp only [Fin.addCases_left]
        rw [sourceNodeExact, sourceOwner]
        change (retainedReplacementWire? result.plan sourceWire).getD
            (replacementHeadWire result.plan) = _
        rw [retainedReplacementWire?_some result.plan sourceWire wireMember]
        rfl
  have transported := Internal.checkedEndpoint_owner_transport
    result.generated
    (⟨Fin.castAdd result.sites.sites.length retainedNode, port⟩ :
      CEndpoint (replacementCandidate result.plan).nodeCount)
  rw [candidateOwner] at transported
  have nodeImageExact :
      result.retainedNodeImage node nodeRetained =
        Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length retainedNode) := by
    unfold ArgumentResult.retainedNodeImage retainedNode nodeMember
    congr
  have wireImageExact :
      result.retainedWireImage sourceWire wireNotRemoved =
        Internal.checkedWire result.generated
          (Fin.castAdd (1 + result.spec.localCount) retainedWire) := by
    unfold ArgumentResult.retainedWireImage retainedWire wireMember
    congr
  rw [nodeImageExact, wireImageExact]
  exact transported

/-- Exact ordered node-payload decomposition at every source region.  Retained
payloads are renamed only by the canonical region equivalence; generated
payloads are precisely the replacement atoms selected by the operation. -/
theorem ArgumentResult.localNodeData_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    (result.checked.val.nodesAt (result.regionImage region)).map
        result.checked.val.nodes =
      ((source.val.nodesAt region).filter
          (fun sourceNode =>
            decide (sourceNode ∉ argumentSiteNodes result.sites))).map
          (fun sourceNode =>
            (source.val.nodes sourceNode).rename result.regionEquiv) ++
        ((Data.Finite.allFin result.sites.sites.length).filter fun site =>
          retainedRegion source (result.sites.sites.get site).region ==
            retainedRegion source region).map (fun site =>
              .atom
                (result.regionImage
                  (result.sites.sites.get site).region)
                result.targetArguments) := by
  rw [result.nodesAt_decomposition, List.map_append]
  have retainedExact :
      (((replacementBase result.plan).nodesAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained))).map
          result.checked.val.nodes =
        ((source.val.nodesAt region).filter
          (fun sourceNode =>
            decide
              (sourceNode ∉ argumentSiteNodes result.sites))).map
          (fun sourceNode =>
            (source.val.nodes sourceNode).rename result.regionEquiv) := by
    calc
      _ = ((replacementBase result.plan).nodesAt
            (retainedRegion source region)).map (fun retained =>
              (source.val.nodes
                (Internal.sourceRetainedNode source
                  (argumentSiteNodes result.sites) retained)).rename
                    result.regionEquiv) := by
            rw [map_map_apply]
            apply List.map_congr_left
            intro retained _member
            rw [← result.retainedNodeImage_sourceRetainedNode retained]
            exact result.retainedNodeImage_data _ _
      _ = _ := by
            have baseSources :=
              batchRemovalCandidate_nodesAt_sources
                result.plan.removal region
            rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
            change
              ((replacementBase result.plan).nodesAt
                  (retainedRegion source region)).map
                    (Internal.sourceRetainedNode source
                      (argumentSiteNodes result.sites)) =
                (source.val.nodesAt region).filter
                  (fun sourceNode =>
                    decide
                      (sourceNode ∉ argumentSiteNodes result.sites))
              at baseSources
            calc
              _ = ((((replacementBase result.plan).nodesAt
                    (retainedRegion source region)).map
                      (Internal.sourceRetainedNode source
                        (argumentSiteNodes result.sites))).map
                    (fun sourceNode =>
                      (source.val.nodes sourceNode).rename
                        result.regionEquiv)) := by
                  exact (map_map_apply
                    ((replacementBase result.plan).nodesAt
                      (retainedRegion source region))
                    (Internal.sourceRetainedNode source
                      (argumentSiteNodes result.sites))
                    (fun sourceNode =>
                      (source.val.nodes sourceNode).rename
                        result.regionEquiv)).symm
              _ = _ := congrArg
                (List.map fun sourceNode =>
                  (source.val.nodes sourceNode).rename result.regionEquiv)
                baseSources
  rw [retainedExact]
  congr 1
  rw [map_map_apply]
  apply List.map_congr_left
  intro site _member
  exact result.targetNode_data site

/-- Argument replacement preserves the exact ordered region tree.  Every
target child is the canonical image of the corresponding source child, with
no reordering or additional region. -/
theorem ArgumentResult.childrenOf_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.childrenOf (result.regionImage region) =
      (source.val.childrenOf region).map result.regionEquiv := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  rw [result.regionImage_exact]
  rw [← map_allFin_finEquivOfEq result.regionCount_exact]
  have equivalenceExact :
      finEquivOfEq result.regionCount_exact = result.regionEquiv := rfl
  rw [equivalenceExact]
  rw [List.filter_map]
  apply congrArg (List.map result.regionEquiv)
  apply List.filter_congr
  intro child _member
  simp only [Function.comp_apply]
  rw [result.regionImage_data child]
  cases source.val.regions child with
  | sheet => rfl
  | cut parent =>
      simp only [CRegion.rename]
      exact decide_eq_decide.mpr result.regionEquiv.injective.eq_iff

/-- An applied site cannot itself lie at a region strictly above the acted
head's scope. -/
theorem ArgumentResult.siteRegion_ne_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope)
    (site : Fin result.sites.sites.length) :
    (result.sites.sites.get site).region ≠ outer := by
  intro same
  have scopeEnclosesOuter :
      source.val.Encloses (source.val.wires wire).scope outer := by
    rw [← same]
    exact (result.sites.sites.get site).head_visible
  have equal :=
    factor_encloses_antisymm definitions source.val source.property
      outerEncloses scopeEnclosesOuter
  exact strict equal

/-- No rewritten application node is local to a region strictly above the
acted head's scope. -/
theorem ArgumentResult.nodeAt_strictlyAbove_not_siteNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt outer) :
    node ∉ argumentSiteNodes result.sites := by
  intro removed
  obtain ⟨site, _siteMember, siteExact⟩ := List.mem_map.mp removed
  have regionExact : site.region = outer := by
    rw [ConcreteDiagram.nodesAt, List.mem_filter] at nodeAt
    have localExact := eq_of_beq nodeAt.2
    rw [← siteExact, site.node_data] at localExact
    exact localExact
  have scopeEnclosesOuter :
      source.val.Encloses (source.val.wires wire).scope outer := by
    rw [← regionExact]
    exact site.head_visible
  have equal :=
    factor_encloses_antisymm definitions source.val source.property
      outerEncloses scopeEnclosesOuter
  exact strict equal

/-- Above the acted scope, node compilation sees exactly the retained source
payloads in source order; the replacement contributes no local node. -/
theorem ArgumentResult.localNodeData_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    (result.checked.val.nodesAt (result.regionImage outer)).map
        result.checked.val.nodes =
      (source.val.nodesAt outer).map (fun sourceNode =>
        (source.val.nodes sourceNode).rename result.regionEquiv) := by
  rw [result.localNodeData_decomposition outer]
  have retainedExact :
      (source.val.nodesAt outer).filter
          (fun sourceNode =>
            decide
              (sourceNode ∉ argumentSiteNodes result.sites)) =
        source.val.nodesAt outer := by
    apply List.filter_eq_self.mpr
    intro node member
    exact decide_eq_true
      (result.nodeAt_strictlyAbove_not_siteNode outer outerEncloses
        strict node member)
  rw [retainedExact]
  have generatedEmpty :
      (Data.Finite.allFin result.sites.sites.length).filter
          (fun site =>
            retainedRegion source (result.sites.sites.get site).region ==
              retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro site _member
    intro accepted
    have same := eq_of_beq accepted
    apply result.siteRegion_ne_strictlyAbove outer outerEncloses strict site
    apply (Internal.noRegionRemovalEquiv source).injective
    rw [← retainedRegion_eq_noRegionRemovalEquiv,
      ← retainedRegion_eq_noRegionRemovalEquiv]
    exact same
  rw [generatedEmpty]
  simp

/-- Construction-owned scope locality needed by frame naturality.  Removed
and freshly generated local wires may live at the acted scope or below it,
never above it. -/
structure ArgumentResult.ScopeLocalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) : Prop where
  removed_enclosed :
    ∀ sourceWire, sourceWire ∈ result.sourceRemovedWires →
      source.val.Encloses (source.val.wires wire).scope
        (source.val.wires sourceWire).scope
  local_enclosed :
    ∀ fresh : Fin result.spec.localCount,
      source.val.Encloses (source.val.wires wire).scope
        (result.spec.localScope fresh)

/-- Exact ordered signature decomposition at every source region.  This is
the typed context counterpart of `wiresAt_decomposition`: retained source
signatures keep their order, followed by the replacement head when it is
local to the region, followed by operation-local signatures. -/
theorem ArgumentResult.localSignatures_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      ((source.val.wiresAt region).filter
          (fun sourceWire =>
            decide (sourceWire ∉ result.sourceRemovedWires))).map
          (fun sourceWire => (source.val.wires sourceWire).sig) ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              .rel result.targetArguments) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map result.spec.localSignature := by
  rw [result.wiresAt_decomposition]
  simp only [List.map_append, List.map_map]
  have retainedExact :
      ((replacementBase result.plan).wiresAt
          (retainedRegion source region)).map
          ((fun targetWire =>
              (result.checked.val.wires targetWire).sig) ∘
            fun retained =>
              Internal.checkedWire result.generated
                (Fin.castAdd (1 + result.spec.localCount) retained)) =
        ((source.val.wiresAt region).filter
          (fun sourceWire =>
            decide (sourceWire ∉ result.sourceRemovedWires))).map
          (fun sourceWire => (source.val.wires sourceWire).sig) := by
    calc
      _ = ((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map
            (fun retained =>
              (source.val.wires
                (Internal.sourceRetainedWire source
                  result.sourceRemovedWires retained)).sig) := by
            apply List.map_congr_left
            intro retained _member
            simp only [Function.comp_apply]
            rw [Internal.checkedWire_signature_transport]
            unfold replacementCandidate
            rw [assigned_wire_signature,
              replacementSkeleton_retained_wire_signature]
            rfl
      _ = ((((replacementBase result.plan).wiresAt
              (retainedRegion source region)).map
                (Internal.sourceRetainedWire source
                  result.sourceRemovedWires)).map
              (fun sourceWire =>
                (source.val.wires sourceWire).sig)) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro retained _member
            rfl
      _ = _ := by
            have baseSources :=
              batchRemovalCandidate_wiresAt_sources
                result.plan.removal region
            rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
            change
              ((replacementBase result.plan).wiresAt
                  (retainedRegion source region)).map
                    (Internal.sourceRetainedWire source
                      result.sourceRemovedWires) =
                (source.val.wiresAt region).filter
                  (fun sourceWire =>
                    decide (sourceWire ∉ result.sourceRemovedWires))
              at baseSources
            rw [baseSources]
  rw [retainedExact]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro head _member
    simp only [Function.comp_apply]
    exact result.targetWire_signature
  · apply List.map_congr_left
    intro fresh _member
    exact result.targetLocalWire_signature fresh

/-- Strictly above a scope-local argument replacement, the exact ordered
local signature context is unchanged. -/
theorem ArgumentResult.localSignatures_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    (result.checked.val.wiresAt (result.regionImage outer)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      (source.val.wiresAt outer).map
        (fun sourceWire => (source.val.wires sourceWire).sig) := by
  rw [result.localSignatures_decomposition outer]
  have retainedExact :
      (source.val.wiresAt outer).filter
          (fun sourceWire =>
            decide (sourceWire ∉ result.sourceRemovedWires)) =
        source.val.wiresAt outer := by
    apply List.filter_eq_self.mpr
    intro sourceWire member
    apply decide_eq_true
    intro removed
    rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
    have scopeExact := eq_of_beq member.2
    have scopeEnclosesOuter :
        source.val.Encloses (source.val.wires wire).scope outer := by
      rw [← scopeExact]
      exact localized.removed_enclosed sourceWire removed
    have equal := factor_encloses_antisymm definitions source.val
      source.property outerEncloses scopeEnclosesOuter
    exact strict equal
  rw [retainedExact]
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro _head _member accepted
    have same := eq_of_beq accepted
    apply strict
    apply (Internal.noRegionRemovalEquiv source).injective
    rw [← retainedRegion_eq_noRegionRemovalEquiv,
      ← retainedRegion_eq_noRegionRemovalEquiv]
    exact same.symm
  rw [headEmpty]
  have localEmpty :
      (Data.Finite.allFin result.spec.localCount).filter (fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _member accepted
    have same := eq_of_beq accepted
    have localExact : result.spec.localScope fresh = outer := by
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact same
    have scopeEnclosesOuter :
        source.val.Encloses (source.val.wires wire).scope outer := by
      rw [← localExact]
      exact localized.local_enclosed fresh
    have equal := factor_encloses_antisymm definitions source.val
      source.property outerEncloses scopeEnclosesOuter
    exact strict equal
  rw [localEmpty]
  simp

end ConcreteWirePrimitive
end VisualProof
