import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsConstruction

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

namespace ArgumentResult

/-- Every endpoint of every source wire removed by the replacement belongs to
one of the exhaustive source application sites. -/
theorem sourceRemovedExhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (removed : sourceWire ∈ result.sourceRemovedWires)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints) :
    endpoint.node ∈ argumentSiteNodes result.sites := by
  exact result.source_removed_exhausted sourceWire removed endpoint incident

/-- Every endpoint of the generated head and generated local wires belongs to
one of the exhaustive target application sites. -/
theorem targetRemovedExhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (targetWire : result.checked.val.WireId)
    (removed : targetWire ∈ result.targetRemovedWires)
    (endpoint : CEndpoint result.checked.val.nodeCount)
    (incident : endpoint ∈
      (result.checked.val.wires targetWire).endpoints) :
    endpoint.node ∈ argumentSiteNodes targetSites := by
  unfold targetRemovedWires at removed
  rcases List.mem_cons.mp removed with headExact | localRemoved
  · subst targetWire
    exact allAppliedSites_removed_exhausted targetSites endpoint incident
  · unfold targetLocalWires at localRemoved
    rcases List.mem_map.mp localRemoved with
      ⟨fresh, _freshMember, localExact⟩
    subst targetWire
    rw [Internal.checkedWire_endpoints_transport] at incident
    rcases List.mem_map.mp incident with
      ⟨candidateEndpoint, candidateIncident, endpointExact⟩
    subst endpoint
    have candidateHeadIncident :=
      replacementCandidate_local_endpoint_head_incident
        result.plan fresh candidateEndpoint candidateIncident
    have checkedHeadIncident :
        Internal.checkedEndpoint result.generated
            ⟨candidateEndpoint.node, .head⟩ ∈
          (result.checked.val.wires result.targetWire).endpoints := by
      rw [result.targetWire_exact,
        Internal.checkedWire_endpoints_transport]
      apply List.mem_map.mpr
      exact ⟨⟨candidateEndpoint.node, .head⟩,
        candidateHeadIncident, rfl⟩
    exact allAppliedSites_removed_exhausted targetSites
      (Internal.checkedEndpoint result.generated
        ⟨candidateEndpoint.node, .head⟩)
      checkedHeadIncident

/-- Target application nodes are precisely images of the freshly generated
replacement nodes; no retained source node can become a target site. -/
theorem targetSiteNode_generated
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : result.checked.val.NodeId)
    (member : node ∈ argumentSiteNodes targetSites) :
    ∃ site : Fin result.sites.sites.length,
      node = Internal.checkedNode result.generated
        (replacementNode result.plan site) := by
  unfold argumentSiteNodes at member
  rcases List.mem_map.mp member with
    ⟨targetSite, targetSiteMember, nodeExact⟩
  have targetEndpointMember :
      targetSite.endpoint ∈
        (result.checked.val.wires result.targetWire).endpoints := by
    rw [← targetSites.exhaustive]
    exact List.mem_map.mpr
      ⟨targetSite, targetSiteMember, rfl⟩
  have targetEndpointsExact :
      (result.checked.val.wires result.targetWire).endpoints =
        ((replacementCandidate result.plan).wires
          (replacementCandidateWire result.plan)).endpoints.map
            (Internal.checkedEndpoint result.generated) := by
    calc
      (result.checked.val.wires result.targetWire).endpoints =
          (result.checked.val.wires
            (Internal.checkedWire result.generated
              (replacementCandidateWire result.plan))).endpoints := by
        rw [result.targetWire_exact]
      _ = _ := Internal.checkedWire_endpoints_transport
        result.generated (replacementCandidateWire result.plan)
  rw [targetEndpointsExact] at targetEndpointMember
  rcases List.mem_map.mp targetEndpointMember with
    ⟨candidateEndpoint, candidateMember, endpointExact⟩
  obtain ⟨site, candidateNodeExact⟩ :=
    replacementCandidate_head_endpoint_generated result.plan
      result.source_removed_exhausted candidateEndpoint candidateMember
  have checkedNodeExact :
      Internal.checkedNode result.generated candidateEndpoint.node =
        targetSite.node :=
    congrArg CEndpoint.node endpointExact
  refine ⟨site, nodeExact.symm.trans ?_⟩
  exact checkedNodeExact.symm.trans
    (congrArg (Internal.checkedNode result.generated) candidateNodeExact)

/-- Every freshly generated replacement node occurs in the exhaustive target
site list. -/
theorem generatedNode_targetSiteNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (site : Fin result.sites.sites.length) :
    Internal.checkedNode result.generated
        (replacementNode result.plan site) ∈ argumentSiteNodes targetSites := by
  have candidateIncident :=
    replacementCandidate_generated_head_incident result.plan site
  have checkedIncident :
      Internal.checkedEndpoint result.generated
          ⟨replacementNode result.plan site, .head⟩ ∈
        (result.checked.val.wires result.targetWire).endpoints := by
    rw [result.targetWire_exact,
      Internal.checkedWire_endpoints_transport]
    exact List.mem_map.mpr
      ⟨⟨replacementNode result.plan site, .head⟩,
        candidateIncident, rfl⟩
  rw [← targetSites.exhaustive] at checkedIncident
  rcases List.mem_map.mp checkedIncident with
    ⟨targetSite, targetSiteMember, endpointExact⟩
  unfold argumentSiteNodes
  apply List.mem_map.mpr
  refine ⟨targetSite, targetSiteMember, ?_⟩
  exact congrArg CEndpoint.node endpointExact

theorem targetSiteNode_iff_ge
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : result.checked.val.NodeId) :
    node ∈ argumentSiteNodes targetSites ↔
      (replacementBase result.plan).nodeCount ≤ node.val := by
  constructor
  · intro member
    obtain ⟨site, exact⟩ :=
      result.targetSiteNode_generated targetSites node member
    have values := congrArg Fin.val exact
    simp [Internal.checkedNode, replacementNode] at values
    omega
  · intro large
    have countExact :
        result.checked.val.nodeCount =
          (replacementBase result.plan).nodeCount +
            result.sites.sites.length := by
      rw [result.generated]
      rfl
    let site : Fin result.sites.sites.length :=
      ⟨node.val - (replacementBase result.plan).nodeCount, by
        have bound := node.isLt
        omega⟩
    have generated :=
      result.generatedNode_targetSiteNode targetSites site
    have nodeExact :
        Internal.checkedNode result.generated
            (replacementNode result.plan site) = node := by
      apply Fin.ext
      simp [Internal.checkedNode, replacementNode, site]
      omega
    simpa [nodeExact] using generated

/-- Decode the ordered source-site position stored in one generated target
application node.  Replacement nodes occupy the checked suffix in source
site order. -/
def sourcePositionOfTargetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : result.checked.val.NodeId)
    (generated : node ∈ argumentSiteNodes targetSites) :
    Fin result.sites.sites.length :=
  ⟨node.val - (replacementBase result.plan).nodeCount, by
    have lower := (result.targetSiteNode_iff_ge targetSites node).mp generated
    have countExact :
        result.checked.val.nodeCount =
          (replacementBase result.plan).nodeCount +
            result.sites.sites.length := by
      rw [result.generated]
      rfl
    have upper := node.isLt
    omega⟩

/-- Decoding a generated target node and re-encoding its site position
returns that exact checked node. -/
theorem targetNode_sourcePositionOfTargetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : result.checked.val.NodeId)
    (generated : node ∈ argumentSiteNodes targetSites) :
    result.targetNode
        (result.sourcePositionOfTargetNode targetSites node generated) =
      node := by
  apply Fin.ext
  have lower := (result.targetSiteNode_iff_ge targetSites node).mp generated
  simp [ArgumentResult.targetNode, sourcePositionOfTargetNode,
    Internal.checkedNode, replacementNode]
  omega

/-- Encoding a source-site position and decoding its generated target node
returns that exact position. -/
@[simp] theorem sourcePositionOfTargetNode_targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (position : Fin result.sites.sites.length)
    (generated :
      result.targetNode position ∈ argumentSiteNodes targetSites) :
    result.sourcePositionOfTargetNode targetSites
        (result.targetNode position) generated = position := by
  apply Fin.ext
  simp [ArgumentResult.targetNode, sourcePositionOfTargetNode,
    Internal.checkedNode, replacementNode]

private theorem targetRetainedNodes_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    Internal.retainedNodes result.checked (argumentSiteNodes targetSites) =
      (Data.Finite.allFin (replacementBase result.plan).nodeCount).map
        (fun node =>
          Internal.checkedNode result.generated
            (Fin.castAdd result.sites.sites.length node)) := by
  unfold Internal.retainedNodes ConcreteDiagram.nodesList
  have countExact :
      result.checked.val.nodeCount =
        (replacementBase result.plan).nodeCount +
          result.sites.sites.length := by
    rw [result.generated]
    rfl
  have filtered := filter_allFin_suffix_of_eq
    result.checked.val.nodeCount
    (replacementBase result.plan).nodeCount result.sites.sites.length
    countExact (argumentSiteNodes targetSites)
    (result.targetSiteNode_iff_ge targetSites)
  rw [filtered]
  apply List.map_congr_left
  intro node _member
  apply Fin.ext
  rfl

private theorem targetRemovedWire_iff_ge
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetWire : result.checked.val.WireId) :
    targetWire ∈ result.targetRemovedWires ↔
      (replacementBase result.plan).wireCount ≤ targetWire.val := by
  constructor
  · intro removed
    unfold targetRemovedWires at removed
    rcases List.mem_cons.mp removed with headExact | localRemoved
    · subst targetWire
      have values := congrArg Fin.val result.targetWire_exact
      simp [Internal.checkedWire, replacementCandidateWire,
        replacementHeadWire] at values
      omega
    · unfold targetLocalWires at localRemoved
      rcases List.mem_map.mp localRemoved with
        ⟨fresh, _freshMember, wireExact⟩
      subst targetWire
      simp [Internal.checkedWire, replacementCandidateLocalWire,
        replacementLocalWire]
  · intro large
    have countExact :
        result.checked.val.wireCount =
          (replacementBase result.plan).wireCount +
            (1 + result.spec.localCount) := by
      rw [result.generated]
      rfl
    by_cases headValue :
        targetWire.val = (replacementBase result.plan).wireCount
    · unfold targetRemovedWires
      apply List.mem_cons.mpr
      left
      rw [result.targetWire_exact]
      apply Fin.ext
      simp [Internal.checkedWire, replacementCandidateWire,
        replacementHeadWire, headValue]
    · have afterHead :
          (replacementBase result.plan).wireCount < targetWire.val := by
        omega
      let fresh : Fin result.spec.localCount :=
        ⟨targetWire.val -
            (replacementBase result.plan).wireCount - 1, by
          have bound := targetWire.isLt
          omega⟩
      unfold targetRemovedWires
      apply List.mem_cons.mpr
      right
      unfold targetLocalWires
      apply List.mem_map.mpr
      refine ⟨fresh, Data.Finite.mem_allFin fresh, ?_⟩
      apply Fin.ext
      simp [Internal.checkedWire, replacementCandidateLocalWire,
        replacementLocalWire, fresh]
      omega

private theorem targetRetainedWires_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Internal.retainedWires result.checked result.targetRemovedWires =
      (Data.Finite.allFin (replacementBase result.plan).wireCount).map
        (fun targetWire =>
          Internal.checkedWire result.generated
            (Fin.castAdd (1 + result.spec.localCount) targetWire)) := by
  unfold Internal.retainedWires ConcreteDiagram.wiresList
  have countExact :
      result.checked.val.wireCount =
        (replacementBase result.plan).wireCount +
          (1 + result.spec.localCount) := by
    rw [result.generated]
    rfl
  have filtered := filter_allFin_suffix_of_eq
    result.checked.val.wireCount
    (replacementBase result.plan).wireCount (1 + result.spec.localCount)
    countExact result.targetRemovedWires result.targetRemovedWire_iff_ge
  rw [filtered]
  apply List.map_congr_left
  intro targetWire _member
  apply Fin.ext
  rfl

private def targetCoreNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : (replacementBase result.plan).NodeId) :
    Fin (Internal.retainedNodes result.checked
      (argumentSiteNodes targetSites)).length :=
  Internal.retainedNodeIndex result.checked (argumentSiteNodes targetSites)
    (Internal.checkedNode result.generated
      (Fin.castAdd result.sites.sites.length node)) (by
        rw [result.targetRetainedNodes_exact targetSites]
        apply List.mem_map.mpr
        exact ⟨node, Data.Finite.mem_allFin node, rfl⟩)

private theorem targetCoreNode_source_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : (replacementBase result.plan).NodeId) :
    Internal.sourceRetainedNode result.checked (argumentSiteNodes targetSites)
        (targetCoreNode result targetSites node) =
      Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length node) := by
  unfold targetCoreNode
  exact Internal.sourceRetainedNode_retainedNodeIndex _ _ _ _

private def targetCoreWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetWire : (replacementBase result.plan).WireId) :
    Fin (Internal.retainedWires result.checked
      result.targetRemovedWires).length :=
  Internal.retainedWireIndex result.checked result.targetRemovedWires
    (Internal.checkedWire result.generated
      (Fin.castAdd (1 + result.spec.localCount) targetWire)) (by
        rw [result.targetRetainedWires_exact]
        apply List.mem_map.mpr
        exact ⟨targetWire, Data.Finite.mem_allFin targetWire, rfl⟩)

private theorem targetCoreWire_source_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetWire : (replacementBase result.plan).WireId) :
    Internal.sourceRetainedWire result.checked result.targetRemovedWires
        (targetCoreWire result targetWire) =
      Internal.checkedWire result.generated
        (Fin.castAdd (1 + result.spec.localCount) targetWire) := by
  unfold targetCoreWire
  exact Internal.sourceRetainedWire_retainedWireIndex _ _ _ _

private theorem targetCoreNodeCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    (replacementBase result.plan).nodeCount =
      (Internal.retainedNodes result.checked
        (argumentSiteNodes targetSites)).length := by
  rw [result.targetRetainedNodes_exact targetSites]
  simp [Data.Finite.allFin_eq_finRange]

private def targetCoreNodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    Data.Finite.FiniteEquiv
      (replacementBase result.plan).NodeId
      (Fin (Internal.retainedNodes result.checked
        (argumentSiteNodes targetSites)).length) :=
  finEquivOfEq (result.targetCoreNodeCount_exact targetSites)

private theorem targetCoreNodeEquiv_source_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (node : (replacementBase result.plan).NodeId) :
    Internal.sourceRetainedNode result.checked (argumentSiteNodes targetSites)
        (targetCoreNodeEquiv result targetSites node) =
      Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length node) := by
  let retained :=
    Internal.retainedNodes result.checked (argumentSiteNodes targetSites)
  let mapped :=
    (Data.Finite.allFin (replacementBase result.plan).nodeCount).map
      (fun candidate =>
        Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length candidate))
  let mappedPosition : Fin mapped.length :=
    Fin.cast (by
      simp [mapped, Data.Finite.allFin_eq_finRange]) node
  have retainedExact : retained = mapped :=
    result.targetRetainedNodes_exact targetSites
  let position : Fin retained.length :=
    Fin.cast (result.targetCoreNodeCount_exact targetSites) node
  have mappedGet :
      mapped.get mappedPosition =
        Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length node) := by
    simp [mapped, mappedPosition]
    apply Fin.ext
    simpa [Internal.checkedNode] using congrArg Fin.val (allFin_get node)
  have positionExact :
      position =
        Fin.cast (congrArg List.length retainedExact).symm
          mappedPosition := by
    apply Fin.ext
    rfl
  have retainedGet :
      retained.get position =
        Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length node) := by
    rw [positionExact, get_of_list_eq retainedExact mappedPosition, mappedGet]
  have castExact :
      targetCoreNodeEquiv result targetSites node = position := by
    apply Fin.ext
    rfl
  rw [castExact]
  exact retainedGet

private theorem targetCoreWireCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (replacementBase result.plan).wireCount =
      (Internal.retainedWires result.checked
        result.targetRemovedWires).length := by
  rw [result.targetRetainedWires_exact]
  simp [Data.Finite.allFin_eq_finRange]

private def targetCoreWireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Data.Finite.FiniteEquiv
      (replacementBase result.plan).WireId
      (Fin (Internal.retainedWires result.checked
        result.targetRemovedWires).length) :=
  finEquivOfEq result.targetCoreWireCount_exact

private theorem targetCoreWireEquiv_source_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetWire : (replacementBase result.plan).WireId) :
    Internal.sourceRetainedWire result.checked result.targetRemovedWires
        (targetCoreWireEquiv result targetWire) =
      Internal.checkedWire result.generated
        (Fin.castAdd (1 + result.spec.localCount) targetWire) := by
  let retained :=
    Internal.retainedWires result.checked result.targetRemovedWires
  let mapped :=
    (Data.Finite.allFin (replacementBase result.plan).wireCount).map
      (fun candidate =>
        Internal.checkedWire result.generated
          (Fin.castAdd (1 + result.spec.localCount) candidate))
  let mappedPosition : Fin mapped.length :=
    Fin.cast (by
      simp [mapped, Data.Finite.allFin_eq_finRange]) targetWire
  have retainedExact : retained = mapped :=
    result.targetRetainedWires_exact
  let position : Fin retained.length :=
    Fin.cast result.targetCoreWireCount_exact targetWire
  have mappedGet :
      mapped.get mappedPosition =
        Internal.checkedWire result.generated
          (Fin.castAdd (1 + result.spec.localCount) targetWire) := by
    simp [mapped, mappedPosition]
    apply Fin.ext
    simpa [Internal.checkedWire] using congrArg Fin.val (allFin_get targetWire)
  have positionExact :
      position =
        Fin.cast (congrArg List.length retainedExact).symm
          mappedPosition := by
    apply Fin.ext
    rfl
  have retainedGet :
      retained.get position =
        Internal.checkedWire result.generated
          (Fin.castAdd (1 + result.spec.localCount) targetWire) := by
    rw [positionExact, get_of_list_eq retainedExact mappedPosition, mappedGet]
  have castExact : targetCoreWireEquiv result targetWire = position := by
    apply Fin.ext
    rfl
  rw [castExact]
  exact retainedGet

private theorem targetCoreRegionCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (replacementBase result.plan).regionCount =
      (Internal.retainedRegions result.checked []).length := by
  rw [Internal.retainedRegions_nil]
  simp [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange]
  have countExact := congrArg ConcreteDiagram.regionCount result.generated
  simpa [replacementCandidate, replacementSkeleton] using countExact.symm

private def targetCoreRegionEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Data.Finite.FiniteEquiv
      (replacementBase result.plan).RegionId
      (Fin (Internal.retainedRegions result.checked []).length) :=
  finEquivOfEq result.targetCoreRegionCount_exact

private theorem targetCoreRegionEquiv_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : (replacementBase result.plan).RegionId) :
    targetCoreRegionEquiv result region =
      Internal.noRegionRemovalEquiv result.checked
        (Internal.checkedRegion result.generated region) := by
  let retained := Internal.retainedRegions result.checked []
  let checked := Internal.checkedRegion result.generated region
  let position : Fin retained.length :=
    Fin.cast (by
      unfold retained
      rw [Internal.retainedRegions_nil]
      simp [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange]) checked
  have retainedGet : retained.get position = checked := by
    let mapped := result.checked.val.regionsList
    let mappedPosition : Fin mapped.length :=
      Fin.cast (by
        simp [mapped, ConcreteDiagram.regionsList,
          Data.Finite.allFin_eq_finRange]) checked
    have retainedExact : retained = mapped := by
      unfold retained mapped
      exact Internal.retainedRegions_nil result.checked
    have positionExact :
        position =
          Fin.cast (congrArg List.length retainedExact).symm
            mappedPosition := by
      apply Fin.ext
      rfl
    rw [positionExact, get_of_list_eq retainedExact mappedPosition]
    unfold mapped mappedPosition ConcreteDiagram.regionsList
    exact allFin_get checked
  have indexed :
      Internal.noRegionRemovalEquiv result.checked checked = position := by
    have checkedMember : checked ∈ retained := by
      rw [← retainedGet]
      exact List.get_mem retained position
    unfold Internal.noRegionRemovalEquiv Internal.retainedRegionIndex
    change DenseList.index retained checked checkedMember = position
    have valueExact :
        DenseList.index retained checked checkedMember =
          DenseList.index retained (retained.get position)
            (List.get_mem retained position) := by
      congr
      exact retainedGet.symm
    exact valueExact.trans (DenseList.index_get retained (by
      unfold retained
      rw [Internal.retainedRegions_nil]
      exact Data.Finite.allFin_nodup result.checked.val.regionCount) _)
  have castExact : targetCoreRegionEquiv result region = position := by
    apply Fin.ext
    rfl
  exact castExact.trans indexed.symm

private theorem replacementCandidate_retained_endpoint_iff
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (baseWire : (replacementBase result.plan).WireId)
    (endpoint : CEndpoint (replacementBase result.plan).nodeCount) :
    (⟨Fin.castAdd result.sites.sites.length endpoint.node, endpoint.port⟩ :
        CEndpoint (replacementCandidate result.plan).nodeCount) ∈
        ((replacementCandidate result.plan).wires
          (Fin.castAdd (1 + result.spec.localCount) baseWire)).endpoints ↔
      endpoint ∈ ((replacementBase result.plan).wires baseWire).endpoints := by
  let candidateEndpoint :
      CEndpoint (replacementCandidate result.plan).nodeCount :=
    ⟨Fin.castAdd result.sites.sites.length endpoint.node, endpoint.port⟩
  constructor
  · intro candidateIncident
    have assigned :=
      (assigned_endpoint_mem_iff (replacementSkeleton result.plan)
        (replacementOwner result.plan)
        (Fin.castAdd (1 + result.spec.localCount) baseWire)
        candidateEndpoint).mp candidateIncident
    have required : endpoint.port ∈
        (replacementSkeleton result.plan).requiredPorts
          (Fin.castAdd result.sites.sites.length endpoint.node) :=
      required_of_endpoint_mem (replacementSkeleton result.plan)
        candidateEndpoint assigned.1
    obtain ⟨sourceWire, retained, sourceOwner, ownerExact⟩ :=
      replacementOwner_retained_exhausted result.plan
        result.source_removed_exhausted endpoint.node endpoint.port required
    have retainedIndexExact :
        Internal.retainedWireIndex source result.sourceRemovedWires
            sourceWire retained = baseWire := by
      apply Fin.ext
      have values := congrArg Fin.val (ownerExact.symm.trans assigned.2)
      simpa using values
    have sourceWireExact :
        Internal.sourceRetainedWire source result.sourceRemovedWires
            baseWire = sourceWire := by
      rw [← retainedIndexExact]
      exact Internal.sourceRetainedWire_retainedWireIndex _ _ _ _
    apply (Internal.batchRemovalCandidate_endpoint_iff
      result.plan.removal baseWire endpoint).mpr
    have sourceIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨Internal.sourceRetainedNode source (argumentSiteNodes result.sites)
          endpoint.node, endpoint.port⟩ sourceWire sourceOwner
    change
      Internal.sourceRetainedEndpoint source (argumentSiteNodes result.sites) endpoint ∈
        (source.val.wires
          (Internal.sourceRetainedWire source result.sourceRemovedWires
            baseWire)).endpoints
    rw [sourceWireExact]
    exact sourceIncident
  · intro baseIncident
    have sourceIncident :=
      (Internal.batchRemovalCandidate_endpoint_iff
        result.plan.removal baseWire endpoint).mp baseIncident
    let sourceWire :=
      Internal.sourceRetainedWire source result.sourceRemovedWires baseWire
    let sourceEndpoint : CEndpoint source.val.nodeCount :=
      Internal.sourceRetainedEndpoint source (argumentSiteNodes result.sites) endpoint
    have sourceRequired : sourceEndpoint.port ∈
        source.val.requiredPorts sourceEndpoint.node :=
      ConcreteDiagram.incident_port_required definitions source.val
        source.property sourceWire sourceEndpoint sourceIncident
    have skeletonRequired : endpoint.port ∈
        (replacementSkeleton result.plan).requiredPorts
          (Fin.castAdd result.sites.sites.length endpoint.node) := by
      rw [replacementSkeleton_retained_requiredPorts result.plan endpoint.node]
      exact sourceRequired
    have candidateRequired : candidateEndpoint ∈
        requiredEndpoints (replacementSkeleton result.plan) :=
      required_endpoint_mem (replacementSkeleton result.plan)
        _ _ skeletonRequired
    apply (assigned_endpoint_mem_iff (replacementSkeleton result.plan)
      (replacementOwner result.plan)
      (Fin.castAdd (1 + result.spec.localCount) baseWire)
      candidateEndpoint).mpr
    refine ⟨candidateRequired, ?_⟩
    have sourceOwner : source.val.endpointOwner? sourceEndpoint =
        some sourceWire :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions source.val
        source.property sourceEndpoint.node sourceEndpoint.port
        sourceRequired sourceWire sourceIncident
    have retained : sourceWire ∈
        Internal.retainedWires source result.sourceRemovedWires := by
      unfold sourceWire Internal.sourceRetainedWire
      exact List.get_mem _ baseWire
    unfold candidateEndpoint replacementOwner
    simp only [Fin.addCases_left]
    change source.val.endpointOwner?
        ⟨Internal.sourceRetainedNode source (argumentSiteNodes result.sites)
          endpoint.node, endpoint.port⟩ = some sourceWire at sourceOwner
    rw [sourceOwner]
    change (retainedReplacementWire? result.plan sourceWire).getD
        (replacementHeadWire result.plan) = _
    rw [retainedReplacementWire?_some result.plan sourceWire retained]
    change Fin.castAdd (1 + result.spec.localCount)
        (Internal.retainedWireIndex source result.sourceRemovedWires
          sourceWire retained) =
      Fin.castAdd (1 + result.spec.localCount) baseWire
    exact congrArg (Fin.castAdd (1 + result.spec.localCount))
      (Internal.retainedWireIndex_sourceRetainedWire
        source result.sourceRemovedWires baseWire)

private theorem checkedReplacement_retained_endpoint_iff
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (baseWire : (replacementBase result.plan).WireId)
    (endpoint : CEndpoint (replacementBase result.plan).nodeCount) :
    Internal.checkedEndpoint result.generated
        ⟨Fin.castAdd result.sites.sites.length endpoint.node,
          endpoint.port⟩ ∈
        (result.checked.val.wires
          (Internal.checkedWire result.generated
            (Fin.castAdd (1 + result.spec.localCount) baseWire))).endpoints ↔
      endpoint ∈ ((replacementBase result.plan).wires baseWire).endpoints := by
  rw [Internal.checkedWire_endpoints_transport]
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨actual, actualMember, mapped⟩
    have actualExact : actual =
        (⟨Fin.castAdd result.sites.sites.length endpoint.node,
          endpoint.port⟩ :
          CEndpoint (replacementCandidate result.plan).nodeCount) := by
      cases actual with
      | mk actualNode actualPort =>
        have nodeExact : actualNode =
            Fin.castAdd result.sites.sites.length endpoint.node := by
          apply Fin.ext
          have values := congrArg (fun candidate => candidate.node.val) mapped
          simpa [Internal.checkedEndpoint, Internal.checkedNode] using values
        have portExact : actualPort = endpoint.port :=
          congrArg CEndpoint.port mapped
        subst actualNode
        subst actualPort
        rfl
    subst actual
    exact (result.replacementCandidate_retained_endpoint_iff
      baseWire endpoint).mp actualMember
  · intro member
    apply List.mem_map.mpr
    refine ⟨⟨Fin.castAdd result.sites.sites.length endpoint.node,
      endpoint.port⟩, ?_, rfl⟩
    exact (result.replacementCandidate_retained_endpoint_iff
      baseWire endpoint).mpr member

private theorem targetCommonCore_endpoint_iff
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (targetPlan : Internal.BatchRemovalPlan result.checked []
      (argumentSiteNodes targetSites) result.targetRemovedWires)
    (baseWire : (replacementBase result.plan).WireId)
    (endpoint : CEndpoint (replacementBase result.plan).nodeCount) :
    (⟨targetCoreNodeEquiv result targetSites endpoint.node, endpoint.port⟩ :
        CEndpoint (Internal.batchRemovalCandidate targetPlan).nodeCount) ∈
        ((Internal.batchRemovalCandidate targetPlan).wires
          (targetCoreWireEquiv result baseWire)).endpoints ↔
      endpoint ∈ ((replacementBase result.plan).wires baseWire).endpoints := by
  rw [Internal.batchRemovalCandidate_endpoint_iff]
  change
    ⟨Internal.sourceRetainedNode result.checked (argumentSiteNodes targetSites)
        (targetCoreNodeEquiv result targetSites endpoint.node), endpoint.port⟩ ∈
      (result.checked.val.wires
        (Internal.sourceRetainedWire result.checked
          result.targetRemovedWires
          (targetCoreWireEquiv result baseWire))).endpoints ↔ _
  rw [result.targetCoreNodeEquiv_source_exact targetSites,
    result.targetCoreWireEquiv_source_exact]
  exact result.checkedReplacement_retained_endpoint_iff baseWire endpoint

/-- The source and target argument erasures expose exactly the same common
core.  This total receipt removes the last search-side failure mode from
argument factorization. -/
def commonCoreIso
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire)
    (sourcePlan : Internal.BatchRemovalPlan source []
      (argumentSiteNodes result.sites) result.sourceRemovedWires)
    (targetPlan : Internal.BatchRemovalPlan result.checked []
      (argumentSiteNodes targetSites) result.targetRemovedWires) :
    ConcreteIso (Internal.batchRemovalCandidate sourcePlan)
      (Internal.batchRemovalCandidate targetPlan) := by
  have sourcePlanExact : sourcePlan = result.plan.removal := by
    cases sourcePlan
    cases result.plan.removal
    congr
  subst sourcePlan
  let base := replacementBase result.plan
  have baseWellFormed : base.WellFormed definitions :=
    Internal.batchRemovalCandidate_wellFormed_noRegions result.plan.removal
      result.source_removed_exhausted
  have regionTable : ∀ region,
      (Internal.batchRemovalCandidate targetPlan).regions
          (targetCoreRegionEquiv result region) =
        (base.regions region).rename (targetCoreRegionEquiv result) := by
    intro region
    change Internal.batchRegionTable targetPlan
        (targetCoreRegionEquiv result region) = _
    rw [result.targetCoreRegionEquiv_exact,
      Internal.batchRegionTable_noRegions]
    simpa [base, replacementCandidate, replacementSkeleton] using
      (Internal.checkedRegion_data_rename_noRegions result.generated
        (targetCoreRegionEquiv result)
        result.targetCoreRegionEquiv_exact region)
  have nodeTable : ∀ node,
      (Internal.batchRemovalCandidate targetPlan).nodes
          (targetCoreNodeEquiv result targetSites node) =
        (base.nodes node).rename (targetCoreRegionEquiv result) := by
    intro node
    change Internal.batchNodeTable targetPlan
        (targetCoreNodeEquiv result targetSites node) = _
    rw [Internal.batchNodeTable_noRegions,
      result.targetCoreNodeEquiv_source_exact targetSites]
    have candidateNodeExact :
        (replacementCandidate result.plan).nodes
            (Fin.castAdd result.sites.sites.length node) =
          (replacementBase result.plan).nodes node := by
      unfold replacementCandidate
      rw [assigned_node]
      unfold replacementSkeleton
      simp only [Fin.addCases_left]
    have transported :=
      Internal.checkedNode_data_rename_noRegions result.generated
        (targetCoreRegionEquiv result)
        result.targetCoreRegionEquiv_exact
        (Fin.castAdd result.sites.sites.length node)
    rw [candidateNodeExact] at transported
    exact transported
  have portCorresponds
      (baseWire : base.WireId)
      (endpoint : CEndpoint base.nodeCount)
      (incident : endpoint ∈ (base.wires baseWire).endpoints) :
      PortCorresponds base (Internal.batchRemovalCandidate targetPlan)
        (targetCoreNodeEquiv result targetSites) endpoint
        ⟨targetCoreNodeEquiv result targetSites endpoint.node,
          endpoint.port⟩ := by
    unfold PortCorresponds
    refine ⟨rfl, ?_⟩
    rw [nodeTable]
    cases data : base.nodes endpoint.node with
    | atom region arguments => simp [data, CNode.rename]
    | ref region definition arguments => simp [data, CNode.rename]
    | identity region signature arity =>
        have required := ConcreteDiagram.incident_port_required definitions
          base baseWellFormed baseWire endpoint incident
        unfold ConcreteDiagram.requiredPorts at required
        rw [data] at required
        rcases List.mem_map.mp required with
          ⟨index, _indexMember, portExact⟩
        simp only [data, CNode.rename]
        exact ⟨trivial, trivial, index, index,
          portExact.symm, portExact.symm⟩
  refine
    { regions := targetCoreRegionEquiv result
      nodes := targetCoreNodeEquiv result targetSites
      wires := targetCoreWireEquiv result
      root := ?_
      region_table := regionTable
      node_table := nodeTable
      wire_signature := ?_
      wire_scope := ?_
      endpointMap := fun _ endpoint =>
        ⟨targetCoreNodeEquiv result targetSites endpoint.node,
          endpoint.port⟩
      endpointInverse := fun _ candidate =>
        ⟨(targetCoreNodeEquiv result targetSites).invFun candidate.node,
          candidate.port⟩
      endpointMap_mem := ?_
      endpointInverse_mem := ?_
      endpointMap_left_inv := ?_
      endpointMap_right_inv := ?_
      endpointMap_corresponds := ?_ }
  · change targetCoreRegionEquiv result
        (replacementBase result.plan).root =
      (Internal.batchRemovalCandidate targetPlan).root
    rw [result.targetCoreRegionEquiv_exact,
      Internal.batchRemovalCandidate_root_noRegions targetPlan]
    apply congrArg (Internal.noRegionRemovalEquiv result.checked)
    rw [Internal.checkedRoot_transport result.generated]
    rfl
  · intro baseWire
    rw [Internal.batchRemovalCandidate_wire_signature,
      result.targetCoreWireEquiv_source_exact,
      Internal.checkedWire_signature_transport]
    change ((replacementSkeleton result.plan).wires
        (Fin.castAdd (1 + result.spec.localCount) baseWire)).sig =
      ((replacementBase result.plan).wires baseWire).sig
    rw [replacementSkeleton_retained_wire_signature]
    rfl
  · intro baseWire
    rw [Internal.batchRemovalCandidate_wire_scope_noRegions,
      result.targetCoreWireEquiv_source_exact,
      Internal.checkedWire_scope_transport,
      result.targetCoreRegionEquiv_exact]
    apply congrArg (Internal.noRegionRemovalEquiv result.checked)
    apply congrArg (Internal.checkedRegion result.generated)
    change ((replacementSkeleton result.plan).wires
        (Fin.castAdd (1 + result.spec.localCount) baseWire)).scope =
      ((replacementBase result.plan).wires baseWire).scope
    rw [replacementSkeleton_retained_wire_scope]
    rfl
  · intro baseWire endpoint incident
    exact (result.targetCommonCore_endpoint_iff targetSites targetPlan
      baseWire endpoint).mpr incident
  · intro baseWire candidate incident
    let endpoint : CEndpoint base.nodeCount :=
      ⟨(targetCoreNodeEquiv result targetSites).invFun candidate.node,
        candidate.port⟩
    have candidateNodeExact :
        targetCoreNodeEquiv result targetSites endpoint.node =
          candidate.node :=
      (targetCoreNodeEquiv result targetSites).right_inv candidate.node
    have candidateExact :
        (⟨targetCoreNodeEquiv result targetSites endpoint.node,
            endpoint.port⟩ :
          CEndpoint (Internal.batchRemovalCandidate targetPlan).nodeCount) =
        candidate := by
      cases candidate
      simp only [endpoint] at candidateNodeExact ⊢
      cases candidateNodeExact
      rfl
    have baseIncident : endpoint ∈ (base.wires baseWire).endpoints := by
      apply (result.targetCommonCore_endpoint_iff targetSites targetPlan
        baseWire endpoint).mp
      rwa [candidateExact]
    exact baseIncident
  · intro baseWire endpoint incident
    cases endpoint
    simp only
    congr
  · intro baseWire candidate incident
    cases candidate
    simp only
    congr
  · intro baseWire endpoint incident
    exact portCorresponds baseWire endpoint incident

/-- Exact target image of one source wire retained by an argument
replacement.  Compiler ambient transport consumes this construction-owned
map instead of rediscovering dense identifiers arithmetically. -/
def retainedWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source result.sourceRemovedWires) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd (1 + result.spec.localCount)
      (Internal.retainedWireIndex source result.sourceRemovedWires
        sourceWire retained))

/-- Retained ambient transport preserves its exact signature. -/
theorem retainedWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source result.sourceRemovedWires) :
    (result.checked.val.wires
        (result.retainedWire sourceWire retained)).sig =
      (source.val.wires sourceWire).sig := by
  unfold retainedWire
  rw [Internal.checkedWire_signature_transport]
  unfold replacementCandidate
  rw [assigned_wire_signature]
  rw [replacementSkeleton_retained_wire_signature]
  change sourceWire ∈
    Internal.retainedWires source (wire :: result.spec.removedWires) at retained
  change
    (source.val.wires
      (Internal.sourceRetainedWire source
        (wire :: result.spec.removedWires)
        (Internal.retainedWireIndex source
          (wire :: result.spec.removedWires) sourceWire retained))).sig =
      (source.val.wires sourceWire).sig
  rw [Internal.sourceRetainedWire_retainedWireIndex source
    (wire :: result.spec.removedWires) sourceWire retained]

/-- A retained ambient wire is never the freshly allocated relation head. -/
theorem retainedWire_ne_targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source result.sourceRemovedWires) :
    result.retainedWire sourceWire retained ≠ result.targetWire := by
  intro same
  have values := congrArg Fin.val same
  unfold retainedWire at values
  rw [result.targetWire_exact] at values
  simp [Internal.checkedWire, replacementCandidateWire,
    replacementHeadWire] at values
  have bound :=
    (Internal.retainedWireIndex source result.sourceRemovedWires
      sourceWire retained).isLt
  omega

end ArgumentResult

end ConcreteWirePrimitive

end VisualProof
