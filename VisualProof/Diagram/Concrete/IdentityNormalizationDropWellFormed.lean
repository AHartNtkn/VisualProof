import VisualProof.Diagram.Concrete.IdentityNormalizationCore

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

private def dropNodes
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List source.val.NodeId :=
  retainedNodes source.val [node]

private def dropSourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    source.val.NodeId :=
  (dropNodes source node).get target

private def dropSourceEndpoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint (dropNodes source node).length) :
    CEndpoint source.val.nodeCount :=
  ⟨dropSourceNode source node endpoint.node, endpoint.port⟩

private def dropTargetEndpoint?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (CEndpoint (dropNodes source node).length) :=
  if decide (endpoint.node ≠ node) = true then
    reindexEndpoint? (dropNodes source node) endpoint
  else
    none

private theorem dropNodes_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    (dropNodes source node).Nodup := by
  exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem dropSourceNode_ne
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    dropSourceNode source node target ≠ node := by
  unfold dropSourceNode dropNodes retainedNodes
  have member :=
    List.get_mem
      (source.val.nodesList.filter fun candidate =>
        decide (candidate ∉ [node]))
      target
  have accepted :
      decide
          ((source.val.nodesList.filter fun candidate =>
              decide (candidate ∉ [node])).get target ∉ [node]) =
        true :=
    (List.mem_filter.mp member).2
  have notMember :
      (source.val.nodesList.filter fun candidate =>
          decide (candidate ∉ [node])).get target ∉ [node] :=
    of_decide_eq_true accepted
  simpa using notMember

@[simp] private theorem indexOf_dropSourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    Data.Finite.indexOf? (dropNodes source node)
        (dropSourceNode source node target) =
      some target := by
  exact Data.Finite.indexOf?_get_eq_some_of_nodup
    (dropNodes_nodup source node) target

private theorem dropEndpoint_mem_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint (dropNodes source node).length) :
    endpoint ∈
        reindexEndpoints (dropNodes source node)
          (eraseNodeEndpoints node
            (source.val.wires wire).endpoints) ↔
      dropSourceEndpoint source node endpoint ∈
        (source.val.wires wire).endpoints := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, retained, mapped⟩
    have candidateMember :
        candidate ∈ (source.val.wires wire).endpoints :=
      (List.mem_filter.mp retained).1
    unfold reindexEndpoint? at mapped
    cases found :
        Data.Finite.indexOf? (dropNodes source node) candidate.node with
    | none =>
        simp [found] at mapped
    | some targetNode =>
        have mappedEndpoint :
            (⟨targetNode, candidate.port⟩ :
              CEndpoint (dropNodes source node).length) = endpoint :=
          Option.some.inj (by simpa [found] using mapped)
        have sourceNode :
            candidate.node =
              dropSourceNode source node endpoint.node := by
          have indexed :=
            Data.Finite.indexOf?_sound found
          have targetNodeEq : targetNode = endpoint.node :=
            congrArg CEndpoint.node mappedEndpoint
          simpa [dropSourceNode, targetNodeEq] using indexed.symm
        have sourcePort : candidate.port = endpoint.port :=
          congrArg CEndpoint.port mappedEndpoint
        cases candidate with
        | mk candidateNode candidatePort =>
            cases endpoint with
            | mk endpointNode endpointPort =>
                simp only at sourceNode sourcePort ⊢
                subst candidateNode
                subst candidatePort
                exact candidateMember
  · intro incident
    let sourceEndpoint := dropSourceEndpoint source node endpoint
    have retained :
        sourceEndpoint ∈
          eraseNodeEndpoints node
            (source.val.wires wire).endpoints := by
      apply List.mem_filter.mpr
      exact ⟨incident, by
        simp [sourceEndpoint, dropSourceEndpoint,
          dropSourceNode_ne source node endpoint.node]⟩
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint, retained, ?_⟩
    unfold reindexEndpoint?
    simp [sourceEndpoint, dropSourceEndpoint]

private def dropSourceWire
    (source : CheckedDiagram definitions)
    (target : Fin source.val.wiresList.length) :
    source.val.WireId :=
  source.val.wiresList.get target

private def dropTargetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Fin source.val.wiresList.length :=
  (Data.Finite.indexOf? source.val.wiresList wire).get
    (Data.Finite.indexOf?_isSome_iff.mpr
      (Data.Finite.mem_allFin wire))

@[simp] private theorem dropSourceWire_dropTargetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    dropSourceWire source (dropTargetWire source wire) = wire := by
  unfold dropSourceWire dropTargetWire
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr
      (Data.Finite.mem_allFin wire))

@[simp] private theorem dropCandidate_node
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (target :
      (dropCandidate source node eligible).NodeId) :
    (dropCandidate source node eligible).nodes target =
      source.val.nodes (dropSourceNode source node target) := by
  rfl

@[simp] private theorem dropCandidate_wire_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (target :
      (dropCandidate source node eligible).WireId) :
    ((dropCandidate source node eligible).wires target).sig =
      (source.val.wires (dropSourceWire source target)).sig := by
  rfl

@[simp] private theorem dropCandidate_wire_scope
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (target :
      (dropCandidate source node eligible).WireId) :
    ((dropCandidate source node eligible).wires target).scope =
      (source.val.wires (dropSourceWire source target)).scope := by
  rfl

private theorem dropCandidate_endpoint_mem_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire :
      (dropCandidate source node eligible).WireId)
    (endpoint :
      CEndpoint (dropCandidate source node eligible).nodeCount) :
    endpoint ∈
        ((dropCandidate source node eligible).wires wire).endpoints ↔
      dropSourceEndpoint source node endpoint ∈
        (source.val.wires (dropSourceWire source wire)).endpoints := by
  exact dropEndpoint_mem_iff source node
    (dropSourceWire source wire) endpoint

@[simp] private theorem dropSourceEndpoint_mk
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (target : (dropCandidate source node eligible).NodeId)
    (port : CPort) :
    dropSourceEndpoint source node
        (⟨target, port⟩ :
          CEndpoint (dropCandidate source node eligible).nodeCount) =
      (⟨dropSourceNode source node target, port⟩ :
        CEndpoint source.val.nodeCount) := by
  rfl

private theorem dropCandidate_requiredPorts
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (target :
      (dropCandidate source node eligible).NodeId) :
    (dropCandidate source node eligible).requiredPorts target =
      source.val.requiredPorts (dropSourceNode source node target) := by
  unfold ConcreteDiagram.requiredPorts
  rw [dropCandidate_node]
  cases source.val.nodes (dropSourceNode source node target) <;> rfl

private theorem dropSourceWire_injective
    (source : CheckedDiagram definitions) :
    Function.Injective (dropSourceWire source) := by
  intro left right equality
  apply Fin.ext
  exact
    (List.getElem_inj
      (Data.Finite.allFin_nodup source.val.wireCount)).mp
      (by simpa [dropSourceWire] using equality)

private theorem dropSourceNode_injective
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Function.Injective (dropSourceNode source node) := by
  intro left right equality
  apply Fin.ext
  exact
    (List.getElem_inj (dropNodes_nodup source node)).mp
      (by simpa [dropSourceNode] using equality)

private theorem dropTargetEndpoint?_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (sourceEndpoint : CEndpoint source.val.nodeCount)
    (targetEndpoint : CEndpoint (dropNodes source node).length)
    (mapped :
      dropTargetEndpoint? source node sourceEndpoint =
        some targetEndpoint) :
    sourceEndpoint =
      dropSourceEndpoint source node targetEndpoint := by
  unfold dropTargetEndpoint? at mapped
  split at mapped
  · unfold reindexEndpoint? at mapped
    cases found :
        Data.Finite.indexOf? (dropNodes source node)
          sourceEndpoint.node with
    | none =>
        simp [found] at mapped
    | some targetNode =>
        have endpointEquality :
            (⟨targetNode, sourceEndpoint.port⟩ :
              CEndpoint (dropNodes source node).length) =
              targetEndpoint :=
          Option.some.inj (by simpa [found] using mapped)
        have sourceNode :
            sourceEndpoint.node =
              dropSourceNode source node targetEndpoint.node := by
          have indexed := Data.Finite.indexOf?_sound found
          have targetNodeEquality :
              targetNode = targetEndpoint.node :=
            congrArg CEndpoint.node endpointEquality
          simpa [dropSourceNode, targetNodeEquality] using indexed.symm
        have sourcePort :
            sourceEndpoint.port = targetEndpoint.port :=
          congrArg CEndpoint.port endpointEquality
        cases sourceEndpoint
        cases targetEndpoint
        simp_all [dropSourceEndpoint]
  · simp at mapped

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem map_self (values : List α) :
    values.map (fun value => value) = values := by
  exact List.map_id values

private theorem flatMap_get_allFin
    (values : List α) (function : α → List β) :
    (Data.Finite.allFin values.length).flatMap
        (fun index => function (values.get index)) =
      values.flatMap function := by
  rw [← List.flatMap_map]
  rw [map_get_allFin]

private theorem dropCandidate_endpointValues
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).endpointOccurrences.map Prod.snd =
      (source.val.endpointOccurrences.map Prod.snd).filterMap
        (dropTargetEndpoint? source node) := by
  simp only [ConcreteDiagram.endpointOccurrences, List.map_flatMap,
    List.map_map, Function.comp_def]
  simp only [map_self]
  change
    (Data.Finite.allFin source.val.wiresList.length).flatMap
        (fun target =>
          reindexEndpoints (dropNodes source node)
            (eraseNodeEndpoints node
              (source.val.wires
                (source.val.wiresList.get target)).endpoints)) =
      (source.val.wiresList.flatMap fun wire =>
        (source.val.wires wire).endpoints).filterMap
          (dropTargetEndpoint? source node)
  rw [List.filterMap_flatMap]
  rw [flatMap_get_allFin source.val.wiresList
    (fun wire =>
      reindexEndpoints (dropNodes source node)
        (eraseNodeEndpoints node
          (source.val.wires wire).endpoints))]
  unfold dropTargetEndpoint?
  simp [reindexEndpoints,
    eraseNodeEndpoints, List.filterMap_filter]

private theorem eraseDups_length_le
    [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α] (values : List α)
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons, Nat.succ.injEq] at sameLength
      let retained := tail.filter fun value => !value == head
      have retainedLength : retained.length = tail.length := by
        apply Nat.le_antisymm
        · exact List.length_filter_le _ tail
        · rw [← sameLength]
          exact eraseDups_length_le retained
      have retainedEquality : retained = tail :=
        List.Sublist.eq_of_length List.filter_sublist retainedLength
      rw [List.nodup_cons]
      constructor
      · intro member
        have accepted :
            (!head == head) = true := by
          have : head ∈ retained := by
            rw [retainedEquality]
            exact member
          exact (List.mem_filter.mp this).2
        simp at accepted
      · apply nodup_of_eraseDups_length_eq tail
        simpa [retained, retainedEquality] using sameLength
termination_by values.length
decreasing_by simp_wf

private theorem eraseDups_eq_self_of_nodup
    [BEq α] [LawfulBEq α] (values : List α)
    (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [List.nodup_cons] at nodup
      rw [List.eraseDups_cons]
      have filterEquality :
          tail.filter (fun value => !value == head) = tail := by
        rw [List.filter_eq_self]
        intro value member
        have different : value ≠ head :=
          fun equality => nodup.1 (equality ▸ member)
        simp [different]
      rw [filterEquality]
      rw [ih nodup.2]

private theorem source_endpointValues_nodup
    (source : CheckedDiagram definitions) :
    (source.val.endpointOccurrences.map Prod.snd).Nodup := by
  apply nodup_of_eraseDups_length_eq
  have noDuplicates := source.property.no_duplicate_endpoints
  unfold NoDuplicateEndpoints at noDuplicates
  simpa using noDuplicates

private theorem dropCandidate_endpointValues_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    ((dropCandidate source node eligible).endpointOccurrences.map
      Prod.snd).Nodup := by
  rw [dropCandidate_endpointValues]
  rw [List.nodup_iff_pairwise_ne]
  exact
    (source_endpointValues_nodup source).filterMap
      (dropTargetEndpoint? source node)
      (by
        intro left right different
        intro leftTarget leftMapped rightTarget rightMapped
        intro targetEquality
        apply different
        rw [dropTargetEndpoint?_source source node left
          leftTarget leftMapped]
        rw [dropTargetEndpoint?_source source node right
          rightTarget rightMapped]
        rw [targetEquality])

private theorem dropCandidate_no_duplicate_endpoints
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).NoDuplicateEndpoints := by
  unfold NoDuplicateEndpoints
  rw [eraseDups_eq_self_of_nodup _
    (dropCandidate_endpointValues_nodup source node eligible)]
  exact List.length_map _

private theorem dropCandidate_occurrence
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire : (dropCandidate source node eligible).WireId)
    (endpoint :
      CEndpoint (dropCandidate source node eligible).nodeCount)
    (incident :
      endpoint ∈
        ((dropCandidate source node eligible).wires wire).endpoints) :
    (wire, endpoint) ∈
      (dropCandidate source node eligible).endpointOccurrences := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
  refine ⟨wire, Data.Finite.mem_allFin wire, ?_⟩
  exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩

private theorem dropCandidate_ports_covered_exactly_once
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).PortsCoveredExactlyOnce := by
  unfold PortsCoveredExactlyOnce
  apply List.all_eq_true.mpr
  intro target _
  apply List.all_eq_true.mpr
  intro port required
  have sourceRequired :
      port ∈
        source.val.requiredPorts
          (dropSourceNode source node target) := by
    rw [← dropCandidate_requiredPorts source node eligible target]
    exact required
  obtain ⟨sourceWire, sourceOwner⟩ :=
    endpointOwner?_complete definitions source.val source.property
      (dropSourceNode source node target) port sourceRequired
  have sourceIncident :
      (dropSourceEndpoint source node ⟨target, port⟩) ∈
        (source.val.wires sourceWire).endpoints := by
    exact endpointOwner?_incident source.val
      (dropSourceEndpoint source node ⟨target, port⟩)
      sourceWire sourceOwner
  let targetWire := dropTargetWire source sourceWire
  let targetEndpoint :
      CEndpoint (dropCandidate source node eligible).nodeCount :=
    ⟨target, port⟩
  have targetIncident :
      targetEndpoint ∈
        ((dropCandidate source node eligible).wires
          targetWire).endpoints := by
    apply (dropCandidate_endpoint_mem_iff source node eligible
      targetWire targetEndpoint).mpr
    simpa [targetWire] using sourceIncident
  have occurrence :
      (targetWire, targetEndpoint) ∈
        (dropCandidate source node eligible).endpointOccurrences :=
    dropCandidate_occurrence source node eligible
      targetWire targetEndpoint targetIncident
  have endpointMember :
      targetEndpoint ∈
        (dropCandidate source node eligible).endpointOccurrences.map
          Prod.snd :=
    List.mem_map.mpr ⟨(targetWire, targetEndpoint), occurrence, rfl⟩
  have counted :=
    (dropCandidate_endpointValues_nodup source node eligible).count
      (a := targetEndpoint)
  rw [if_pos endpointMember] at counted
  rw [List.count_eq_length_filter] at counted
  rw [List.filter_map] at counted
  simp only [List.length_map] at counted
  have countOne :
      ((dropCandidate source node eligible).endpointOccurrences.filter
        fun occurrence => occurrence.2 == targetEndpoint).length = 1 :=
    counted
  have ownerSome :
      ((dropCandidate source node eligible).endpointOwner?
        targetEndpoint).isSome = true := by
    unfold ConcreteDiagram.endpointOwner?
    simp only [Option.isSome_map]
    rw [List.find?_isSome]
    exact ⟨(targetWire, targetEndpoint), occurrence,
      beq_self_eq_true _⟩
  rw [Bool.and_eq_true]
  constructor
  · apply beq_iff_eq.mpr
    exact countOne
  · exact ownerSome

private theorem occurrence_incident
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (occurs : (wire, endpoint) ∈ diagram.endpointOccurrences) :
    endpoint ∈ (diagram.wires wire).endpoints := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap] at occurs
  rcases occurs with ⟨candidate, _, member⟩
  simp only [List.mem_map] at member
  rcases member with ⟨candidateEndpoint, incident, equality⟩
  cases equality
  exact incident

private theorem dropCandidate_root_is_sheet
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).RootIsSheet := by
  exact source.property.root_is_sheet

@[simp] private theorem dropCandidate_region
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : (dropCandidate source node eligible).RegionId) :
    (dropCandidate source node eligible).regions region =
      source.val.regions region := by
  rfl

@[simp] private theorem dropCandidate_climb
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (steps : Nat)
    (region : source.val.RegionId) :
    (dropCandidate source node eligible).climb steps region =
      source.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      unfold ConcreteDiagram.climb
      rw [dropCandidate_region]
      cases source.val.regions region with
      | sheet => rfl
      | cut parent => simpa using ih parent

private theorem dropCandidate_only_root_is_sheet
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).OnlyRootIsSheet := by
  simpa [OnlyRootIsSheet, dropCandidate] using
    source.property.only_root_is_sheet

private theorem dropCandidate_all_regions_reach_root
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).AllRegionsReachRoot := by
  unfold AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin _)
  unfold ConcreteDiagram.Encloses at sourceChecked ⊢
  simpa using sourceChecked

private theorem dropCandidate_references_match
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).ReferencesMatch definitions := by
  unfold ReferencesMatch
  apply List.all_eq_true.mpr
  intro target _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.references_match)
      (dropSourceNode source node target)
      (Data.Finite.mem_allFin _)
  cases nodeData :
      source.val.nodes (dropSourceNode source node target) <;>
    simp [dropCandidate_node, nodeData] at sourceChecked ⊢ <;>
    assumption

private theorem dropCandidate_ports_exist
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).PortsExist := by
  unfold PortsExist
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have targetIncident :=
    occurrence_incident (dropCandidate source node eligible)
      wire endpoint occurrence
  have sourceIncident :=
    (dropCandidate_endpoint_mem_iff source node eligible
      wire endpoint).mp targetIncident
  have sourceRequired :=
    incident_port_required definitions source.val source.property
      (dropSourceWire source wire)
      (dropSourceEndpoint source node endpoint) sourceIncident
  apply decide_eq_true
  rw [dropCandidate_requiredPorts]
  exact sourceRequired

private theorem dropCandidate_identities_have_arity
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).IdentitiesHaveArity := by
  unfold IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro target _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.identities_have_arity)
      (dropSourceNode source node target)
      (Data.Finite.mem_allFin _)
  cases nodeData :
      source.val.nodes (dropSourceNode source node target) <;>
    simp [dropCandidate_node, nodeData] at sourceChecked ⊢ <;>
    assumption

private theorem dropCandidate_wire_scopes_enclose
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).WireScopesEnclose := by
  unfold WireScopesEnclose
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have targetIncident :=
    occurrence_incident (dropCandidate source node eligible)
      wire endpoint occurrence
  have sourceIncident :=
    (dropCandidate_endpoint_mem_iff source node eligible
      wire endpoint).mp targetIncident
  have sourceChecked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (dropSourceWire source wire,
        dropSourceEndpoint source node endpoint)
      (by
        simp only [ConcreteDiagram.endpointOccurrences,
          List.mem_flatMap]
        refine ⟨dropSourceWire source wire,
          Data.Finite.mem_allFin _, ?_⟩
        exact List.mem_map.mpr
          ⟨dropSourceEndpoint source node endpoint,
            sourceIncident, rfl⟩)
  unfold ConcreteDiagram.Encloses at sourceChecked ⊢
  simpa [dropSourceEndpoint] using sourceChecked

private theorem dropCandidate_owner_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (endpoint :
      CEndpoint (dropCandidate source node eligible).nodeCount)
    (wire : (dropCandidate source node eligible).WireId)
    (owner :
      (dropCandidate source node eligible).endpointOwner? endpoint =
        some wire) :
    source.val.endpointOwner?
        (dropSourceEndpoint source node endpoint) =
      some (dropSourceWire source wire) := by
  have targetIncident :=
    endpointOwner?_incident (dropCandidate source node eligible)
      endpoint wire owner
  have sourceIncident :=
    (dropCandidate_endpoint_mem_iff source node eligible
      wire endpoint).mp targetIncident
  have sourceRequired :=
    incident_port_required definitions source.val source.property
      (dropSourceWire source wire)
      (dropSourceEndpoint source node endpoint) sourceIncident
  exact endpointOwner?_eq_of_incident definitions source.val
    source.property
    (dropSourceEndpoint source node endpoint).node
    (dropSourceEndpoint source node endpoint).port
    sourceRequired (dropSourceWire source wire) sourceIncident

private theorem dropCandidate_port_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (endpoint :
      CEndpoint (dropCandidate source node eligible).nodeCount)
    (expected : Sig)
    (required :
      endpoint.port ∈
        (dropCandidate source node eligible).requiredPorts endpoint.node)
    (sourceTyped :
      ∀ wire,
        source.val.endpointOwner?
            (dropSourceEndpoint source node endpoint) =
          some wire →
        (source.val.wires wire).sig = expected) :
    (match (dropCandidate source node eligible).endpointOwner?
        endpoint with
      | some wire =>
          ((dropCandidate source node eligible).wires wire).sig ==
            expected
      | none => false) = true := by
  have nodeChecked :=
    (List.all_eq_true.mp
      (dropCandidate_ports_covered_exactly_once source node eligible))
      endpoint.node (Data.Finite.mem_allFin _)
  have portChecked :=
    (List.all_eq_true.mp nodeChecked) endpoint.port required
  rw [Bool.and_eq_true] at portChecked
  obtain ⟨wire, owner⟩ :=
    Option.isSome_iff_exists.mp portChecked.2
  rw [owner]
  apply beq_iff_eq.mpr
  rw [dropCandidate_wire_signature]
  exact sourceTyped (dropSourceWire source wire)
    (dropCandidate_owner_source source node eligible
      endpoint wire owner)

private theorem dropCandidate_atom_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).AtomPortsTyped := by
  unfold AtomPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.atom_ports_typed)
      (dropSourceNode source node target)
      (Data.Finite.mem_allFin _)
  cases nodeData :
      source.val.nodes (dropSourceNode source node target) with
  | atom region args =>
      rw [nodeData] at sourceChecked
      rw [Bool.and_eq_true] at sourceChecked
      rw [dropCandidate_node, nodeData]
      rw [Bool.and_eq_true]
      constructor
      · let endpoint :
            CEndpoint (dropCandidate source node eligible).nodeCount :=
          ⟨target, .head⟩
        have typed :=
          dropCandidate_port_typed source node eligible
            endpoint (.rel args)
            (by
              simp [endpoint, ConcreteDiagram.requiredPorts, nodeData])
            (by
              intro wire owner
              have sourceOwner :
                  source.val.endpointOwner?
                      (⟨dropSourceNode source node target, .head⟩ :
                        CEndpoint source.val.nodeCount) =
                    some wire := by
                simpa [endpoint] using owner
              rw [sourceOwner] at sourceChecked
              exact eq_of_beq sourceChecked.1)
        have endpointEquality :
            endpoint =
              (⟨target, .head⟩ :
                CEndpoint
                  (dropCandidate source node eligible).nodeCount) := by
          rfl
        rw [endpointEquality] at typed
        cases owner :
            (dropCandidate source node eligible).endpointOwner?
              (⟨target, .head⟩ :
                CEndpoint
                  (dropCandidate source node eligible).nodeCount) <;>
          simp [owner] at typed ⊢ <;> assumption
      · apply List.all_eq_true.mpr
        intro index member
        have bound : index < args.length := by simpa using member
        rw [List.getElem?_eq_getElem bound]
        let endpoint :
            CEndpoint (dropCandidate source node eligible).nodeCount :=
          ⟨target, .arg index⟩
        have typed :=
          dropCandidate_port_typed source node eligible
            endpoint args[index]
            (by
              simp [endpoint, ConcreteDiagram.requiredPorts,
                nodeData, bound])
            (by
              intro wire owner
              have sourceOwner :
                  source.val.endpointOwner?
                      (⟨dropSourceNode source node target, .arg index⟩ :
                        CEndpoint source.val.nodeCount) =
                    some wire := by
                simpa [endpoint] using owner
              have indexChecked :=
                (List.all_eq_true.mp sourceChecked.2) index member
              rw [sourceOwner, List.getElem?_eq_getElem bound] at indexChecked
              exact eq_of_beq indexChecked)
        have endpointEquality :
            endpoint =
              (⟨target, .arg index⟩ :
                CEndpoint
                  (dropCandidate source node eligible).nodeCount) := by
          rfl
        rw [endpointEquality] at typed
        cases owner :
            (dropCandidate source node eligible).endpointOwner?
              (⟨target, .arg index⟩ :
                CEndpoint
                  (dropCandidate source node eligible).nodeCount) <;>
          simp [owner] at typed ⊢ <;> assumption
  | ref region definition args =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢
  | identity region sig arity =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢

private theorem dropCandidate_ref_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).RefPortsTyped := by
  unfold RefPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.ref_ports_typed)
      (dropSourceNode source node target)
      (Data.Finite.mem_allFin _)
  cases nodeData :
      source.val.nodes (dropSourceNode source node target) with
  | atom region args =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢
  | ref region definition args =>
      rw [nodeData] at sourceChecked
      rw [dropCandidate_node, nodeData]
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < args.length := by simpa using member
      rw [List.getElem?_eq_getElem bound]
      let endpoint :
          CEndpoint (dropCandidate source node eligible).nodeCount :=
        ⟨target, .arg index⟩
      have typed :=
        dropCandidate_port_typed source node eligible
          endpoint args[index]
          (by
            simp [endpoint, ConcreteDiagram.requiredPorts,
              nodeData, bound])
          (by
            intro wire owner
            have sourceOwner :
                source.val.endpointOwner?
                    (⟨dropSourceNode source node target, .arg index⟩ :
                      CEndpoint source.val.nodeCount) =
                  some wire := by
              simpa [endpoint] using owner
            have indexChecked :=
              (List.all_eq_true.mp sourceChecked) index member
            rw [sourceOwner, List.getElem?_eq_getElem bound] at indexChecked
            exact eq_of_beq indexChecked)
      have endpointEquality :
          endpoint =
            (⟨target, .arg index⟩ :
              CEndpoint
                (dropCandidate source node eligible).nodeCount) := by
        rfl
      rw [endpointEquality] at typed
      cases owner :
          (dropCandidate source node eligible).endpointOwner?
            (⟨target, .arg index⟩ :
              CEndpoint
                (dropCandidate source node eligible).nodeCount) <;>
        simp [owner] at typed ⊢ <;> assumption
  | identity region sig arity =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢

private theorem dropCandidate_identity_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).IdentityPortsTyped := by
  unfold IdentityPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.identity_ports_typed)
      (dropSourceNode source node target)
      (Data.Finite.mem_allFin _)
  cases nodeData :
      source.val.nodes (dropSourceNode source node target) with
  | atom region args =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢
  | ref region definition args =>
      simp [dropCandidate_node, nodeData] at sourceChecked ⊢
  | identity region sig arity =>
      rw [nodeData] at sourceChecked
      rw [dropCandidate_node, nodeData]
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arity := by simpa using member
      let endpoint :
          CEndpoint (dropCandidate source node eligible).nodeCount :=
        ⟨target, .identity index⟩
      have typed :=
        dropCandidate_port_typed source node eligible
          endpoint sig
          (by
            simp [endpoint, ConcreteDiagram.requiredPorts,
              nodeData, bound])
          (by
            intro wire owner
            have sourceOwner :
                source.val.endpointOwner?
                    (⟨dropSourceNode source node target,
                      .identity index⟩ :
                      CEndpoint source.val.nodeCount) =
                  some wire := by
              simpa [endpoint] using owner
            have indexChecked :=
              (List.all_eq_true.mp sourceChecked) index member
            rw [sourceOwner] at indexChecked
            exact eq_of_beq indexChecked)
      have endpointEquality :
          endpoint =
            (⟨target, .identity index⟩ :
              CEndpoint
                (dropCandidate source node eligible).nodeCount) := by
        rfl
      rw [endpointEquality] at typed
      cases owner :
          (dropCandidate source node eligible).endpointOwner?
            (⟨target, .identity index⟩ :
              CEndpoint
                (dropCandidate source node eligible).nodeCount) <;>
        simp [owner] at typed ⊢ <;> assumption

theorem dropCandidate_wellFormed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).WellFormed definitions where
  root_is_sheet :=
    dropCandidate_root_is_sheet source node eligible
  only_root_is_sheet :=
    dropCandidate_only_root_is_sheet source node eligible
  all_regions_reach_root :=
    dropCandidate_all_regions_reach_root source node eligible
  references_match :=
    dropCandidate_references_match source node eligible
  ports_exist :=
    dropCandidate_ports_exist source node eligible
  no_duplicate_endpoints :=
    dropCandidate_no_duplicate_endpoints source node eligible
  ports_covered_exactly_once :=
    dropCandidate_ports_covered_exactly_once source node eligible
  atom_ports_typed :=
    dropCandidate_atom_ports_typed source node eligible
  ref_ports_typed :=
    dropCandidate_ref_ports_typed source node eligible
  identities_have_arity :=
    dropCandidate_identities_have_arity source node eligible
  identity_ports_typed :=
    dropCandidate_identity_ports_typed source node eligible
  wire_scopes_enclose :=
    dropCandidate_wire_scopes_enclose source node eligible

end IdentityNormalizationCore

end ConcreteDiagram

end VisualProof
