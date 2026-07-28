import VisualProof.Diagram.Concrete.IdentityNormalizationCore

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

private abbrev fusionNodes
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) :
    List source.val.NodeId :=
  retainedNodes source.val [right]

private abbrev fusionIncident
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    List source.val.WireId :=
  (source.val.identityIncidentWires left ++
    source.val.identityIncidentWires right).eraseDups

private def fusionSourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (target : Fin (fusionNodes source right).length) :
    source.val.NodeId :=
  (fusionNodes source right).get target

private def fusionSourceEndpoint
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (endpoint : CEndpoint (fusionNodes source right).length) :
    CEndpoint source.val.nodeCount :=
  ⟨fusionSourceNode source right endpoint.node, endpoint.port⟩

private def fusionSourceWire
    (source : CheckedDiagram definitions)
    (target : Fin source.val.wiresList.length) :
    source.val.WireId :=
  source.val.wiresList.get target

private def fusionTargetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Fin source.val.wiresList.length :=
  ⟨wire.val, by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, wire.isLt]⟩

@[simp] private theorem fusionSourceWire_target
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    fusionSourceWire source (fusionTargetWire source wire) = wire := by
  apply Fin.ext
  simp [fusionSourceWire, fusionTargetWire,
    ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]

private theorem fusionSourceWire_injective
    (source : CheckedDiagram definitions) :
    Function.Injective (fusionSourceWire source) := by
  intro left right equality
  apply Fin.ext
  exact
    (List.getElem_inj
      (Data.Finite.allFin_nodup source.val.wireCount)).mp
      (by simpa [fusionSourceWire] using equality)

private theorem fusionNodes_nodup
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) :
    (fusionNodes source right).Nodup := by
  exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem fusionSourceNode_ne_right
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (target : Fin (fusionNodes source right).length) :
    fusionSourceNode source right target ≠ right := by
  have member := List.get_mem (fusionNodes source right) target
  have filteredMember :
      fusionSourceNode source right target ∈
        source.val.nodesList.filter fun candidate =>
          decide (candidate ∉ [right]) := by
    simp [fusionSourceNode, fusionNodes, retainedNodes] at member ⊢
  have accepted :
      decide (fusionSourceNode source right target ∉ [right]) = true := by
    exact (List.mem_filter.mp filteredMember).2
  have notMember :
      fusionSourceNode source right target ∉ [right] :=
    of_decide_eq_true accepted
  simpa using notMember

@[simp] private theorem indexOf_fusionSourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (target : Fin (fusionNodes source right).length) :
    Data.Finite.indexOf? (fusionNodes source right)
        (fusionSourceNode source right target) =
      some target := by
  exact Data.Finite.indexOf?_get_eq_some_of_nodup
    (fusionNodes_nodup source right) target

private theorem left_mem_fusionNodes
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) :
    left ∈ fusionNodes source right := by
  apply List.mem_filter.mpr
  exact ⟨Data.Finite.mem_allFin left, by simp [distinct]⟩

private def fusionLeftNode
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) :
    Fin (fusionNodes source right).length :=
  (Data.Finite.indexOf? (fusionNodes source right) left).get
    (by
      rw [Data.Finite.indexOf?_isSome_iff]
      exact left_mem_fusionNodes source left right distinct)

@[simp] private theorem fusionSourceNode_left
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) :
    fusionSourceNode source right
        (fusionLeftNode source left right distinct) =
      left := by
  unfold fusionSourceNode fusionLeftNode
  let found :=
    Data.Finite.indexOf? (fusionNodes source right) left
  have someFound : found.isSome = true := by
    rw [Data.Finite.indexOf?_isSome_iff]
    exact left_mem_fusionNodes source left right distinct
  obtain ⟨index, equation⟩ := Option.isSome_iff_exists.mp someFound
  have getEquality :
      found.get someFound = index :=
    Option.get_of_eq_some someFound equation
  rw [getEquality]
  exact Data.Finite.indexOf?_sound equation

private theorem fusionRetainedEndpoint_mem_iff
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint (fusionNodes source right).length)
    (notLeft :
      fusionSourceNode source right endpoint.node ≠ left) :
    endpoint ∈
        reindexEndpoints (fusionNodes source right)
          (eraseTwoNodeEndpoints left right
            (source.val.wires wire).endpoints) ↔
      fusionSourceEndpoint source right endpoint ∈
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
        Data.Finite.indexOf? (fusionNodes source right) candidate.node with
    | none =>
        simp [found] at mapped
    | some targetNode =>
        have mappedEndpoint :
            (⟨targetNode, candidate.port⟩ :
              CEndpoint (fusionNodes source right).length) = endpoint :=
          Option.some.inj (by simpa [found] using mapped)
        have sourceNode :
            candidate.node =
              fusionSourceNode source right endpoint.node := by
          have indexed :=
            Data.Finite.indexOf?_sound found
          have targetNodeEq : targetNode = endpoint.node :=
            congrArg CEndpoint.node mappedEndpoint
          simpa [fusionSourceNode, targetNodeEq] using indexed.symm
        have sourcePort : candidate.port = endpoint.port :=
          congrArg CEndpoint.port mappedEndpoint
        cases candidate
        cases endpoint
        simp_all [fusionSourceEndpoint]
  · intro incident
    let sourceEndpoint := fusionSourceEndpoint source right endpoint
    have retained :
        sourceEndpoint ∈
          eraseTwoNodeEndpoints left right
            (source.val.wires wire).endpoints := by
      apply List.mem_filter.mpr
      exact ⟨incident, by
        simp [sourceEndpoint, fusionSourceEndpoint, notLeft,
          fusionSourceNode_ne_right source right endpoint.node]⟩
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint, retained, ?_⟩
    unfold reindexEndpoint?
    simp [sourceEndpoint, fusionSourceEndpoint]

private theorem fusionIncident_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    (fusionIncident source left right).Nodup := by
  exact Data.Finite.eraseDups_nodup _

private def fusionIncidentIndex
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    Fin (fusionIncident source left right).length :=
  (Data.Finite.indexOf? (fusionIncident source left right) wire).get
    (Data.Finite.indexOf?_isSome_iff.mpr member)

@[simp] private theorem fusionIncident_get_index
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    (fusionIncident source left right).get
        (fusionIncidentIndex source left right wire member) =
      wire := by
  apply Data.Finite.indexOf?_sound
  exact
    (Option.some_get
      (Data.Finite.indexOf?_isSome_iff.mpr member)).symm

private def fusionIdentityEndpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (index : Fin (fusionIncident source left right).length) :
    CEndpoint (retainedNodes source.val [right]).length :=
  ⟨fusionLeftNode source left right eligible.distinct,
    .identity index.val⟩

private theorem fusionGeneratedEndpoint_mem
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    fusionIdentityEndpoint source left right eligible
        (fusionIncidentIndex source left right wire member) ∈
      ((fusionCandidate source left right eligible).wires
        (fusionTargetWire source wire)).endpoints := by
  simp only [fusionCandidate]
  have sourceWireEq :
      source.val.wiresList.get (fusionTargetWire source wire) = wire := by
    exact fusionSourceWire_target source wire
  rw [sourceWireEq]
  apply List.mem_append.mpr
  apply Or.inr
  obtain ⟨leftIndex, leftEquation⟩ :=
    Data.Finite.indexOf?_complete
      (left_mem_fusionNodes source left right eligible.distinct)
  obtain ⟨wireIndex, wireEquation⟩ :=
    Data.Finite.indexOf?_complete member
  have leftEquationRaw :
      Data.Finite.indexOf? (retainedNodes source.val [right]) left =
        some leftIndex := by
    simpa [fusionNodes] using leftEquation
  have wireEquationRaw :
      Data.Finite.indexOf?
          (source.val.identityIncidentWires left ++
            source.val.identityIncidentWires right).eraseDups wire =
        some wireIndex := by
    simpa [fusionIncident] using wireEquation
  have leftIndexEq :
      fusionLeftNode source left right eligible.distinct = leftIndex := by
    unfold fusionLeftNode
    apply Fin.ext
    rw [Option.get_of_eq_some _ leftEquation]
  have wireIndexEq :
      fusionIncidentIndex source left right wire member = wireIndex := by
    unfold fusionIncidentIndex
    apply Fin.ext
    rw [Option.get_of_eq_some _ wireEquation]
  rw [leftEquationRaw, wireEquationRaw]
  simp [fusionIdentityEndpoint, leftIndexEq, wireIndexEq]


@[simp] private theorem fusionCandidate_node
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (target : (fusionCandidate source left right eligible).NodeId) :
    (fusionCandidate source left right eligible).nodes target =
      if fusionSourceNode source right target = left then
        .identity eligible.leftIdentity.region
          eligible.leftIdentity.signature
          (fusionIncident source left right).length
      else
        source.val.nodes (fusionSourceNode source right target) := by
  rfl

@[simp] private theorem fusionCandidate_wire_signature
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId) :
    ((fusionCandidate source left right eligible).wires wire).sig =
      (source.val.wires (fusionSourceWire source wire)).sig := by
  rfl

@[simp] private theorem fusionCandidate_wire_scope
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId) :
    ((fusionCandidate source left right eligible).wires wire).scope =
      (source.val.wires (fusionSourceWire source wire)).scope := by
  rfl

private theorem fusionCandidate_requiredPorts
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (target : (fusionCandidate source left right eligible).NodeId) :
    (fusionCandidate source left right eligible).requiredPorts target =
      if fusionSourceNode source right target = left then
        (List.range (fusionIncident source left right).length).map
          CPort.identity
      else
        source.val.requiredPorts (fusionSourceNode source right target) := by
  unfold ConcreteDiagram.requiredPorts
  by_cases atLeft : fusionSourceNode source right target = left
  · simp [fusionCandidate_node, atLeft]
  · simp [fusionCandidate_node, atLeft]
    generalize nodeEquation :
      source.val.nodes (fusionSourceNode source right target) = node
    cases node <;> rfl

private theorem fusionRetainedEndpoint_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint (fusionNodes source right).length)
    (member :
      endpoint ∈
        reindexEndpoints (fusionNodes source right)
          (eraseTwoNodeEndpoints left right
            (source.val.wires wire).endpoints)) :
    fusionSourceEndpoint source right endpoint ∈
        (source.val.wires wire).endpoints ∧
      fusionSourceNode source right endpoint.node ≠ left := by
  rcases List.mem_filterMap.mp member with
    ⟨sourceEndpoint, retained, mapped⟩
  have sourceMember :
      sourceEndpoint ∈ (source.val.wires wire).endpoints :=
    (List.mem_filter.mp retained).1
  have sourceDifferent :
      sourceEndpoint.node ≠ left ∧ sourceEndpoint.node ≠ right :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  unfold reindexEndpoint? at mapped
  cases found :
      Data.Finite.indexOf? (fusionNodes source right)
        sourceEndpoint.node with
  | none => simp [found] at mapped
  | some targetNode =>
      have endpointEquality :
          (⟨targetNode, sourceEndpoint.port⟩ :
            CEndpoint (fusionNodes source right).length) = endpoint :=
        Option.some.inj (by simpa [found] using mapped)
      have indexed := Data.Finite.indexOf?_sound found
      have nodeEquality : sourceEndpoint.node =
          fusionSourceNode source right endpoint.node := by
        have targetEquality : targetNode = endpoint.node :=
          congrArg CEndpoint.node endpointEquality
        simpa [fusionSourceNode, targetEquality] using indexed.symm
      have portEquality : sourceEndpoint.port = endpoint.port :=
        congrArg CEndpoint.port endpointEquality
      constructor
      · cases sourceEndpoint
        cases endpoint
        simp_all [fusionSourceEndpoint]
      · simpa [← nodeEquality] using sourceDifferent.1

private theorem fusionCandidate_endpoint_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires wire).endpoints) :
    (fusionSourceEndpoint source right endpoint ∈
          (source.val.wires (fusionSourceWire source wire)).endpoints ∧
        fusionSourceNode source right endpoint.node ≠ left) ∨
      ∃ index : Fin (fusionIncident source left right).length,
        endpoint = fusionIdentityEndpoint source left right eligible index ∧
          fusionSourceWire source wire =
            (fusionIncident source left right).get index := by
  simp only [fusionCandidate] at member
  rcases List.mem_append.mp member with retained | generated
  · exact Or.inl
      (fusionRetainedEndpoint_origin source left right
        (fusionSourceWire source wire)
        endpoint retained)
  · apply Or.inr
    have canonicalWire :
        source.val.wiresList.get wire =
          fusionSourceWire source wire := by
      apply Fin.ext
      simp [fusionSourceWire]
    rw [canonicalWire] at generated
    cases leftEquation :
        Data.Finite.indexOf? (retainedNodes source.val [right]) left with
    | none => simp [leftEquation] at generated
    | some targetNode =>
        cases wireEquation :
            Data.Finite.indexOf?
              (source.val.identityIncidentWires left ++
                source.val.identityIncidentWires right).eraseDups
              (fusionSourceWire source wire) with
        | none => simp [leftEquation, wireEquation] at generated
        | some index =>
            have endpointEquality :
                endpoint = (⟨targetNode, .identity index.val⟩ :
                  CEndpoint
                    (fusionCandidate source left right eligible).nodeCount) := by
              simpa [leftEquation, wireEquation] using generated
            have sourceWire :=
              Data.Finite.indexOf?_sound wireEquation
            have targetNodeEq :
                targetNode =
                  fusionLeftNode source left right eligible.distinct := by
              exact
                (Data.Finite.indexOf?_unique_of_nodup
                  (fusionNodes_nodup source right)
                  (by simpa [fusionNodes] using leftEquation)
                  (fusionSourceNode_left source left right
                    eligible.distinct)).symm
            refine ⟨index, ?_, ?_⟩
            rw [endpointEquality, targetNodeEq]
            rfl
            simpa [fusionIncident] using sourceWire.symm

@[simp] private theorem fusionSourceNode_identityEndpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (index : Fin (fusionIncident source left right).length) :
    fusionSourceNode source right
        (fusionIdentityEndpoint source left right eligible index).node =
      left := by
  exact fusionSourceNode_left source left right eligible.distinct

private theorem fusion_eraseDups_length_le
    [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (fusion_eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ tail)
    (Nat.lt_succ_self _)

private theorem fusion_nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α]
    (values : List α)
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons, Nat.succ.injEq] at sameLength
      have filteredLength :
          (tail.filter fun value => !value == head).length =
            tail.length := by
        apply Nat.le_antisymm (List.length_filter_le _ tail)
        exact
          sameLength ▸
            fusion_eraseDups_length_le
              (tail.filter fun value => !value == head)
      have accepted :
          ∀ value ∈ tail, (!value == head) = true :=
        List.length_filter_eq_length_iff.mp filteredLength
      have filtered :
          (tail.filter fun value => !value == head) = tail :=
        List.filter_eq_self.mpr accepted
      rw [filtered] at sameLength
      rw [List.nodup_cons]
      refine ⟨?_, ih sameLength⟩
      intro member
      have acceptedHead := accepted head member
      simp at acceptedHead

private theorem fusion_sourceEndpoints_nodup
    (source : CheckedDiagram definitions) :
    (source.val.wiresList.flatMap fun wire =>
      (source.val.wires wire).endpoints).Nodup := by
  have nodup :=
    fusion_nodup_of_eraseDups_length_eq
      (source.val.endpointOccurrences.map Prod.snd)
      (by
        have noDuplicates :=
          source.property.no_duplicate_endpoints
        unfold NoDuplicateEndpoints at noDuplicates
        simpa using noDuplicates)
  unfold ConcreteDiagram.endpointOccurrences at nodup
  rw [List.map_flatMap] at nodup
  simpa [List.map_map, Function.comp_def] using nodup

private theorem fusion_sourceWireEndpoints_nodup
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    (source.val.wires wire).endpoints.Nodup := by
  have components :=
    (List.pairwise_flatMap.mp
      (fusion_sourceEndpoints_nodup source)).1
  exact components wire (Data.Finite.mem_allFin wire)

private theorem fusion_sourceWire_eq_of_common_endpoint
    (source : CheckedDiagram definitions)
    (leftWire rightWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (leftMember : endpoint ∈ (source.val.wires leftWire).endpoints)
    (rightMember : endpoint ∈ (source.val.wires rightWire).endpoints) :
    leftWire = rightWire := by
  have required :=
    incident_port_required _ source.val source.property leftWire endpoint
      leftMember
  have leftOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required leftWire leftMember
  have rightOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required rightWire rightMember
  rw [leftOwner] at rightOwner
  exact Option.some.inj rightOwner

private theorem fusion_reindexEndpoint_corresponds
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (target : CEndpoint (fusionNodes source right).length)
    (equation :
      reindexEndpoint? (fusionNodes source right) endpoint =
        some target) :
    fusionSourceNode source right target.node = endpoint.node ∧
      target.port = endpoint.port := by
  unfold reindexEndpoint? at equation
  cases indexEquation :
      Data.Finite.indexOf? (fusionNodes source right)
        endpoint.node with
  | none => simp [indexEquation] at equation
  | some index =>
      simp [indexEquation] at equation
      subst target
      constructor
      · simpa [fusionSourceNode] using
          Data.Finite.indexOf?_sound indexEquation
      · rfl

private theorem fusion_reindexEndpoints_nodup
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (nodup : endpoints.Nodup) :
    (reindexEndpoints (fusionNodes source right) endpoints).Nodup := by
  apply nodup.filterMap (reindexEndpoint? (fusionNodes source right))
  intro leftEndpoint rightEndpoint different
    leftTarget leftEquation rightTarget rightEquation targetEquality
  have leftCorresponds :=
    fusion_reindexEndpoint_corresponds source right
      leftEndpoint leftTarget leftEquation
  have rightCorresponds :=
    fusion_reindexEndpoint_corresponds source right
      rightEndpoint rightTarget rightEquation
  apply different
  cases leftEndpoint
  cases rightEndpoint
  cases leftTarget
  cases rightTarget
  simp_all

private theorem fusionWireEndpoints_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId) :
    ((fusionCandidate source left right eligible).wires
      wire).endpoints.Nodup := by
  simp only [fusionCandidate]
  let sourceWire := source.val.wiresList.get wire
  let retained :=
    reindexEndpoints (retainedNodes source.val [right])
      (eraseTwoNodeEndpoints left right
        (source.val.wires sourceWire).endpoints)
  have retainedNodup : retained.Nodup := by
    apply fusion_reindexEndpoints_nodup source right
    exact
      (fusion_sourceWireEndpoints_nodup source sourceWire).filter _
  cases leftEquation :
      Data.Finite.indexOf? (retainedNodes source.val [right]) left with
  | none =>
      simpa [sourceWire, retained, leftEquation] using retainedNodup
  | some targetNode =>
      cases wireEquation :
          Data.Finite.indexOf?
            (source.val.identityIncidentWires left ++
              source.val.identityIncidentWires right).eraseDups
            sourceWire with
      | none =>
          simpa [sourceWire, retained, leftEquation, wireEquation] using
            retainedNodup
      | some port =>
          have targetNodeEq :
              targetNode =
                fusionLeftNode source left right eligible.distinct := by
            exact
              (Data.Finite.indexOf?_unique_of_nodup
                (fusionNodes_nodup source right)
                (by simpa [fusionNodes] using leftEquation)
                (fusionSourceNode_left source left right
                  eligible.distinct)).symm
          have notRetained :
              (⟨targetNode, .identity port.val⟩ :
                CEndpoint (fusionNodes source right).length) ∉ retained := by
            intro member
            have origin :=
              fusionRetainedEndpoint_origin source left right
                sourceWire _ member
            exact origin.2 (by simp [targetNodeEq])
          have combined :
              (retained ++
                [(⟨targetNode, .identity port.val⟩ :
                  CEndpoint (fusionNodes source right).length)]).Nodup := by
            rw [List.nodup_append]
            refine ⟨retainedNodup, by simp, ?_⟩
            intro retainedEndpoint retainedMember
              generatedEndpoint generatedMember
            simp only [List.mem_singleton] at generatedMember
            subst generatedEndpoint
            intro equality
            exact notRetained (equality ▸ retainedMember)
          simpa [sourceWire, retained, leftEquation, wireEquation] using
            combined

private theorem fusionWireEndpoints_disjoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (leftWire rightWire :
      (fusionCandidate source left right eligible).WireId)
    (different : leftWire ≠ rightWire)
    (leftEndpoint rightEndpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (leftMember :
      leftEndpoint ∈
        ((fusionCandidate source left right eligible).wires
          leftWire).endpoints)
    (rightMember :
      rightEndpoint ∈
        ((fusionCandidate source left right eligible).wires
          rightWire).endpoints) :
    leftEndpoint ≠ rightEndpoint := by
  intro endpointEquality
  rcases fusionCandidate_endpoint_origin source left right eligible
      leftWire leftEndpoint leftMember with
    leftRetained | ⟨leftIndex, leftGenerated, leftSourceWire⟩
  · rcases fusionCandidate_endpoint_origin source left right eligible
        rightWire rightEndpoint rightMember with
      rightRetained | ⟨rightIndex, rightGenerated, rightSourceWire⟩
    · have sourceEndpointEquality :
          fusionSourceEndpoint source right leftEndpoint =
            fusionSourceEndpoint source right rightEndpoint := by
        cases leftEndpoint
        cases rightEndpoint
        simp_all [fusionSourceEndpoint]
      have sourceWireEquality :=
        fusion_sourceWire_eq_of_common_endpoint source
          (fusionSourceWire source leftWire)
          (fusionSourceWire source rightWire)
          (fusionSourceEndpoint source right leftEndpoint)
          leftRetained.1
          (by simpa [sourceEndpointEquality] using rightRetained.1)
      exact different
        (fusionSourceWire_injective source sourceWireEquality)
    · exact leftRetained.2 (by
        rw [endpointEquality, rightGenerated]
        exact fusionSourceNode_identityEndpoint
          source left right eligible rightIndex)
  · rcases fusionCandidate_endpoint_origin source left right eligible
        rightWire rightEndpoint rightMember with
      rightRetained | ⟨rightIndex, rightGenerated, rightSourceWire⟩
    · exact rightRetained.2 (by
        rw [← endpointEquality, leftGenerated]
        exact fusionSourceNode_identityEndpoint
          source left right eligible leftIndex)
    · have indexEquality : leftIndex = rightIndex := by
        apply Fin.ext
        have portEquality :
            (fusionIdentityEndpoint source left right eligible
              leftIndex).port =
              (fusionIdentityEndpoint source left right eligible
                rightIndex).port := by
          simpa [leftGenerated, rightGenerated] using
            congrArg CEndpoint.port endpointEquality
        simpa [fusionIdentityEndpoint] using portEquality
      have sourceWireEquality :
          fusionSourceWire source leftWire =
            fusionSourceWire source rightWire := by
        rw [leftSourceWire, rightSourceWire, indexEquality]
      exact different
        (fusionSourceWire_injective source sourceWireEquality)

private theorem fusionEndpoints_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ((fusionCandidate source left right eligible).wiresList.flatMap
      fun wire =>
        ((fusionCandidate source left right eligible).wires
          wire).endpoints).Nodup := by
  change List.Pairwise (· ≠ ·)
    ((fusionCandidate source left right eligible).wiresList.flatMap
      fun wire =>
        ((fusionCandidate source left right eligible).wires
          wire).endpoints)
  rw [List.pairwise_flatMap]
  constructor
  · intro wire _
    exact fusionWireEndpoints_nodup source left right eligible wire
  · apply
      (Data.Finite.allFin_nodup
        (fusionCandidate source left right eligible).wireCount).imp
    intro leftWire rightWire different
      leftEndpoint leftMember rightEndpoint rightMember
    exact
      fusionWireEndpoints_disjoint source left right eligible
        leftWire rightWire different leftEndpoint rightEndpoint
        leftMember rightMember

private theorem fusionEndpointValues_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ((fusionCandidate source left right eligible).endpointOccurrences.map
      Prod.snd).Nodup := by
  unfold ConcreteDiagram.endpointOccurrences
  rw [List.map_flatMap]
  simpa [List.map_map, Function.comp_def] using
    fusionEndpoints_nodup source left right eligible

private theorem fusion_eraseDups_length_eq_of_nodup
    [BEq α] [LawfulBEq α]
    (values : List α)
    (nodup : values.Nodup) :
    values.eraseDups.length = values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at nodup
      rw [List.eraseDups_cons]
      have filtered :
          (tail.filter fun value => !value == head) = tail := by
        rw [List.filter_eq_self]
        intro value member
        have different : value ≠ head := by
          intro equality
          exact nodup.1 (equality ▸ member)
        simp [different]
      rw [filtered]
      simp only [List.length_cons, Nat.succ.injEq]
      exact ih nodup.2

private theorem fusionCandidate_no_duplicate_endpoints
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).NoDuplicateEndpoints := by
  unfold NoDuplicateEndpoints
  simpa using
    fusion_eraseDups_length_eq_of_nodup _
      (fusionEndpointValues_nodup source left right eligible)

private theorem fusionCandidate_occurrence
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints) :
    (wire, endpoint) ∈
      (fusionCandidate source left right eligible).endpointOccurrences := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
  exact
    ⟨wire, Data.Finite.mem_allFin wire,
      List.mem_map.mpr ⟨endpoint, member, rfl⟩⟩

private theorem fusionCandidate_owner_isSome
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints) :
    ((fusionCandidate source left right eligible).endpointOwner?
      endpoint).isSome = true := by
  unfold ConcreteDiagram.endpointOwner?
  simp only [Option.isSome_map]
  rw [List.find?_isSome]
  exact
    ⟨(wire, endpoint),
      fusionCandidate_occurrence source left right eligible
        wire endpoint member,
      beq_self_eq_true _⟩

private theorem fusionRetainedEndpoint_candidate_mem
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (notLeft : fusionSourceNode source right endpoint.node ≠ left)
    (sourceMember :
      fusionSourceEndpoint source right endpoint ∈
        (source.val.wires wire).endpoints) :
    endpoint ∈
      ((fusionCandidate source left right eligible).wires
        (fusionTargetWire source wire)).endpoints := by
  simp only [fusionCandidate]
  have sourceWireEq :
      source.val.wiresList.get (fusionTargetWire source wire) = wire := by
    exact fusionSourceWire_target source wire
  rw [sourceWireEq]
  apply List.mem_append.mpr
  exact Or.inl
    ((fusionRetainedEndpoint_mem_iff source left right
      wire endpoint notLeft).mpr sourceMember)

private theorem fusionCandidate_incident_port_required
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints) :
    endpoint.port ∈
      (fusionCandidate source left right eligible).requiredPorts
        endpoint.node := by
  rcases fusionCandidate_endpoint_origin source left right eligible
      wire endpoint member with
    retained | ⟨index, generated, sourceWire⟩
  · have sourceRequired :=
      incident_port_required _ source.val source.property
        (fusionSourceWire source wire)
        (fusionSourceEndpoint source right endpoint)
        retained.1
    rw [fusionCandidate_requiredPorts]
    simp only [retained.2, if_false]
    exact sourceRequired
  · subst endpoint
    rw [fusionCandidate_requiredPorts]
    simp only [fusionSourceNode_identityEndpoint, if_true]
    simp [fusionIdentityEndpoint, index.isLt]

private theorem fusionCandidate_ports_exist
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).PortsExist := by
  unfold PortsExist
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints := by
    simp only [ConcreteDiagram.endpointOccurrences,
      List.mem_flatMap] at occurrence
    rcases occurrence with ⟨candidate, _, mapped⟩
    simp only [List.mem_map] at mapped
    rcases mapped with ⟨candidateEndpoint, candidateMember, equality⟩
    cases equality
    exact candidateMember
  exact decide_eq_true
    (fusionCandidate_incident_port_required source left right eligible
      wire endpoint member)

private theorem fusionCandidate_exact_endpoint_exists
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (target : (fusionCandidate source left right eligible).NodeId)
    (port : CPort)
    (required :
      port ∈
        (fusionCandidate source left right eligible).requiredPorts
          target) :
    ∃ wire,
      (⟨target, port⟩ :
        CEndpoint (fusionCandidate source left right eligible).nodeCount) ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints := by
  by_cases atLeft : fusionSourceNode source right target = left
  · have targetEq :
        target = fusionLeftNode source left right eligible.distinct := by
      apply Fin.ext
      apply
        (List.getElem_inj (fusionNodes_nodup source right)).mp
      change
        fusionSourceNode source right target =
          fusionSourceNode source right
            (fusionLeftNode source left right eligible.distinct)
      exact atLeft.trans
        (fusionSourceNode_left source left right
          eligible.distinct).symm
    rw [fusionCandidate_requiredPorts] at required
    simp only [atLeft, if_true] at required
    rcases List.mem_map.mp required with
      ⟨indexValue, indexMember, portEq⟩
    have indexBound : indexValue <
        (fusionIncident source left right).length := by
      simpa using indexMember
    let index : Fin (fusionIncident source left right).length :=
      ⟨indexValue, indexBound⟩
    let sourceWire := (fusionIncident source left right).get index
    have sourceWireMember :
        sourceWire ∈ fusionIncident source left right :=
      List.get_mem _ index
    refine ⟨fusionTargetWire source sourceWire, ?_⟩
    have generated :=
      fusionGeneratedEndpoint_mem source left right eligible
        sourceWire sourceWireMember
    have endpointEq :
        fusionIdentityEndpoint source left right eligible
            (fusionIncidentIndex source left right
              sourceWire sourceWireMember) =
          (⟨target, port⟩ :
            CEndpoint
              (fusionCandidate source left right eligible).nodeCount) := by
      have indexEq :
          fusionIncidentIndex source left right
              sourceWire sourceWireMember =
            index := by
        apply Fin.ext
        exact
          (List.getElem_inj (fusionIncident_nodup source left right)).mp
            (fusionIncident_get_index source left right
              sourceWire sourceWireMember)
      rw [indexEq]
      cases targetEq
      cases portEq
      rfl
    exact endpointEq ▸ generated
  · rw [fusionCandidate_requiredPorts] at required
    simp only [atLeft, if_false] at required
    obtain ⟨sourceWire, sourceOwner⟩ :=
      endpointOwner?_complete _ source.val source.property
        (fusionSourceNode source right target) port required
    have sourceMember :=
      endpointOwner?_incident source.val
        (⟨fusionSourceNode source right target, port⟩ :
          CEndpoint source.val.nodeCount)
        sourceWire sourceOwner
    refine ⟨fusionTargetWire source sourceWire, ?_⟩
    apply fusionRetainedEndpoint_candidate_mem
      source left right eligible sourceWire
      (⟨target, port⟩ :
        CEndpoint (fusionCandidate source left right eligible).nodeCount)
      atLeft
    simpa [fusionSourceEndpoint] using sourceMember

private theorem fusionCandidate_ports_covered_exactly_once
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).PortsCoveredExactlyOnce := by
  unfold PortsCoveredExactlyOnce
  apply List.all_eq_true.mpr
  intro target _
  apply List.all_eq_true.mpr
  intro port required
  obtain ⟨wire, member⟩ :=
    fusionCandidate_exact_endpoint_exists source left right eligible
      target port required
  have occurrence :=
    fusionCandidate_occurrence source left right eligible wire
      (⟨target, port⟩ :
        CEndpoint (fusionCandidate source left right eligible).nodeCount)
      member
  have valueMember :
      (⟨target, port⟩ :
        CEndpoint (fusionCandidate source left right eligible).nodeCount) ∈
        (fusionCandidate source left right eligible).endpointOccurrences.map
          Prod.snd :=
    List.mem_map.mpr ⟨(wire, ⟨target, port⟩), occurrence, rfl⟩
  have endpointCount :
      ((fusionCandidate source left right eligible).endpointOccurrences.filter
        fun occurrence =>
          occurrence.2 ==
            (⟨target, port⟩ :
              CEndpoint
                (fusionCandidate source left right eligible).nodeCount)).length =
        1 := by
    calc
      _ =
          (fusionCandidate source left right eligible).endpointOccurrences.countP
            (fun occurrence => occurrence.2 == ⟨target, port⟩) :=
        (List.countP_eq_length_filter).symm
      _ =
          ((fusionCandidate source left right eligible).endpointOccurrences.map
            Prod.snd).countP
              (fun endpoint => endpoint == ⟨target, port⟩) := by
        symm
        exact List.countP_map
      _ =
          ((fusionCandidate source left right eligible).endpointOccurrences.map
            Prod.snd).count ⟨target, port⟩ := rfl
      _ = 1 := by
        rw [(fusionEndpointValues_nodup source left right eligible).count]
        simp [valueMember]
  rw [Bool.and_eq_true]
  constructor
  · exact beq_iff_eq.mpr endpointCount
  · exact
      fusionCandidate_owner_isSome source left right eligible
        wire ⟨target, port⟩ member

private theorem fusionIncidentWire_signature
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    (source.val.wires wire).sig =
      eligible.leftIdentity.signature := by
  have unionMember :
      wire ∈ source.val.identityIncidentWires left ++
        source.val.identityIncidentWires right := by
    simpa [fusionIncident] using member
  rcases List.mem_append.mp unionMember with leftMember | rightMember
  · exact identityIncidentWire_signature
      (definitions := definitions) (diagram := source.val)
      (wellFormed := source.property)
      eligible.leftIdentity.node_eq wire leftMember
  · obtain ⟨pivot, pivotLeft, pivotRight⟩ := eligible.shared
    have pivotLeftSignature :=
      identityIncidentWire_signature
        (definitions := definitions) (diagram := source.val)
        (wellFormed := source.property)
        eligible.leftIdentity.node_eq pivot pivotLeft
    have pivotRightSignature :=
      identityIncidentWire_signature
        (definitions := definitions) (diagram := source.val)
        (wellFormed := source.property)
        eligible.rightIdentity.node_eq pivot pivotRight
    have signaturesEqual :
        eligible.rightIdentity.signature =
          eligible.leftIdentity.signature :=
      pivotRightSignature.symm.trans pivotLeftSignature
    exact
      (identityIncidentWire_signature
        (definitions := definitions) (diagram := source.val)
        (wellFormed := source.property)
        eligible.rightIdentity.node_eq wire rightMember).trans
        signaturesEqual

private theorem fusionCandidate_port_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (expected : Sig)
    (required :
      endpoint.port ∈
        (fusionCandidate source left right eligible).requiredPorts
          endpoint.node)
    (wireTyped :
      ∀ wire,
        endpoint ∈
            ((fusionCandidate source left right eligible).wires
              wire).endpoints →
          ((fusionCandidate source left right eligible).wires wire).sig =
            expected) :
    (match
      (fusionCandidate source left right eligible).endpointOwner? endpoint with
    | some wire =>
        ((fusionCandidate source left right eligible).wires wire).sig ==
          expected
    | none => false) = true := by
  obtain ⟨witnessWire, witnessMember⟩ :=
    fusionCandidate_exact_endpoint_exists source left right eligible
      endpoint.node endpoint.port required
  cases owner :
      (fusionCandidate source left right eligible).endpointOwner? endpoint with
  | none =>
      have some :=
        fusionCandidate_owner_isSome source left right eligible
          witnessWire endpoint witnessMember
      simp [owner] at some
  | some wire =>
      apply beq_iff_eq.mpr
      exact wireTyped wire
        (endpointOwner?_incident
          (fusionCandidate source left right eligible)
          endpoint wire owner)

private theorem fusionCandidate_old_port_wire_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (expected : Sig)
    (notLeft : fusionSourceNode source right endpoint.node ≠ left)
    (sourceTyped :
      ∀ wire,
        source.val.endpointOwner?
            (fusionSourceEndpoint source right endpoint) =
          some wire →
        (source.val.wires wire).sig = expected)
    (wire : (fusionCandidate source left right eligible).WireId)
    (member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires wire).endpoints) :
    ((fusionCandidate source left right eligible).wires wire).sig =
      expected := by
  rcases fusionCandidate_endpoint_origin source left right eligible
      wire endpoint member with
    retained | ⟨index, generated, sourceWire⟩
  · rw [fusionCandidate_wire_signature]
    have sourceRequired :=
      incident_port_required _ source.val source.property
        (fusionSourceWire source wire)
        (fusionSourceEndpoint source right endpoint)
        retained.1
    exact sourceTyped (fusionSourceWire source wire)
      (endpointOwner?_eq_of_incident _ source.val source.property
        (fusionSourceEndpoint source right endpoint).node
        (fusionSourceEndpoint source right endpoint).port
        sourceRequired (fusionSourceWire source wire) retained.1)
  · exact False.elim (notLeft (by
      rw [generated]
      exact fusionSourceNode_identityEndpoint
        source left right eligible index))

private theorem fusionCandidate_new_identity_wire_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (target : (fusionCandidate source left right eligible).NodeId)
    (atLeft : fusionSourceNode source right target = left)
    (index : Nat)
    (_bound : index < (fusionIncident source left right).length)
    (wire : (fusionCandidate source left right eligible).WireId)
    (member :
      (⟨target, .identity index⟩ :
        CEndpoint (fusionCandidate source left right eligible).nodeCount) ∈
        ((fusionCandidate source left right eligible).wires wire).endpoints) :
    ((fusionCandidate source left right eligible).wires wire).sig =
      eligible.leftIdentity.signature := by
  let endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount :=
    ⟨target, .identity index⟩
  rcases fusionCandidate_endpoint_origin source left right eligible
      wire endpoint (by simpa [endpoint] using member) with
    retained | ⟨incidentIndex, generated, sourceWire⟩
  · exact False.elim (retained.2 (by simpa [endpoint] using atLeft))
  · rw [fusionCandidate_wire_signature, sourceWire]
    exact fusionIncidentWire_signature source left right eligible
      ((fusionIncident source left right).get incidentIndex)
      (List.get_mem _ incidentIndex)

private theorem fusionCandidate_identities_have_arity
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).IdentitiesHaveArity := by
  unfold IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro target _
  by_cases atLeft : fusionSourceNode source right target = left
  · rw [fusionCandidate_node]
    simp [atLeft, fusionIncident, eligible.union_at_least_two]
  · have sourceChecked :=
      (List.all_eq_true.mp source.property.identities_have_arity)
        (fusionSourceNode source right target)
        (Data.Finite.mem_allFin _)
    cases nodeData :
        source.val.nodes (fusionSourceNode source right target) <;>
      simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢ <;>
      exact sourceChecked

private theorem fusionCandidate_atom_ports_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).AtomPortsTyped := by
  unfold AtomPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  by_cases atLeft : fusionSourceNode source right target = left
  · rw [fusionCandidate_node]
    simp [atLeft]
  · have sourceChecked :=
      (List.all_eq_true.mp source.property.atom_ports_typed)
        (fusionSourceNode source right target)
        (Data.Finite.mem_allFin _)
    cases nodeData :
        source.val.nodes (fusionSourceNode source right target) with
    | atom region args =>
        rw [nodeData] at sourceChecked
        rw [Bool.and_eq_true] at sourceChecked
        rw [fusionCandidate_node]
        simp only [atLeft, if_false, nodeData]
        rw [Bool.and_eq_true]
        constructor
        · let endpoint :
              CEndpoint
                (fusionCandidate source left right eligible).nodeCount :=
            ⟨target, .head⟩
          have typed :=
            fusionCandidate_port_typed source left right eligible
              endpoint (.rel args)
              (by
                simp [endpoint, ConcreteDiagram.requiredPorts,
                  fusionCandidate_node, atLeft, nodeData])
              (fusionCandidate_old_port_wire_typed
                source left right eligible endpoint (.rel args)
                (by simpa [endpoint] using atLeft)
                (by
                  intro wire owner
                  have sourceOwner :
                      source.val.endpointOwner?
                          (⟨fusionSourceNode source right target, .head⟩ :
                            CEndpoint source.val.nodeCount) =
                        some wire := by
                    simpa [endpoint, fusionSourceEndpoint] using owner
                  rw [sourceOwner] at sourceChecked
                  exact eq_of_beq sourceChecked.1))
          have endpointEquality :
              endpoint =
                (⟨target, .head⟩ :
                  CEndpoint
                    (fusionCandidate source left right eligible).nodeCount) :=
            rfl
          rw [endpointEquality] at typed
          cases owner :
              (fusionCandidate source left right eligible).endpointOwner?
                (⟨target, .head⟩ :
                  CEndpoint
                    (fusionCandidate source left right eligible).nodeCount) <;>
            simp [owner] at typed ⊢ <;> assumption
        · apply List.all_eq_true.mpr
          intro index member
          have bound : index < args.length := by simpa using member
          rw [List.getElem?_eq_getElem bound]
          let endpoint :
              CEndpoint
                (fusionCandidate source left right eligible).nodeCount :=
            ⟨target, .arg index⟩
          have typed :=
            fusionCandidate_port_typed source left right eligible
              endpoint args[index]
              (by
                simp [endpoint, ConcreteDiagram.requiredPorts,
                  fusionCandidate_node, atLeft, nodeData, bound])
              (fusionCandidate_old_port_wire_typed
                source left right eligible endpoint args[index]
                (by simpa [endpoint] using atLeft)
                (by
                  intro wire owner
                  have sourceOwner :
                      source.val.endpointOwner?
                          (⟨fusionSourceNode source right target,
                            .arg index⟩ :
                            CEndpoint source.val.nodeCount) =
                        some wire := by
                    simpa [endpoint, fusionSourceEndpoint] using owner
                  have indexChecked :=
                    (List.all_eq_true.mp sourceChecked.2) index member
                  rw [sourceOwner,
                    List.getElem?_eq_getElem bound] at indexChecked
                  exact eq_of_beq indexChecked))
          have endpointEquality :
              endpoint =
                (⟨target, .arg index⟩ :
                  CEndpoint
                    (fusionCandidate source left right eligible).nodeCount) :=
            rfl
          rw [endpointEquality] at typed
          cases owner :
              (fusionCandidate source left right eligible).endpointOwner?
                (⟨target, .arg index⟩ :
                  CEndpoint
                    (fusionCandidate source left right eligible).nodeCount) <;>
            simp [owner] at typed ⊢ <;> assumption
    | ref region definition args =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢
    | identity region sig arity =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢

private theorem fusionCandidate_ref_ports_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).RefPortsTyped := by
  unfold RefPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  by_cases atLeft : fusionSourceNode source right target = left
  · rw [fusionCandidate_node]
    simp [atLeft]
  · have sourceChecked :=
      (List.all_eq_true.mp source.property.ref_ports_typed)
        (fusionSourceNode source right target)
        (Data.Finite.mem_allFin _)
    cases nodeData :
        source.val.nodes (fusionSourceNode source right target) with
    | atom region args =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢
    | ref region definition args =>
        rw [nodeData] at sourceChecked
        rw [fusionCandidate_node]
        simp only [atLeft, if_false, nodeData]
        apply List.all_eq_true.mpr
        intro index member
        have bound : index < args.length := by simpa using member
        rw [List.getElem?_eq_getElem bound]
        let endpoint :
            CEndpoint
              (fusionCandidate source left right eligible).nodeCount :=
          ⟨target, .arg index⟩
        have typed :=
          fusionCandidate_port_typed source left right eligible
            endpoint args[index]
            (by
              simp [endpoint, ConcreteDiagram.requiredPorts,
                fusionCandidate_node, atLeft, nodeData, bound])
            (fusionCandidate_old_port_wire_typed
              source left right eligible endpoint args[index]
              (by simpa [endpoint] using atLeft)
              (by
                intro wire owner
                have sourceOwner :
                    source.val.endpointOwner?
                        (⟨fusionSourceNode source right target,
                          .arg index⟩ :
                          CEndpoint source.val.nodeCount) =
                      some wire := by
                  simpa [endpoint, fusionSourceEndpoint] using owner
                have indexChecked :=
                  (List.all_eq_true.mp sourceChecked) index member
                rw [sourceOwner,
                  List.getElem?_eq_getElem bound] at indexChecked
                exact eq_of_beq indexChecked))
        have endpointEquality :
            endpoint =
              (⟨target, .arg index⟩ :
                CEndpoint
                  (fusionCandidate source left right eligible).nodeCount) :=
          rfl
        rw [endpointEquality] at typed
        cases owner :
            (fusionCandidate source left right eligible).endpointOwner?
              (⟨target, .arg index⟩ :
                CEndpoint
                  (fusionCandidate source left right eligible).nodeCount) <;>
          simp [owner] at typed ⊢ <;> assumption
    | identity region sig arity =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢

private theorem fusionCandidate_identity_ports_typed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).IdentityPortsTyped := by
  unfold IdentityPortsTyped
  apply List.all_eq_true.mpr
  intro target _
  by_cases atLeft : fusionSourceNode source right target = left
  · rw [fusionCandidate_node]
    simp only [atLeft, if_true]
    apply List.all_eq_true.mpr
    intro index member
    have bound :
        index < (fusionIncident source left right).length := by
      simpa using member
    let endpoint :
        CEndpoint (fusionCandidate source left right eligible).nodeCount :=
      ⟨target, .identity index⟩
    have typed :=
      fusionCandidate_port_typed source left right eligible endpoint
        eligible.leftIdentity.signature
        (by
          simp [endpoint, ConcreteDiagram.requiredPorts,
            fusionCandidate_node, atLeft, bound])
        (fusionCandidate_new_identity_wire_typed
          source left right eligible target atLeft index bound)
    have endpointEquality :
        endpoint =
          (⟨target, .identity index⟩ :
            CEndpoint
              (fusionCandidate source left right eligible).nodeCount) := rfl
    rw [endpointEquality] at typed
    cases owner :
        (fusionCandidate source left right eligible).endpointOwner?
          (⟨target, .identity index⟩ :
            CEndpoint
              (fusionCandidate source left right eligible).nodeCount) <;>
      simp [owner] at typed ⊢ <;> assumption
  · have sourceChecked :=
      (List.all_eq_true.mp source.property.identity_ports_typed)
        (fusionSourceNode source right target)
        (Data.Finite.mem_allFin _)
    cases nodeData :
        source.val.nodes (fusionSourceNode source right target) with
    | atom region args =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢
    | ref region definition args =>
        simp [fusionCandidate_node, atLeft, nodeData] at sourceChecked ⊢
    | identity region sig arity =>
        rw [nodeData] at sourceChecked
        rw [fusionCandidate_node]
        simp only [atLeft, if_false, nodeData]
        apply List.all_eq_true.mpr
        intro index member
        have bound : index < arity := by simpa using member
        let endpoint :
            CEndpoint
              (fusionCandidate source left right eligible).nodeCount :=
          ⟨target, .identity index⟩
        have typed :=
          fusionCandidate_port_typed source left right eligible endpoint sig
            (by
              simp [endpoint, ConcreteDiagram.requiredPorts,
                fusionCandidate_node, atLeft, nodeData, bound])
            (fusionCandidate_old_port_wire_typed
              source left right eligible endpoint sig
              (by simpa [endpoint] using atLeft)
              (by
                intro wire owner
                have sourceOwner :
                    source.val.endpointOwner?
                        (⟨fusionSourceNode source right target,
                          .identity index⟩ :
                          CEndpoint source.val.nodeCount) =
                      some wire := by
                  simpa [endpoint, fusionSourceEndpoint] using owner
                have indexChecked :=
                  (List.all_eq_true.mp sourceChecked) index member
                rw [sourceOwner] at indexChecked
                exact eq_of_beq indexChecked))
        have endpointEquality :
            endpoint =
              (⟨target, .identity index⟩ :
                CEndpoint
                  (fusionCandidate source left right eligible).nodeCount) :=
          rfl
        rw [endpointEquality] at typed
        cases owner :
            (fusionCandidate source left right eligible).endpointOwner?
              (⟨target, .identity index⟩ :
                CEndpoint
                  (fusionCandidate source left right eligible).nodeCount) <;>
          simp [owner] at typed ⊢ <;> assumption

@[simp] private theorem fusionCandidate_region
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : (fusionCandidate source left right eligible).RegionId) :
    (fusionCandidate source left right eligible).regions region =
      source.val.regions region := by
  rfl

private theorem fusionCandidate_climb
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ∀ steps region,
      (fusionCandidate source left right eligible).climb steps region =
        source.val.climb steps region := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps induction =>
      intro region
      unfold ConcreteDiagram.climb
      rw [fusionCandidate_region]
      cases source.val.regions region with
      | sheet => rfl
      | cut parent => exact induction parent

private theorem fusionCandidate_encloses_iff
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (ancestor descendant : source.val.RegionId) :
    (fusionCandidate source left right eligible).Encloses
        ancestor descendant ↔
      source.val.Encloses ancestor descendant := by
  unfold ConcreteDiagram.Encloses
  change
    ((Data.Finite.allFin (source.val.regionCount + 1)).any fun steps =>
      (fusionCandidate source left right eligible).climb steps descendant ==
        some ancestor) = true ↔
      ((Data.Finite.allFin (source.val.regionCount + 1)).any fun steps =>
        source.val.climb steps descendant == some ancestor) = true
  constructor <;> intro accepted
  · simpa only [fusionCandidate_climb source left right eligible] using accepted
  · simpa only [fusionCandidate_climb source left right eligible] using accepted

private theorem fusion_source_scope_encloses_identity
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : source.val.nodes node = .identity region sig arity)
    (wire : source.val.WireId)
    (incident : wire ∈ source.val.identityIncidentWires node) :
    source.val.Encloses (source.val.wires wire).scope region := by
  obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
    (mem_identityIncidentWires source.val node wire).mp incident
  have occurrence :
      (wire, endpoint) ∈ source.val.endpointOccurrences := by
    simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
    exact
      ⟨wire, Data.Finite.mem_allFin wire,
        List.mem_map.mpr ⟨endpoint, endpointMember, rfl⟩⟩
  have checked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (wire, endpoint) occurrence
  have encloses :
      source.val.Encloses (source.val.wires wire).scope
        (source.val.nodes endpoint.node).region :=
    of_decide_eq_true checked
  cases endpoint with
  | mk endpointNodeId port =>
      simp only at endpointNode
      subst endpointNodeId
      simpa [nodeData] using encloses

private theorem fusionCandidate_wire_scopes_enclose
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).WireScopesEnclose := by
  unfold WireScopesEnclose
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have member :
      endpoint ∈
        ((fusionCandidate source left right eligible).wires
          wire).endpoints := by
    simp only [ConcreteDiagram.endpointOccurrences,
      List.mem_flatMap] at occurrence
    rcases occurrence with ⟨candidate, _, mapped⟩
    simp only [List.mem_map] at mapped
    rcases mapped with ⟨candidateEndpoint, candidateMember, equality⟩
    cases equality
    exact candidateMember
  rcases fusionCandidate_endpoint_origin source left right eligible
      wire endpoint member with
    retained | ⟨index, generated, sourceWire⟩
  · have sourceOccurrence :
        (fusionSourceWire source wire,
          fusionSourceEndpoint source right endpoint) ∈
          source.val.endpointOccurrences := by
      simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
      exact
        ⟨fusionSourceWire source wire,
          Data.Finite.mem_allFin _,
          List.mem_map.mpr
            ⟨fusionSourceEndpoint source right endpoint,
              retained.1, rfl⟩⟩
    have sourceChecked :=
      (List.all_eq_true.mp source.property.wire_scopes_enclose)
        (fusionSourceWire source wire,
          fusionSourceEndpoint source right endpoint)
        sourceOccurrence
    have sourceEncloses :
        source.val.Encloses
          (source.val.wires (fusionSourceWire source wire)).scope
          (source.val.nodes
            (fusionSourceNode source right endpoint.node)).region := by
      simpa [fusionSourceEndpoint] using of_decide_eq_true sourceChecked
    apply decide_eq_true
    rw [fusionCandidate_wire_scope, fusionCandidate_node]
    simp only [retained.2, if_false]
    exact
      (fusionCandidate_encloses_iff source left right eligible _ _).mpr
        sourceEncloses
  · have incidentMember :
        (fusionIncident source left right).get index ∈
          fusionIncident source left right :=
      List.get_mem _ index
    have unionMember :
        (fusionIncident source left right).get index ∈
          source.val.identityIncidentWires left ++
            source.val.identityIncidentWires right := by
      change
        (fusionIncident source left right).get index ∈
          (source.val.identityIncidentWires left ++
            source.val.identityIncidentWires right).eraseDups
          at incidentMember
      exact List.mem_eraseDups.mp incidentMember
    have sourceEncloses :
        source.val.Encloses
          (source.val.wires
            ((fusionIncident source left right).get index)).scope
          eligible.leftIdentity.region := by
      rcases List.mem_append.mp unionMember with
        leftMember | rightMember
      · exact fusion_source_scope_encloses_identity source left
          eligible.leftIdentity.region
          eligible.leftIdentity.signature eligible.leftIdentity.arity
          eligible.leftIdentity.node_eq _ leftMember
      · have rightEncloses :=
          fusion_source_scope_encloses_identity source right
            eligible.rightIdentity.region
            eligible.rightIdentity.signature eligible.rightIdentity.arity
            eligible.rightIdentity.node_eq _ rightMember
        simpa [eligible.sameRegion] using rightEncloses
    apply decide_eq_true
    rw [generated, fusionCandidate_wire_scope, sourceWire,
      fusionCandidate_node]
    simp only [fusionSourceNode_identityEndpoint, if_true]
    exact
      (fusionCandidate_encloses_iff source left right eligible _ _).mpr
        sourceEncloses

private theorem fusion_root_is_sheet
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).RootIsSheet := by
  change source.val.regions source.val.root = .sheet
  exact source.property.root_is_sheet

private theorem fusion_only_root_is_sheet
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).OnlyRootIsSheet := by
  simpa [OnlyRootIsSheet, fusionCandidate] using
    source.property.only_root_is_sheet

private theorem fusion_all_regions_reach_root
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).AllRegionsReachRoot := by
  unfold AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin _)
  exact decide_eq_true
    ((fusionCandidate_encloses_iff source left right eligible
      source.val.root region).mpr
      (of_decide_eq_true sourceChecked))

private theorem fusion_references_match
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).ReferencesMatch
      definitions := by
  unfold ReferencesMatch
  apply List.all_eq_true.mpr
  intro target _
  by_cases atLeft :
      fusionSourceNode source right target = left
  · rw [fusionCandidate_node]
    simp [atLeft]
  · have sourceChecked :=
      (List.all_eq_true.mp source.property.references_match)
        (fusionSourceNode source right target)
        (Data.Finite.mem_allFin _)
    rw [fusionCandidate_node]
    simp only [atLeft, if_false]
    cases data :
        source.val.nodes (fusionSourceNode source right target) <;>
      simp [data] at sourceChecked ⊢
    exact sourceChecked

theorem fusionCandidate_wellFormed
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).WellFormed definitions where
  root_is_sheet :=
    fusion_root_is_sheet source left right eligible
  only_root_is_sheet :=
    fusion_only_root_is_sheet source left right eligible
  all_regions_reach_root :=
    fusion_all_regions_reach_root source left right eligible
  references_match :=
    fusion_references_match source left right eligible
  ports_exist :=
    fusionCandidate_ports_exist source left right eligible
  no_duplicate_endpoints :=
    fusionCandidate_no_duplicate_endpoints source left right eligible
  ports_covered_exactly_once :=
    fusionCandidate_ports_covered_exactly_once
      source left right eligible
  atom_ports_typed :=
    fusionCandidate_atom_ports_typed source left right eligible
  ref_ports_typed :=
    fusionCandidate_ref_ports_typed source left right eligible
  identities_have_arity :=
    fusionCandidate_identities_have_arity source left right eligible
  identity_ports_typed :=
    fusionCandidate_identity_ports_typed source left right eligible
  wire_scopes_enclose :=
    fusionCandidate_wire_scopes_enclose source left right eligible

end IdentityNormalizationCore

end ConcreteDiagram

end VisualProof
