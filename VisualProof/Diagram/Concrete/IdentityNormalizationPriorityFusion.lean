import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityCollapse

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

private theorem endpoint_eq
    {nodeCount : Nat}
    (left right : CEndpoint nodeCount)
    (node : left.node = right.node)
    (port : left.port = right.port) : left = right := by
  cases left
  cases right
  simp_all

private abbrev fusionNodes
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) : List source.val.NodeId :=
  retainedNodes source.val [right]

private abbrev fusionIncident
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) : List source.val.WireId :=
  (source.val.identityIncidentWires left ++
    source.val.identityIncidentWires right).eraseDups

private def fusionSourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) : source.val.NodeId :=
  (fusionNodes source right).get node

private def fusionSourceEndpoint
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (endpoint : CEndpoint (fusionNodes source right).length) :
    CEndpoint source.val.nodeCount :=
  ⟨fusionSourceNode source right endpoint.node, endpoint.port⟩

private def fusionSourceWire
    (source : CheckedDiagram definitions)
    (wire : Fin source.val.wiresList.length) : source.val.WireId :=
  source.val.wiresList.get wire

private def fusionTargetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) : Fin source.val.wiresList.length :=
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
  intro leftWire rightWire equality
  apply Fin.ext
  exact (List.getElem_inj
    (Data.Finite.allFin_nodup source.val.wireCount)).mp
    (by simpa [fusionSourceWire] using equality)

private theorem fusionNodes_nodup
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) :
    (fusionNodes source right).Nodup :=
  (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem wiresList_nodup
    (source : CheckedDiagram definitions) : source.val.wiresList.Nodup :=
  Data.Finite.allFin_nodup source.val.wireCount

private theorem fusionNodes_mem_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed node : left.val.NodeId) :
    iso.nodes node ∈ fusionNodes right (iso.nodes removed) ↔
      node ∈ fusionNodes left removed := by
  simp [fusionNodes, retainedNodes, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange, iso.nodes.injective.eq_iff]

private theorem wiresList_mem_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (wire : left.val.WireId) :
    iso.wires wire ∈ right.val.wiresList ↔ wire ∈ left.val.wiresList := by
  simp [ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange]

private def fusionRegionEquiv
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    Data.Finite.FiniteEquiv
      (fusionCandidate leftDiagram left right eligible).RegionId
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).RegionId := by
  change Data.Finite.FiniteEquiv
    leftDiagram.val.RegionId rightDiagram.val.RegionId
  exact iso.regions

private def fusionNodeEquiv
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    Data.Finite.FiniteEquiv
      (fusionCandidate leftDiagram left right eligible).NodeId
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).NodeId :=
  Data.Finite.FiniteEquiv.restrictLists iso.nodes
    (fusionNodes leftDiagram right)
    (fusionNodes rightDiagram (iso.nodes right))
    (fusionNodes_nodup leftDiagram right)
    (fusionNodes_nodup rightDiagram (iso.nodes right))
    (fusionNodes_mem_iff iso right)

private def fusionWireEquiv
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    Data.Finite.FiniteEquiv
      (fusionCandidate leftDiagram left right eligible).WireId
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).WireId :=
  Data.Finite.FiniteEquiv.restrictLists iso.wires
    leftDiagram.val.wiresList rightDiagram.val.wiresList
    (wiresList_nodup leftDiagram) (wiresList_nodup rightDiagram)
    (wiresList_mem_iff iso)

private theorem fusionSourceNode_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (node : (fusionCandidate leftDiagram left right eligible).NodeId) :
    fusionSourceNode rightDiagram (iso.nodes right)
        (fusionNodeEquiv iso left right eligible node) =
      iso.nodes (fusionSourceNode leftDiagram right node) :=
  Data.Finite.FiniteEquiv.restrictLists_spec iso.nodes
    (fusionNodes leftDiagram right)
    (fusionNodes rightDiagram (iso.nodes right))
    (fusionNodes_nodup leftDiagram right)
    (fusionNodes_nodup rightDiagram (iso.nodes right))
    (fusionNodes_mem_iff iso right) node

private theorem fusionSourceWire_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId) :
    fusionSourceWire rightDiagram
        (fusionWireEquiv iso left right eligible wire) =
      iso.wires (fusionSourceWire leftDiagram wire) :=
  Data.Finite.FiniteEquiv.restrictLists_spec iso.wires
    leftDiagram.val.wiresList rightDiagram.val.wiresList
    (wiresList_nodup leftDiagram) (wiresList_nodup rightDiagram)
    (wiresList_mem_iff iso) wire

private theorem fusionSourceNode_ne_right
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) :
    fusionSourceNode source right node ≠ right := by
  have member := List.get_mem (fusionNodes source right) node
  have accepted := (List.mem_filter.mp member).2
  simpa [fusionSourceNode, fusionNodes, retainedNodes] using
    of_decide_eq_true accepted

private theorem indexOf_fusionSourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) :
    Data.Finite.indexOf? (fusionNodes source right)
        (fusionSourceNode source right node) = some node :=
  Data.Finite.indexOf?_get_eq_some_of_nodup
    (fusionNodes_nodup source right) node

private theorem left_mem_fusionNodes
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) : left ∈ fusionNodes source right := by
  apply List.mem_filter.mpr
  exact ⟨Data.Finite.mem_allFin left, by simp [distinct]⟩

private def fusionLeftNode
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) : Fin (fusionNodes source right).length :=
  (Data.Finite.indexOf? (fusionNodes source right) left).get
    (Data.Finite.indexOf?_isSome_iff.mpr
      (left_mem_fusionNodes source left right distinct))

@[simp] private theorem fusionSourceNode_left
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) :
    fusionSourceNode source right
        (fusionLeftNode source left right distinct) = left := by
  unfold fusionSourceNode fusionLeftNode
  exact Data.Finite.indexOf?_sound
    (Option.some_get (Data.Finite.indexOf?_isSome_iff.mpr
      (left_mem_fusionNodes source left right distinct))).symm

private theorem fusionSourceNode_injective
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) :
    Function.Injective (fusionSourceNode source right) := by
  intro leftNode rightNode equality
  apply Fin.ext
  exact (List.getElem_inj (fusionNodes_nodup source right)).mp
    (by simpa [fusionSourceNode] using equality)

private theorem fusionLeftNode_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    fusionNodeEquiv iso left right eligible
        (fusionLeftNode leftDiagram left right eligible.distinct) =
      fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible).distinct := by
  apply (fun equality =>
    (fusionSourceNode_injective rightDiagram (iso.nodes right)) equality)
  rw [fusionSourceNode_map, fusionSourceNode_left, fusionSourceNode_left]

private theorem fusionRawReindexed_mem_iff
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (endpoint : CEndpoint (fusionNodes source right).length) :
    endpoint ∈ reindexEndpoints (fusionNodes source right) endpoints ↔
      fusionSourceEndpoint source right endpoint ∈ endpoints := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, candidateMember, mapped⟩
    unfold reindexEndpoint? at mapped
    cases found : Data.Finite.indexOf? (fusionNodes source right)
        candidate.node with
    | none => simp [found] at mapped
    | some targetNode =>
        have mappedEndpoint :
            (⟨targetNode, candidate.port⟩ :
              CEndpoint (fusionNodes source right).length) = endpoint :=
          Option.some.inj (by simpa [found] using mapped)
        have sourceNode : candidate.node =
            fusionSourceNode source right endpoint.node := by
          have indexed := Data.Finite.indexOf?_sound found
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
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint, incident, ?_⟩
    unfold reindexEndpoint?
    simp [sourceEndpoint, fusionSourceEndpoint,
      indexOf_fusionSourceNode]

private theorem fusionReindexed_mem_iff
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (endpoint : CEndpoint (fusionNodes source right).length) :
    endpoint ∈ reindexEndpoints (fusionNodes source right)
        (eraseTwoNodeEndpoints left right endpoints) ↔
      fusionSourceEndpoint source right endpoint ∈ endpoints ∧
        fusionSourceNode source right endpoint.node ≠ left := by
  rw [fusionRawReindexed_mem_iff]
  simp [eraseTwoNodeEndpoints, fusionSourceEndpoint,
    fusionSourceNode_ne_right source right endpoint.node]

private theorem fusionIncident_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    (fusionIncident source left right).Nodup :=
  Data.Finite.eraseDups_nodup _

private theorem fusionIncident_mem_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (wire : leftDiagram.val.WireId) :
    iso.wires wire ∈ fusionIncident rightDiagram
        (iso.nodes left) (iso.nodes right) ↔
      wire ∈ fusionIncident leftDiagram left right := by
  simp only [fusionIncident, List.mem_eraseDups, List.mem_append,
    mem_identityIncidentWires_map iso left wire,
    mem_identityIncidentWires_map iso right wire]

private theorem fusionIncident_length_eq
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId) :
    (fusionIncident rightDiagram (iso.nodes left) (iso.nodes right)).length =
      (fusionIncident leftDiagram left right).length := by
  apply Nat.le_antisymm
  · let restricted := Data.Finite.FiniteEquiv.restrictLists iso.wires.symm
      (fusionIncident rightDiagram (iso.nodes left) (iso.nodes right))
      (fusionIncident leftDiagram left right)
      (fusionIncident_nodup rightDiagram (iso.nodes left) (iso.nodes right))
      (fusionIncident_nodup leftDiagram left right)
      (fun wire => by
        simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
          (fusionIncident_mem_map iso left right (iso.wires.symm wire)).symm)
    exact Data.Finite.fin_card_le_of_injective restricted restricted.injective
  · let restricted := Data.Finite.FiniteEquiv.restrictLists iso.wires
      (fusionIncident leftDiagram left right)
      (fusionIncident rightDiagram (iso.nodes left) (iso.nodes right))
      (fusionIncident_nodup leftDiagram left right)
      (fusionIncident_nodup rightDiagram (iso.nodes left) (iso.nodes right))
      (fusionIncident_mem_map iso left right)
    exact Data.Finite.fin_card_le_of_injective restricted restricted.injective

@[simp] private theorem fusionCandidate_node_source
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

@[simp] private theorem fusionCandidate_wire_signature_source
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId) :
    ((fusionCandidate source left right eligible).wires wire).sig =
      (source.val.wires (fusionSourceWire source wire)).sig := by
  rfl

@[simp] private theorem fusionCandidate_wire_scope_source
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId) :
    ((fusionCandidate source left right eligible).wires wire).scope =
      (source.val.wires (fusionSourceWire source wire)).scope := by
  rfl

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
        (fusionIncidentIndex source left right wire member) = wire := by
  apply Data.Finite.indexOf?_sound
  exact (Option.some_get
    (Data.Finite.indexOf?_isSome_iff.mpr member)).symm

private theorem indexOf_fusionLeftNode
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (distinct : left ≠ right) :
    Data.Finite.indexOf? (fusionNodes source right) left =
      some (fusionLeftNode source left right distinct) := by
  have indexed := Data.Finite.indexOf?_get_eq_some_of_nodup
    (fusionNodes_nodup source right)
    (fusionLeftNode source left right distinct)
  have nodeExact := fusionSourceNode_left source left right distinct
  exact (congrArg (Data.Finite.indexOf? (fusionNodes source right))
    nodeExact).symm.trans indexed

private theorem indexOf_fusionIncidentIndex
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    Data.Finite.indexOf? (fusionIncident source left right) wire =
      some (fusionIncidentIndex source left right wire member) := by
  simpa only [fusionIncident_get_index source left right wire member] using
    Data.Finite.indexOf?_get_eq_some_of_nodup
      (fusionIncident_nodup source left right)
      (fusionIncidentIndex source left right wire member)

private def fusionIdentityEndpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    CEndpoint (fusionNodes source right).length :=
  ⟨fusionLeftNode source left right eligible.distinct,
    .identity (fusionIncidentIndex source left right wire member).val⟩

private theorem fusionIdentityEndpoint_mem
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId)
    (member : wire ∈ fusionIncident source left right) :
    fusionIdentityEndpoint source left right eligible wire member ∈
      ((fusionCandidate source left right eligible).wires
        (fusionTargetWire source wire)).endpoints := by
  simp only [fusionCandidate]
  have sourceWireExact := fusionSourceWire_target source wire
  simp only [fusionSourceWire] at sourceWireExact
  rw [sourceWireExact]
  apply List.mem_append.mpr
  apply Or.inr
  rw [indexOf_fusionLeftNode source left right eligible.distinct]
  rw [indexOf_fusionIncidentIndex source left right wire member]
  simp [fusionIdentityEndpoint]

private theorem fusionIdentityEndpoint_mem_candidate
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (member : fusionSourceWire source wire ∈
      fusionIncident source left right) :
    fusionIdentityEndpoint source left right eligible
        (fusionSourceWire source wire) member ∈
      ((fusionCandidate source left right eligible).wires wire).endpoints := by
  simp only [fusionCandidate]
  apply List.mem_append.mpr
  apply Or.inr
  rw [indexOf_fusionLeftNode source left right eligible.distinct]
  have incidentIndex := indexOf_fusionIncidentIndex source left right
    (fusionSourceWire source wire) member
  simp only [fusionSourceWire] at incidentIndex
  rw [incidentIndex]
  simp [fusionIdentityEndpoint, fusionSourceWire]

private theorem fusionGenerated_mem_iff
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint : CEndpoint (fusionNodes source right).length) :
    endpoint ∈
        (match Data.Finite.indexOf? (fusionNodes source right) left,
            Data.Finite.indexOf? (fusionIncident source left right)
              (fusionSourceWire source wire) with
          | some targetNode, some port =>
              [(⟨targetNode, .identity port.val⟩ :
                CEndpoint (fusionNodes source right).length)]
          | _, _ => []) ↔
      ∃ member : fusionSourceWire source wire ∈
          fusionIncident source left right,
        endpoint = fusionIdentityEndpoint source left right eligible
          (fusionSourceWire source wire) member := by
  constructor
  · intro generated
    have leftIndex := indexOf_fusionLeftNode source left right
      eligible.distinct
    rw [leftIndex] at generated
    cases incident : Data.Finite.indexOf? (fusionIncident source left right)
        (fusionSourceWire source wire) with
    | none => simp [incident] at generated
    | some port =>
        have sourceExact := Data.Finite.indexOf?_sound incident
        have member : fusionSourceWire source wire ∈
            fusionIncident source left right := by
          rw [← sourceExact]
          exact List.get_mem _ port
        refine ⟨member, ?_⟩
        have canonical := indexOf_fusionIncidentIndex source left right
          (fusionSourceWire source wire) member
        rw [incident] at canonical
        have indexExact := Option.some.inj canonical.symm
        simp only [incident, List.mem_singleton] at generated
        simpa [fusionIdentityEndpoint, indexExact] using generated
  · rintro ⟨member, exact⟩
    subst endpoint
    rw [indexOf_fusionLeftNode source left right eligible.distinct]
    rw [indexOf_fusionIncidentIndex source left right
      (fusionSourceWire source wire) member]
    simp [fusionIdentityEndpoint]

private def fusionIdentityEndpointAt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (index : Fin (fusionIncident source left right).length) :
    CEndpoint (fusionNodes source right).length :=
  ⟨fusionLeftNode source left right eligible.distinct,
    .identity index.val⟩

private theorem fusionRetainedEndpoint_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint (fusionNodes source right).length)
    (member : endpoint ∈
      reindexEndpoints (fusionNodes source right)
        (eraseTwoNodeEndpoints left right
          (source.val.wires wire).endpoints)) :
    fusionSourceEndpoint source right endpoint ∈
        (source.val.wires wire).endpoints ∧
      fusionSourceNode source right endpoint.node ≠ left :=
  (fusionReindexed_mem_iff source left right _ endpoint).mp member

private theorem fusionCandidate_endpoint_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint :
      CEndpoint (fusionCandidate source left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate source left right eligible).wires wire).endpoints) :
    (fusionSourceEndpoint source right endpoint ∈
          (source.val.wires (fusionSourceWire source wire)).endpoints ∧
        fusionSourceNode source right endpoint.node ≠ left) ∨
      ∃ index : Fin (fusionIncident source left right).length,
        endpoint = fusionIdentityEndpointAt source left right eligible index ∧
          fusionSourceWire source wire =
            (fusionIncident source left right).get index := by
  simp only [fusionCandidate] at member
  rcases List.mem_append.mp member with retained | generated
  · exact Or.inl
      (fusionRetainedEndpoint_origin source left right
        (fusionSourceWire source wire) endpoint retained)
  · apply Or.inr
    have canonicalWire : source.val.wiresList.get wire =
        fusionSourceWire source wire := by
      apply Fin.ext
      simp [fusionSourceWire]
    rw [canonicalWire] at generated
    cases leftEquation :
        Data.Finite.indexOf? (retainedNodes source.val [right]) left with
    | none => simp [leftEquation] at generated
    | some targetNode =>
        cases wireEquation : Data.Finite.indexOf?
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
            have sourceWire := Data.Finite.indexOf?_sound wireEquation
            have targetNodeEq : targetNode =
                fusionLeftNode source left right eligible.distinct := by
              exact (Data.Finite.indexOf?_unique_of_nodup
                (fusionNodes_nodup source right)
                (by simpa [fusionNodes] using leftEquation)
                (fusionSourceNode_left source left right
                  eligible.distinct)).symm
            refine ⟨index, ?_, ?_⟩
            · rw [endpointEquality, targetNodeEq]
              rfl
            · simpa [fusionIncident] using sourceWire.symm

@[simp] private theorem fusionSourceNode_identityEndpointAt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (index : Fin (fusionIncident source left right).length) :
    fusionSourceNode source right
        (fusionIdentityEndpointAt source left right eligible index).node =
      left :=
  fusionSourceNode_left source left right eligible.distinct

private theorem fusionIncident_of_left_endpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate source left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate source left right eligible).wires wire).endpoints)
    (atLeft : endpoint.node =
      fusionLeftNode source left right eligible.distinct) :
    fusionSourceWire source wire ∈ fusionIncident source left right := by
  rcases fusionCandidate_endpoint_origin source left right eligible wire
      endpoint member with retained | ⟨index, generated, sourceWire⟩
  · exact False.elim (retained.2 (by
      rw [atLeft, fusionSourceNode_left]))
  · rw [sourceWire]
    exact List.get_mem _ index

private theorem fusionRetained_of_not_left
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate source left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate source left right eligible).wires wire).endpoints)
    (notLeft : endpoint.node ≠
      fusionLeftNode source left right eligible.distinct) :
    fusionSourceEndpoint source right endpoint ∈
        (source.val.wires (fusionSourceWire source wire)).endpoints ∧
      fusionSourceNode source right endpoint.node ≠ left := by
  rcases fusionCandidate_endpoint_origin source left right eligible wire
      endpoint member with retained | ⟨index, generated, sourceWire⟩
  · exact retained
  · exact False.elim (notLeft (by
      rw [generated]
      rfl))

private noncomputable def fusionMapEndpoint
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate leftDiagram left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints) :
    CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount :=
  if atLeft : endpoint.node =
      fusionLeftNode leftDiagram left right eligible.distinct then
    let sourceIncident := fusionIncident_of_left_endpoint leftDiagram
      left right eligible wire endpoint member atLeft
    let targetIncident : fusionSourceWire rightDiagram
          (fusionWireEquiv iso left right eligible wire) ∈
        fusionIncident rightDiagram (iso.nodes left) (iso.nodes right) := by
      rw [fusionSourceWire_map iso left right eligible wire]
      exact (fusionIncident_mem_map iso left right
        (fusionSourceWire leftDiagram wire)).mpr sourceIncident
    fusionIdentityEndpoint rightDiagram (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)
      (fusionSourceWire rightDiagram
        (fusionWireEquiv iso left right eligible wire)) targetIncident
  else
    let sourceWire := fusionSourceWire leftDiagram wire
    let mapped := iso.endpointMap sourceWire
      (fusionSourceEndpoint leftDiagram right endpoint)
    ⟨fusionNodeEquiv iso left right eligible endpoint.node, mapped.port⟩

private theorem fusionMapEndpoint_mem
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate leftDiagram left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints) :
    fusionMapEndpoint iso left right eligible wire endpoint member ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints := by
  by_cases atLeft : endpoint.node =
      fusionLeftNode leftDiagram left right eligible.distinct
  · rw [fusionMapEndpoint, dif_pos atLeft]
    exact fusionIdentityEndpoint_mem_candidate rightDiagram
      (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)
      (fusionWireEquiv iso left right eligible wire) _
  · rw [fusionMapEndpoint, dif_neg atLeft]
    have retained := fusionRetained_of_not_left leftDiagram left right
      eligible wire endpoint member atLeft
    let sourceWire := fusionSourceWire leftDiagram wire
    let sourceEndpoint := fusionSourceEndpoint leftDiagram right endpoint
    let mapped := iso.endpointMap sourceWire sourceEndpoint
    let targetEndpoint : CEndpoint
        (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
          (transportFusionEligibility iso eligible)).nodeCount :=
      ⟨fusionNodeEquiv iso left right eligible endpoint.node, mapped.port⟩
    have mappedMember : mapped ∈
        (rightDiagram.val.wires (iso.wires sourceWire)).endpoints :=
      iso.endpointMap_mem sourceWire sourceEndpoint retained.1
    have sourceExact :
        fusionSourceEndpoint rightDiagram (iso.nodes right) targetEndpoint =
          mapped := by
      apply endpoint_eq
      · change fusionSourceNode rightDiagram (iso.nodes right)
            (fusionNodeEquiv iso left right eligible endpoint.node) = mapped.node
        rw [fusionSourceNode_map iso left right eligible endpoint.node]
        exact (iso.endpointMap_corresponds sourceWire sourceEndpoint
          retained.1).1.symm
      · rfl
    have targetRetained : targetEndpoint ∈
        reindexEndpoints (fusionNodes rightDiagram (iso.nodes right))
          (eraseTwoNodeEndpoints (iso.nodes left) (iso.nodes right)
            (rightDiagram.val.wires (fusionSourceWire rightDiagram
              (fusionWireEquiv iso left right eligible wire))).endpoints) := by
      apply (fusionReindexed_mem_iff rightDiagram (iso.nodes left)
        (iso.nodes right) _ targetEndpoint).mpr
      constructor
      · rw [sourceExact, fusionSourceWire_map iso left right eligible wire]
        exact mappedMember
      · intro same
        have mappedLeft : mapped.node = iso.nodes left :=
          (congrArg CEndpoint.node sourceExact).symm.trans same
        have corresponds := iso.endpointMap_corresponds sourceWire
          sourceEndpoint retained.1
        exact retained.2 (iso.nodes.injective
          (corresponds.1.symm.trans mappedLeft))
    change targetEndpoint ∈ _
    simp only [fusionCandidate]
    exact List.mem_append.mpr (Or.inl targetRetained)

private noncomputable def fusionInverseEndpoint
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints) :
    CEndpoint (fusionCandidate leftDiagram left right eligible).nodeCount :=
  if atLeft : endpoint.node =
      fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible).distinct then
    let targetIncident := fusionIncident_of_left_endpoint rightDiagram
      (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)
      (fusionWireEquiv iso left right eligible wire) endpoint member atLeft
    let sourceIncident : fusionSourceWire leftDiagram wire ∈
        fusionIncident leftDiagram left right := by
      apply (fusionIncident_mem_map iso left right
        (fusionSourceWire leftDiagram wire)).mp
      rw [← fusionSourceWire_map iso left right eligible wire]
      exact targetIncident
    fusionIdentityEndpoint leftDiagram left right eligible
      (fusionSourceWire leftDiagram wire) sourceIncident
  else
    let sourceWire := fusionSourceWire leftDiagram wire
    let mapped := iso.endpointInverse sourceWire
      (fusionSourceEndpoint rightDiagram (iso.nodes right) endpoint)
    ⟨(fusionNodeEquiv iso left right eligible).symm endpoint.node,
      mapped.port⟩

private theorem fusionInverseEndpoint_mem
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints) :
    fusionInverseEndpoint iso left right eligible wire endpoint member ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints := by
  by_cases atLeft : endpoint.node =
      fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible).distinct
  · rw [fusionInverseEndpoint, dif_pos atLeft]
    exact fusionIdentityEndpoint_mem_candidate leftDiagram left right eligible
      wire _
  · rw [fusionInverseEndpoint, dif_neg atLeft]
    have retained := fusionRetained_of_not_left rightDiagram
      (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)
      (fusionWireEquiv iso left right eligible wire) endpoint member atLeft
    let sourceWire := fusionSourceWire leftDiagram wire
    let targetEndpoint :=
      fusionSourceEndpoint rightDiagram (iso.nodes right) endpoint
    have targetMember : targetEndpoint ∈
        (rightDiagram.val.wires (iso.wires sourceWire)).endpoints := by
      rw [← fusionSourceWire_map iso left right eligible wire]
      exact retained.1
    let mapped := iso.endpointInverse sourceWire targetEndpoint
    let sourceEndpoint : CEndpoint
        (fusionCandidate leftDiagram left right eligible).nodeCount :=
      ⟨(fusionNodeEquiv iso left right eligible).symm endpoint.node,
        mapped.port⟩
    have mappedMember : mapped ∈
        (leftDiagram.val.wires sourceWire).endpoints :=
      iso.endpointInverse_mem sourceWire targetEndpoint targetMember
    have sourceExact :
        fusionSourceEndpoint leftDiagram right sourceEndpoint = mapped := by
      have corresponds := iso.endpointMap_corresponds sourceWire mapped
        mappedMember
      rw [iso.endpointMap_right_inv sourceWire targetEndpoint targetMember]
        at corresponds
      apply endpoint_eq
      · have nodeMap := fusionSourceNode_map iso left right eligible
          ((fusionNodeEquiv iso left right eligible).symm endpoint.node)
        rw [Data.Finite.FiniteEquiv.apply_symm_apply] at nodeMap
        change fusionSourceNode leftDiagram right
            ((fusionNodeEquiv iso left right eligible).symm endpoint.node) =
          mapped.node
        exact iso.nodes.injective (nodeMap.symm.trans corresponds.1)
      · rfl
    have sourceRetained : sourceEndpoint ∈
        reindexEndpoints (fusionNodes leftDiagram right)
          (eraseTwoNodeEndpoints left right
            (leftDiagram.val.wires (fusionSourceWire leftDiagram wire)).endpoints) := by
      apply (fusionReindexed_mem_iff leftDiagram left right _ sourceEndpoint).mpr
      constructor
      · rw [sourceExact]
        exact mappedMember
      · intro same
        have mappedLeft : mapped.node = left :=
          (congrArg CEndpoint.node sourceExact).symm.trans same
        have corresponds := iso.endpointMap_corresponds sourceWire mapped
          mappedMember
        rw [iso.endpointMap_right_inv sourceWire targetEndpoint targetMember]
          at corresponds
        exact retained.2
          (corresponds.1.trans (congrArg iso.nodes mappedLeft))
    change sourceEndpoint ∈ _
    simp only [fusionCandidate]
    exact List.mem_append.mpr (Or.inl sourceRetained)

private theorem fusion_left_endpoint_canonical
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : (fusionCandidate source left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate source left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate source left right eligible).wires wire).endpoints)
    (atLeft : endpoint.node =
      fusionLeftNode source left right eligible.distinct) :
    endpoint = fusionIdentityEndpoint source left right eligible
      (fusionSourceWire source wire)
      (fusionIncident_of_left_endpoint source left right eligible wire
        endpoint member atLeft) := by
  rcases fusionCandidate_endpoint_origin source left right eligible wire
      endpoint member with retained | ⟨index, generated, sourceWire⟩
  · exact False.elim (retained.2 (by
      rw [atLeft, fusionSourceNode_left]))
  · have incident := fusionIncident_of_left_endpoint source left right
      eligible wire endpoint member atLeft
    have indexExact : fusionIncidentIndex source left right
        (fusionSourceWire source wire) incident = index := by
      apply Fin.ext
      apply (List.getElem_inj (fusionIncident_nodup source left right)).mp
      exact (fusionIncident_get_index source left right
        (fusionSourceWire source wire) incident).trans sourceWire
    apply endpoint_eq
    · exact atLeft
    · simpa [fusionIdentityEndpointAt, fusionIdentityEndpoint,
        indexExact] using congrArg CEndpoint.port generated

private theorem fusionMapEndpoint_left_iff
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate leftDiagram left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints) :
    (fusionMapEndpoint iso left right eligible wire endpoint member).node =
        fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
          (transportFusionEligibility iso eligible).distinct ↔
      endpoint.node = fusionLeftNode leftDiagram left right eligible.distinct := by
  by_cases atLeft : endpoint.node =
      fusionLeftNode leftDiagram left right eligible.distinct
  · rw [fusionMapEndpoint, dif_pos atLeft]
    constructor
    · intro
      exact atLeft
    · intro
      rfl
  · rw [fusionMapEndpoint, dif_neg atLeft]
    rw [← fusionLeftNode_map iso left right eligible]
    exact ⟨fun same => False.elim (atLeft
      ((fusionNodeEquiv iso left right eligible).injective same)),
      fun same => False.elim (atLeft same)⟩

private theorem fusionInverseEndpoint_left_iff
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints) :
    (fusionInverseEndpoint iso left right eligible wire endpoint member).node =
        fusionLeftNode leftDiagram left right eligible.distinct ↔
      endpoint.node = fusionLeftNode rightDiagram
        (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible).distinct := by
  by_cases atLeft : endpoint.node = fusionLeftNode rightDiagram
      (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible).distinct
  · rw [fusionInverseEndpoint, dif_pos atLeft]
    constructor
    · intro
      exact atLeft
    · intro
      rfl
  · rw [fusionInverseEndpoint, dif_neg atLeft]
    rw [← fusionLeftNode_map iso left right eligible]
    constructor
    · intro same
      have mapped := congrArg (fusionNodeEquiv iso left right eligible) same
      rw [Data.Finite.FiniteEquiv.apply_symm_apply,
        fusionLeftNode_map iso left right eligible] at mapped
      exact False.elim (atLeft mapped)
    · intro same
      exact False.elim (atLeft
        (same.trans (fusionLeftNode_map iso left right eligible)))

private theorem fusionMapEndpoint_source_of_not_left
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate leftDiagram left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints)
    (notLeft : endpoint.node ≠
      fusionLeftNode leftDiagram left right eligible.distinct) :
    fusionSourceEndpoint rightDiagram (iso.nodes right)
        (fusionMapEndpoint iso left right eligible wire endpoint member) =
      iso.endpointMap (fusionSourceWire leftDiagram wire)
        (fusionSourceEndpoint leftDiagram right endpoint) := by
  rw [fusionMapEndpoint, dif_neg notLeft]
  let sourceWire := fusionSourceWire leftDiagram wire
  let sourceEndpoint := fusionSourceEndpoint leftDiagram right endpoint
  have retained := fusionRetained_of_not_left leftDiagram left right eligible
    wire endpoint member notLeft
  apply endpoint_eq
  · change fusionSourceNode rightDiagram (iso.nodes right)
        (fusionNodeEquiv iso left right eligible endpoint.node) =
      (iso.endpointMap sourceWire sourceEndpoint).node
    rw [fusionSourceNode_map iso left right eligible endpoint.node]
    exact (iso.endpointMap_corresponds sourceWire sourceEndpoint
      retained.1).1.symm
  · rfl

private theorem fusionInverseEndpoint_source_of_not_left
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints)
    (notLeft : endpoint.node ≠
      fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible).distinct) :
    fusionSourceEndpoint leftDiagram right
        (fusionInverseEndpoint iso left right eligible wire endpoint member) =
      iso.endpointInverse (fusionSourceWire leftDiagram wire)
        (fusionSourceEndpoint rightDiagram (iso.nodes right) endpoint) := by
  rw [fusionInverseEndpoint, dif_neg notLeft]
  let sourceWire := fusionSourceWire leftDiagram wire
  let targetEndpoint :=
    fusionSourceEndpoint rightDiagram (iso.nodes right) endpoint
  have retained := fusionRetained_of_not_left rightDiagram
    (iso.nodes left) (iso.nodes right)
    (transportFusionEligibility iso eligible)
    (fusionWireEquiv iso left right eligible wire) endpoint member notLeft
  have targetMember : targetEndpoint ∈
      (rightDiagram.val.wires (iso.wires sourceWire)).endpoints := by
    rw [← fusionSourceWire_map iso left right eligible wire]
    exact retained.1
  let mapped := iso.endpointInverse sourceWire targetEndpoint
  have mappedMember := iso.endpointInverse_mem sourceWire targetEndpoint
    targetMember
  have corresponds := iso.endpointMap_corresponds sourceWire mapped
    mappedMember
  rw [iso.endpointMap_right_inv sourceWire targetEndpoint targetMember]
    at corresponds
  apply endpoint_eq
  · have nodeMap := fusionSourceNode_map iso left right eligible
        ((fusionNodeEquiv iso left right eligible).symm endpoint.node)
    rw [Data.Finite.FiniteEquiv.apply_symm_apply] at nodeMap
    change fusionSourceNode leftDiagram right
        ((fusionNodeEquiv iso left right eligible).symm endpoint.node) =
      mapped.node
    exact iso.nodes.injective (nodeMap.symm.trans corresponds.1)
  · rfl

private theorem fusionInverse_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate leftDiagram left right eligible).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate leftDiagram left right eligible).wires wire).endpoints) :
    fusionInverseEndpoint iso left right eligible wire
        (fusionMapEndpoint iso left right eligible wire endpoint member)
        (fusionMapEndpoint_mem iso left right eligible wire endpoint member) =
      endpoint := by
  let mappedEndpoint :=
    fusionMapEndpoint iso left right eligible wire endpoint member
  let mappedMember :=
    fusionMapEndpoint_mem iso left right eligible wire endpoint member
  by_cases atLeft : endpoint.node =
      fusionLeftNode leftDiagram left right eligible.distinct
  · have targetLeft := (fusionMapEndpoint_left_iff iso left right eligible
      wire endpoint member).mpr atLeft
    rw [fusionInverseEndpoint, dif_pos targetLeft]
    exact (fusion_left_endpoint_canonical leftDiagram left right eligible wire
      endpoint member atLeft).symm
  · have targetNotLeft : mappedEndpoint.node ≠
        fusionLeftNode rightDiagram (iso.nodes left) (iso.nodes right)
          (transportFusionEligibility iso eligible).distinct :=
      (not_congr (fusionMapEndpoint_left_iff iso left right eligible wire
        endpoint member)).mpr atLeft
    rw [fusionInverseEndpoint, dif_neg targetNotLeft]
    apply endpoint_eq
    · change (fusionNodeEquiv iso left right eligible).symm mappedEndpoint.node =
        endpoint.node
      have mappedNode : mappedEndpoint.node =
          fusionNodeEquiv iso left right eligible endpoint.node := by
        simp [mappedEndpoint, fusionMapEndpoint, atLeft]
      rw [mappedNode]
      exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
    · have sourceExact := fusionMapEndpoint_source_of_not_left iso left right
          eligible wire endpoint member atLeft
      have retained := fusionRetained_of_not_left leftDiagram left right eligible
        wire endpoint member atLeft
      change (iso.endpointInverse (fusionSourceWire leftDiagram wire)
          (fusionSourceEndpoint rightDiagram (iso.nodes right)
            mappedEndpoint)).port = endpoint.port
      rw [sourceExact]
      rw [iso.endpointMap_left_inv (fusionSourceWire leftDiagram wire)
        (fusionSourceEndpoint leftDiagram right endpoint) retained.1]
      rfl

private theorem fusionMap_inverse
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId)
    (endpoint : CEndpoint
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).wires
          (fusionWireEquiv iso left right eligible wire)).endpoints) :
    fusionMapEndpoint iso left right eligible wire
        (fusionInverseEndpoint iso left right eligible wire endpoint member)
        (fusionInverseEndpoint_mem iso left right eligible wire endpoint member) =
      endpoint := by
  let inverseEndpoint :=
    fusionInverseEndpoint iso left right eligible wire endpoint member
  let inverseMember :=
    fusionInverseEndpoint_mem iso left right eligible wire endpoint member
  by_cases atLeft : endpoint.node = fusionLeftNode rightDiagram
      (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible).distinct
  · have sourceLeft := (fusionInverseEndpoint_left_iff iso left right
      eligible wire endpoint member).mpr atLeft
    rw [fusionMapEndpoint, dif_pos sourceLeft]
    exact (fusion_left_endpoint_canonical rightDiagram (iso.nodes left)
      (iso.nodes right) (transportFusionEligibility iso eligible)
      (fusionWireEquiv iso left right eligible wire) endpoint member atLeft).symm
  · have sourceNotLeft : inverseEndpoint.node ≠
        fusionLeftNode leftDiagram left right eligible.distinct :=
      (not_congr (fusionInverseEndpoint_left_iff iso left right eligible wire
        endpoint member)).mpr atLeft
    rw [fusionMapEndpoint, dif_neg sourceNotLeft]
    apply endpoint_eq
    · change fusionNodeEquiv iso left right eligible inverseEndpoint.node =
        endpoint.node
      have inverseNode : inverseEndpoint.node =
          (fusionNodeEquiv iso left right eligible).symm endpoint.node := by
        simp [inverseEndpoint, fusionInverseEndpoint, atLeft]
      rw [inverseNode]
      exact Data.Finite.FiniteEquiv.apply_symm_apply _ _
    · have sourceExact := fusionInverseEndpoint_source_of_not_left iso
          left right eligible wire endpoint member atLeft
      have retained := fusionRetained_of_not_left rightDiagram
        (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)
        (fusionWireEquiv iso left right eligible wire) endpoint member atLeft
      have targetMember : fusionSourceEndpoint rightDiagram (iso.nodes right)
            endpoint ∈
          (rightDiagram.val.wires
            (iso.wires (fusionSourceWire leftDiagram wire))).endpoints := by
        rw [← fusionSourceWire_map iso left right eligible wire]
        exact retained.1
      change (iso.endpointMap (fusionSourceWire leftDiagram wire)
          (fusionSourceEndpoint leftDiagram right inverseEndpoint)).port =
        endpoint.port
      rw [sourceExact]
      rw [iso.endpointMap_right_inv (fusionSourceWire leftDiagram wire)
        (fusionSourceEndpoint rightDiagram (iso.nodes right) endpoint)
        targetMember]
      rfl

private noncomputable def fusionEndpointFiber
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId) :
    ConcreteIso.EndpointFiberEquiv
      (fusionNodeEquiv iso left right eligible)
      (fusionWireEquiv iso left right eligible) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨fusionMapEndpoint iso left right eligible wire endpoint.1 endpoint.2,
          fusionMapEndpoint_mem iso left right eligible wire endpoint.1
            endpoint.2⟩
      invFun := fun endpoint =>
        ⟨fusionInverseEndpoint iso left right eligible wire endpoint.1
            endpoint.2,
          fusionInverseEndpoint_mem iso left right eligible wire endpoint.1
            endpoint.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact fusionInverse_map iso left right eligible wire endpoint.1
          endpoint.2
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact fusionMap_inverse iso left right eligible wire endpoint.1
          endpoint.2 }
  corresponds := by
    intro endpoint
    by_cases atLeft : endpoint.1.node =
        fusionLeftNode leftDiagram left right eligible.distinct
    · have sourceIncident := fusionIncident_of_left_endpoint leftDiagram left
        right eligible wire endpoint.1 endpoint.2 atLeft
      have targetIncident := (fusionIncident_mem_map iso left right
        (fusionSourceWire leftDiagram wire)).mpr sourceIncident
      have targetIncidentActual : fusionSourceWire rightDiagram
            (fusionWireEquiv iso left right eligible wire) ∈
          fusionIncident rightDiagram (iso.nodes left) (iso.nodes right) := by
        rw [fusionSourceWire_map iso left right eligible wire]
        exact targetIncident
      have canonical := fusion_left_endpoint_canonical leftDiagram left right
        eligible wire endpoint.1 endpoint.2 atLeft
      have mappedLeft := (fusionMapEndpoint_left_iff iso left right eligible
        wire endpoint.1 endpoint.2).mpr atLeft
      unfold PortCorresponds
      constructor
      · simpa [atLeft, fusionLeftNode_map iso left right eligible] using
          mappedLeft
      · rw [fusionCandidate_node_source, fusionCandidate_node_source]
        rw [show fusionSourceNode leftDiagram right endpoint.1.node = left by
          rw [atLeft, fusionSourceNode_left]]
        rw [show fusionSourceNode rightDiagram (iso.nodes right)
            (fusionMapEndpoint iso left right eligible wire endpoint.1
              endpoint.2).node = iso.nodes left by
          rw [mappedLeft, fusionSourceNode_left]]
        simp only [if_pos]
        constructor
        · change eligible.leftIdentity.signature =
            eligible.leftIdentity.signature
          rfl
        · constructor
          · exact (fusionIncident_length_eq iso left right).symm
          · refine ⟨(fusionIncidentIndex leftDiagram left right
                (fusionSourceWire leftDiagram wire) sourceIncident).val,
              (fusionIncidentIndex rightDiagram (iso.nodes left)
                (iso.nodes right)
                (fusionSourceWire rightDiagram
                  (fusionWireEquiv iso left right eligible wire))
                targetIncidentActual).val, ?_, ?_⟩
            · exact congrArg CEndpoint.port canonical
            · rw [fusionMapEndpoint, dif_pos atLeft]
              rfl
    · let sourceWire := fusionSourceWire leftDiagram wire
      let sourceEndpoint := fusionSourceEndpoint leftDiagram right endpoint.1
      have retained := fusionRetained_of_not_left leftDiagram left right
        eligible wire endpoint.1 endpoint.2 atLeft
      have original := iso.endpointMap_corresponds sourceWire sourceEndpoint
        retained.1
      change PortCorresponds
        (fusionCandidate leftDiagram left right eligible)
        (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
          (transportFusionEligibility iso eligible))
        (fusionNodeEquiv iso left right eligible) endpoint.1
        (fusionMapEndpoint iso left right eligible wire endpoint.1 endpoint.2)
      unfold PortCorresponds at original ⊢
      have originalPort := original.2
      rw [original.1] at originalPort
      constructor
      · rw [fusionMapEndpoint, dif_neg atLeft]
      · have sourceNodeMap := fusionSourceNode_map iso left right eligible
            endpoint.1.node
        rw [show (fusionMapEndpoint iso left right eligible wire endpoint.1
            endpoint.2).node =
          fusionNodeEquiv iso left right eligible endpoint.1.node by
            rw [fusionMapEndpoint, dif_neg atLeft]]
        rw [fusionCandidate_node_source, fusionCandidate_node_source]
        rw [sourceNodeMap]
        rw [if_neg retained.2]
        have mappedNotLeft :
            iso.nodes (fusionSourceNode leftDiagram right endpoint.1.node) ≠
              iso.nodes left := by
          exact fun same => retained.2 (iso.nodes.injective same)
        rw [if_neg mappedNotLeft]
        have nodeTable := iso.node_table
          (fusionSourceNode leftDiagram right endpoint.1.node)
        rw [nodeTable]
        simp only [sourceEndpoint, fusionSourceEndpoint] at originalPort
        rw [nodeTable] at originalPort
        cases sourceData : leftDiagram.val.nodes
            (fusionSourceNode leftDiagram right endpoint.1.node) <;>
          simp [sourceData, CNode.rename, fusionMapEndpoint,
            fusionSourceEndpoint, atLeft] at originalPort ⊢
        all_goals simpa only [sourceWire, sourceEndpoint] using originalPort

private theorem fusion_root
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    fusionRegionEquiv iso left right eligible
        (fusionCandidate leftDiagram left right eligible).root =
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)).root := by
  change iso.regions leftDiagram.val.root = rightDiagram.val.root
  exact iso.root

private theorem fusion_region_table
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (region : (fusionCandidate leftDiagram left right eligible).RegionId) :
    (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)).regions
        (fusionRegionEquiv iso left right eligible region) =
      ((fusionCandidate leftDiagram left right eligible).regions region).rename
        (fusionRegionEquiv iso left right eligible) := by
  change rightDiagram.val.regions (iso.regions region) =
    (leftDiagram.val.regions region).rename iso.regions
  exact iso.region_table region

private theorem fusion_node_table
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (node : (fusionCandidate leftDiagram left right eligible).NodeId) :
    (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)).nodes
        (fusionNodeEquiv iso left right eligible node) =
      ((fusionCandidate leftDiagram left right eligible).nodes node).rename
        (fusionRegionEquiv iso left right eligible) := by
  rw [fusionCandidate_node_source, fusionCandidate_node_source]
  rw [fusionSourceNode_map iso left right eligible node]
  by_cases atLeft : fusionSourceNode leftDiagram right node = left
  · have mappedAtLeft :
        iso.nodes (fusionSourceNode leftDiagram right node) = iso.nodes left :=
      congrArg iso.nodes atLeft
    rw [if_pos atLeft, if_pos mappedAtLeft]
    change CNode.identity (iso.regions eligible.leftIdentity.region)
        eligible.leftIdentity.signature
        (fusionIncident rightDiagram (iso.nodes left)
          (iso.nodes right)).length =
      (CNode.identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (fusionIncident leftDiagram left right).length).rename iso.regions
    rw [fusionIncident_length_eq iso left right]
    rfl
  · have mappedNotLeft :
        iso.nodes (fusionSourceNode leftDiagram right node) ≠ iso.nodes left :=
      fun same => atLeft (iso.nodes.injective same)
    rw [if_neg atLeft, if_neg mappedNotLeft]
    exact iso.node_table _

private theorem fusion_wire_signature
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId) :
    ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)).wires
        (fusionWireEquiv iso left right eligible wire)).sig =
      ((fusionCandidate leftDiagram left right eligible).wires wire).sig := by
  rw [fusionCandidate_wire_signature_source,
    fusionCandidate_wire_signature_source]
  rw [fusionSourceWire_map iso left right eligible wire]
  exact iso.wire_signature _

private theorem fusion_wire_scope
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right)
    (wire : (fusionCandidate leftDiagram left right eligible).WireId) :
    ((fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
      (transportFusionEligibility iso eligible)).wires
        (fusionWireEquiv iso left right eligible wire)).scope =
      fusionRegionEquiv iso left right eligible
        ((fusionCandidate leftDiagram left right eligible).wires wire).scope := by
  rw [fusionCandidate_wire_scope_source,
    fusionCandidate_wire_scope_source]
  rw [fusionSourceWire_map iso left right eligible wire]
  exact iso.wire_scope _

/-- A paired Rule-3 rewrite constructs its target isomorphism from the
retained carriers and the reconstructed fused-identity endpoint fibers,
independently of identifiers and endpoint ordering. -/
noncomputable def transportFusionCandidate
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (eligible : FusionEligibility leftDiagram left right) :
    ConcreteIso
      (fusionCandidate leftDiagram left right eligible)
      (fusionCandidate rightDiagram (iso.nodes left) (iso.nodes right)
        (transportFusionEligibility iso eligible)) :=
  ConcreteIso.ofEquivs
    (fusionRegionEquiv iso left right eligible)
    (fusionNodeEquiv iso left right eligible)
    (fusionWireEquiv iso left right eligible)
    (fusion_root iso left right eligible)
    (fusion_region_table iso left right eligible)
    (fusion_node_table iso left right eligible)
    (fusion_wire_signature iso left right eligible)
    (fusion_wire_scope iso left right eligible)
    (fusionEndpointFiber iso left right eligible)

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
