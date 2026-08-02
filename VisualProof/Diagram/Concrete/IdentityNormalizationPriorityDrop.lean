import VisualProof.Diagram.Concrete.IdentityNormalizationPriority

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

private def dropSourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    source.val.NodeId :=
  (retainedNodes source.val [removed]).get target

private def dropSourceEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoint : CEndpoint (retainedNodes source.val [removed]).length) :
    CEndpoint source.val.nodeCount :=
  ⟨dropSourceNode source removed endpoint.node, endpoint.port⟩

private theorem retainedNodes_nodup
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    (retainedNodes source.val [removed]).Nodup :=
  (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem dropSourceNode_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    dropSourceNode source removed target ≠ removed := by
  have member := List.get_mem (retainedNodes source.val [removed]) target
  have accepted := (List.mem_filter.mp member).2
  unfold dropSourceNode
  simpa [retainedNodes] using of_decide_eq_true accepted

private theorem indexOf_dropSourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    Data.Finite.indexOf? (retainedNodes source.val [removed])
        (dropSourceNode source removed target) = some target :=
  Data.Finite.indexOf?_get_eq_some_of_nodup
    (retainedNodes_nodup source removed) target

private theorem dropEndpoint_mem_iff
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint (retainedNodes source.val [removed]).length) :
    endpoint ∈
        reindexEndpoints (retainedNodes source.val [removed])
          (eraseNodeEndpoints removed
            (source.val.wires wire).endpoints) ↔
      dropSourceEndpoint source removed endpoint ∈
        (source.val.wires wire).endpoints := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, retained, mapped⟩
    have candidateMember :
        candidate ∈ (source.val.wires wire).endpoints :=
      (List.mem_filter.mp retained).1
    unfold reindexEndpoint? at mapped
    cases found : Data.Finite.indexOf?
        (retainedNodes source.val [removed]) candidate.node with
    | none => simp [found] at mapped
    | some targetNode =>
        have mappedEndpoint :
            (⟨targetNode, candidate.port⟩ :
              CEndpoint (retainedNodes source.val [removed]).length) =
              endpoint := Option.some.inj (by simpa [found] using mapped)
        have sourceNode : candidate.node =
            dropSourceNode source removed endpoint.node := by
          have indexed := Data.Finite.indexOf?_sound found
          have targetNodeEq : targetNode = endpoint.node :=
            congrArg CEndpoint.node mappedEndpoint
          simpa [dropSourceNode, targetNodeEq] using indexed.symm
        have sourcePort : candidate.port = endpoint.port :=
          congrArg CEndpoint.port mappedEndpoint
        cases candidate
        cases endpoint
        simp only at sourceNode sourcePort ⊢
        subst sourceNode
        subst sourcePort
        exact candidateMember
  · intro incident
    let sourceEndpoint := dropSourceEndpoint source removed endpoint
    have retained : sourceEndpoint ∈
        eraseNodeEndpoints removed (source.val.wires wire).endpoints := by
      apply List.mem_filter.mpr
      exact ⟨incident, by
        simp [sourceEndpoint, dropSourceEndpoint,
          dropSourceNode_ne source removed endpoint.node]⟩
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint, retained, ?_⟩
    unfold reindexEndpoint?
    simp [sourceEndpoint, dropSourceEndpoint, indexOf_dropSourceNode]

private theorem dropCandidate_endpoint_mem_iff
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (wire : (dropCandidate source removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate source removed eligible).nodeCount) :
    endpoint ∈ ((dropCandidate source removed eligible).wires wire).endpoints ↔
      dropSourceEndpoint source removed endpoint ∈
        (source.val.wires (source.val.wiresList.get wire)).endpoints := by
  change endpoint ∈
      reindexEndpoints (retainedNodes source.val [removed])
        (eraseNodeEndpoints removed
          (source.val.wires (source.val.wiresList.get wire)).endpoints) ↔ _
  exact dropEndpoint_mem_iff source removed
    (source.val.wiresList.get wire) endpoint

@[simp] private theorem dropCandidate_node_source
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (node : (dropCandidate source removed eligible).NodeId) :
    (dropCandidate source removed eligible).nodes node =
      source.val.nodes (dropSourceNode source removed node) := by
  rfl

private def dropRegionEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    Data.Finite.FiniteEquiv
      (dropCandidate left removed eligible).RegionId
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).RegionId := by
  change Data.Finite.FiniteEquiv left.val.RegionId right.val.RegionId
  exact iso.regions

private theorem retainedNodes_mem_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (node : left.val.NodeId) :
    iso.nodes node ∈ retainedNodes right.val [iso.nodes removed] ↔
      node ∈ retainedNodes left.val [removed] := by
  simp only [retainedNodes, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange, List.mem_filter, List.mem_singleton,
    List.mem_finRange, true_and, decide_eq_true_eq]
  exact not_congr iso.nodes.injective.eq_iff

private def dropNodeEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    Data.Finite.FiniteEquiv
      (dropCandidate left removed eligible).NodeId
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).NodeId :=
  Data.Finite.FiniteEquiv.restrictLists iso.nodes
    (retainedNodes left.val [removed])
    (retainedNodes right.val [iso.nodes removed])
    (retainedNodes_nodup left removed)
    (retainedNodes_nodup right (iso.nodes removed))
    (retainedNodes_mem_iff iso removed)

private def dropWireEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    Data.Finite.FiniteEquiv
      (dropCandidate left removed eligible).WireId
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).WireId :=
  Data.Finite.FiniteEquiv.restrictLists iso.wires
    left.val.wiresList right.val.wiresList
    (Data.Finite.allFin_nodup left.val.wireCount)
    (Data.Finite.allFin_nodup right.val.wireCount)
    (fun wire => by
      simp [ConcreteDiagram.wiresList, Data.Finite.mem_allFin])

private theorem dropRegionEquiv_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (region : (dropCandidate left removed eligible).RegionId) :
    dropRegionEquiv iso removed eligible region = iso.regions region := by
  rfl

private theorem dropSourceNode_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (node : (dropCandidate left removed eligible).NodeId) :
    dropSourceNode right (iso.nodes removed)
        (dropNodeEquiv iso removed eligible node) =
      iso.nodes (dropSourceNode left removed node) := by
  unfold dropSourceNode
  exact Data.Finite.FiniteEquiv.restrictLists_spec iso.nodes
    (retainedNodes left.val [removed])
    (retainedNodes right.val [iso.nodes removed])
    (retainedNodes_nodup left removed)
    (retainedNodes_nodup right (iso.nodes removed))
    (retainedNodes_mem_iff iso removed) node

private theorem dropSourceWire_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    right.val.wiresList.get (dropWireEquiv iso removed eligible wire) =
      iso.wires (left.val.wiresList.get wire) := by
  exact Data.Finite.FiniteEquiv.restrictLists_spec iso.wires
    left.val.wiresList right.val.wiresList
    (Data.Finite.allFin_nodup left.val.wireCount)
    (Data.Finite.allFin_nodup right.val.wireCount)
    (fun sourceWire => by
      simp [ConcreteDiagram.wiresList, Data.Finite.mem_allFin]) wire

private def dropLeftWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (wire : (dropCandidate source removed eligible).WireId) :
    source.val.WireId :=
  source.val.wiresList.get wire

private def dropMapEndpoint
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount) :
    CEndpoint
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).nodeCount :=
  let sourceEndpoint := dropSourceEndpoint left removed endpoint
  let mapped := iso.endpointMap
    (dropLeftWire left removed eligible wire) sourceEndpoint
  ⟨dropNodeEquiv iso removed eligible endpoint.node, mapped.port⟩

private def dropInverseEndpoint
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).nodeCount) :
    CEndpoint (dropCandidate left removed eligible).nodeCount :=
  let targetEndpoint := dropSourceEndpoint right
    (iso.nodes removed) endpoint
  let mapped := iso.endpointInverse
    (dropLeftWire left removed eligible wire) targetEndpoint
  ⟨(dropNodeEquiv iso removed eligible).symm endpoint.node, mapped.port⟩

private theorem dropMapEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropSourceEndpoint right (iso.nodes removed)
        (dropMapEndpoint iso removed eligible wire endpoint) =
      iso.endpointMap (dropLeftWire left removed eligible wire)
        (dropSourceEndpoint left removed endpoint) := by
  apply endpoint_eq
  · change dropSourceNode right (iso.nodes removed)
        (dropNodeEquiv iso removed eligible endpoint.node) = _
    rw [dropSourceNode_map iso removed eligible endpoint.node]
    exact (iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint)
      ((dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
        member)).1.symm
  · rfl

private theorem dropMapEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropMapEndpoint iso removed eligible wire endpoint ∈
      ((dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).wires
          (dropWireEquiv iso removed eligible wire)).endpoints := by
  apply (dropCandidate_endpoint_mem_iff right (iso.nodes removed)
    (transportDropEligibility iso eligible)
    (dropWireEquiv iso removed eligible wire)
    (dropMapEndpoint iso removed eligible wire endpoint)).mpr
  rw [dropMapEndpoint_source iso removed eligible wire endpoint member]
  rw [dropSourceWire_map iso removed eligible wire]
  exact iso.endpointMap_mem (dropLeftWire left removed eligible wire)
    (dropSourceEndpoint left removed endpoint)
    ((dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
      member)

private theorem dropInverseEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).wires
          (dropWireEquiv iso removed eligible wire)).endpoints) :
    dropSourceEndpoint left removed
        (dropInverseEndpoint iso removed eligible wire endpoint) =
      iso.endpointInverse (dropLeftWire left removed eligible wire)
        (dropSourceEndpoint right (iso.nodes removed) endpoint) := by
  apply endpoint_eq
  · have targetMember :=
      (dropCandidate_endpoint_mem_iff right (iso.nodes removed)
        (transportDropEligibility iso eligible)
        (dropWireEquiv iso removed eligible wire) endpoint).mp member
    rw [dropSourceWire_map iso removed eligible wire] at targetMember
    let sourceEndpoint := iso.endpointInverse
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (iso.nodes removed) endpoint)
    have sourceMember := iso.endpointInverse_mem
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (iso.nodes removed) endpoint) targetMember
    have corresponds := iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire) sourceEndpoint sourceMember
    rw [iso.endpointMap_right_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (iso.nodes removed) endpoint)
      targetMember] at corresponds
    have mappedSource := dropSourceNode_map iso removed eligible
      ((dropNodeEquiv iso removed eligible).symm endpoint.node)
    rw [Data.Finite.FiniteEquiv.apply_symm_apply] at mappedSource
    change dropSourceNode left removed
      ((dropNodeEquiv iso removed eligible).symm endpoint.node) =
        sourceEndpoint.node
    exact iso.nodes.injective
      (mappedSource.symm.trans corresponds.1)
  · rfl

private theorem dropInverseEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).wires
          (dropWireEquiv iso removed eligible wire)).endpoints) :
    dropInverseEndpoint iso removed eligible wire endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints := by
  apply (dropCandidate_endpoint_mem_iff left removed eligible wire
    (dropInverseEndpoint iso removed eligible wire endpoint)).mpr
  rw [dropInverseEndpoint_source iso removed eligible wire endpoint member]
  have targetMember :=
    (dropCandidate_endpoint_mem_iff right (iso.nodes removed)
      (transportDropEligibility iso eligible)
      (dropWireEquiv iso removed eligible wire) endpoint).mp member
  rw [dropSourceWire_map iso removed eligible wire] at targetMember
  exact iso.endpointInverse_mem (dropLeftWire left removed eligible wire)
    (dropSourceEndpoint right (iso.nodes removed) endpoint) targetMember

private theorem dropInverse_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropInverseEndpoint iso removed eligible wire
        (dropMapEndpoint iso removed eligible wire endpoint) = endpoint := by
  apply endpoint_eq
  · change (dropNodeEquiv iso removed eligible).symm
        (dropNodeEquiv iso removed eligible endpoint.node) = endpoint.node
    exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
  · have sourceMember :=
      (dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
        member
    have sourceExact := dropMapEndpoint_source iso removed eligible wire
      endpoint member
    change (iso.endpointInverse
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (iso.nodes removed)
        (dropMapEndpoint iso removed eligible wire endpoint))).port =
      endpoint.port
    rw [sourceExact]
    rw [iso.endpointMap_left_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint) sourceMember]
    rfl

private theorem dropMap_inverse
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).wires
          (dropWireEquiv iso removed eligible wire)).endpoints) :
    dropMapEndpoint iso removed eligible wire
        (dropInverseEndpoint iso removed eligible wire endpoint) = endpoint := by
  apply endpoint_eq
  · change dropNodeEquiv iso removed eligible
        ((dropNodeEquiv iso removed eligible).symm endpoint.node) = endpoint.node
    exact Data.Finite.FiniteEquiv.apply_symm_apply _ _
  · have targetMember :=
      (dropCandidate_endpoint_mem_iff right (iso.nodes removed)
        (transportDropEligibility iso eligible)
        (dropWireEquiv iso removed eligible wire) endpoint).mp member
    rw [dropSourceWire_map iso removed eligible wire] at targetMember
    have sourceExact := dropInverseEndpoint_source iso removed eligible wire
      endpoint member
    change (iso.endpointMap
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed
        (dropInverseEndpoint iso removed eligible wire endpoint))).port =
      endpoint.port
    rw [sourceExact]
    rw [iso.endpointMap_right_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (iso.nodes removed) endpoint)
      targetMember]
    rfl

private def dropEndpointFiber
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ConcreteIso.EndpointFiberEquiv
      (dropNodeEquiv iso removed eligible)
      (dropWireEquiv iso removed eligible) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨dropMapEndpoint iso removed eligible wire endpoint.1,
          dropMapEndpoint_mem iso removed eligible wire endpoint.1
            endpoint.2⟩
      invFun := fun endpoint =>
        ⟨dropInverseEndpoint iso removed eligible wire endpoint.1,
          dropInverseEndpoint_mem iso removed eligible wire endpoint.1
            endpoint.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact dropInverse_map iso removed eligible wire endpoint.1 endpoint.2
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact dropMap_inverse iso removed eligible wire endpoint.1 endpoint.2 }
  corresponds := by
    intro endpoint
    have sourceMember :=
      (dropCandidate_endpoint_mem_iff left removed eligible wire endpoint.1).mp
        endpoint.2
    have original := iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint.1) sourceMember
    change PortCorresponds
      (dropCandidate left removed eligible)
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible))
      (dropNodeEquiv iso removed eligible) endpoint.1
      (dropMapEndpoint iso removed eligible wire endpoint.1)
    unfold PortCorresponds at original ⊢
    have originalPort := original.2
    rw [original.1] at originalPort
    constructor
    · rfl
    · have sourceNodeMap := dropSourceNode_map iso removed eligible
        endpoint.1.node
      rw [show (dropMapEndpoint iso removed eligible wire endpoint.1).node =
        dropNodeEquiv iso removed eligible endpoint.1.node by rfl]
      rw [dropCandidate_node_source, dropCandidate_node_source]
      rw [sourceNodeMap]
      have nodeTable := iso.node_table
        (dropSourceNode left removed endpoint.1.node)
      rw [nodeTable]
      simp only [dropSourceEndpoint] at originalPort
      rw [nodeTable] at originalPort
      cases sourceData : left.val.nodes
          (dropSourceNode left removed endpoint.1.node) <;>
        simp [sourceData, CNode.rename, dropMapEndpoint,
          dropSourceEndpoint] at originalPort ⊢
      all_goals exact originalPort

private theorem drop_root
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    dropRegionEquiv iso removed eligible
        (dropCandidate left removed eligible).root =
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)).root := by
  change iso.regions left.val.root = right.val.root
  exact iso.root

private theorem drop_region_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (region : (dropCandidate left removed eligible).RegionId) :
    (dropCandidate right (iso.nodes removed)
      (transportDropEligibility iso eligible)).regions
        (dropRegionEquiv iso removed eligible region) =
      ((dropCandidate left removed eligible).regions region).rename
        (dropRegionEquiv iso removed eligible) := by
  change right.val.regions (iso.regions region) =
    (left.val.regions region).rename iso.regions
  exact iso.region_table region

private theorem drop_node_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (node : (dropCandidate left removed eligible).NodeId) :
    (dropCandidate right (iso.nodes removed)
      (transportDropEligibility iso eligible)).nodes
        (dropNodeEquiv iso removed eligible node) =
      ((dropCandidate left removed eligible).nodes node).rename
        (dropRegionEquiv iso removed eligible) := by
  rw [dropCandidate_node_source, dropCandidate_node_source]
  rw [dropSourceNode_map iso removed eligible node]
  exact iso.node_table _

private theorem drop_wire_signature
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ((dropCandidate right (iso.nodes removed)
      (transportDropEligibility iso eligible)).wires
        (dropWireEquiv iso removed eligible wire)).sig =
      ((dropCandidate left removed eligible).wires wire).sig := by
  change (right.val.wires
      (right.val.wiresList.get (dropWireEquiv iso removed eligible wire))).sig =
    (left.val.wires (left.val.wiresList.get wire)).sig
  rw [dropSourceWire_map iso removed eligible wire]
  exact iso.wire_signature _

private theorem drop_wire_scope
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ((dropCandidate right (iso.nodes removed)
      (transportDropEligibility iso eligible)).wires
        (dropWireEquiv iso removed eligible wire)).scope =
      dropRegionEquiv iso removed eligible
        ((dropCandidate left removed eligible).wires wire).scope := by
  let sourceWire := left.val.wiresList.get wire
  change (right.val.wires
      (right.val.wiresList.get (dropWireEquiv iso removed eligible wire))).scope = _
  rw [dropSourceWire_map iso removed eligible wire]
  exact iso.wire_scope sourceWire

/-- Dense position of a distinct source node after a Rule-1 deletion. -/
def dropRetainedNode
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (different : other ≠ removed) :
    (dropCandidate source removed eligible).NodeId :=
  eraseNodeIndex source removed other (by
    simp [retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin, different])

@[simp] theorem dropSourceNode_retained
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (different : other ≠ removed) :
    dropSourceNode source removed
        (dropRetainedNode source removed other eligible different) = other := by
  unfold dropRetainedNode dropSourceNode eraseNodeIndex
  apply Data.Finite.indexOf?_sound
  exact (Option.some_get (Data.Finite.indexOf?_isSome_iff.mpr (by
    simp [retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin, different]))).symm

private theorem map_allFin_get (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

/-- Sequential singleton deletion enumerates exactly the original nodes with
both named nodes removed.  This is the carrier identity underlying the
drop/drop critical-pair isomorphism. -/
private theorem doubleDropNodeOrigins
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (different : other ≠ removed) :
    (retainedNodes (dropCandidate source removed eligible)
      [dropRetainedNode source removed other eligible different]).map
        (retainedNodes source.val [removed]).get =
      retainedNodes source.val [removed, other] := by
  let first := retainedNodes source.val [removed]
  let mapped := dropRetainedNode source removed other eligible different
  have getMapped : first.get mapped = other := by
    exact dropSourceNode_retained source removed other eligible different
  have firstNodup : first.Nodup := by
    dsimp only [first]
    exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _
  change ((Data.Finite.allFin first.length).filter
      (fun node => decide (node ∉ [mapped]))).map first.get = _
  have predicate :
      (fun node : Fin first.length => decide (node ∉ [mapped])) =
      (fun node => decide (first.get node ≠ other)) := by
    funext node
    rw [decide_eq_decide]
    constructor
    · intro retained sameOrigin
      have nodeDifferent : node ≠ mapped := fun same =>
        retained (same ▸ List.mem_cons_self)
      apply nodeDifferent
      apply Fin.ext
      apply (List.getElem_inj firstNodup).mp
      simpa only [List.get_eq_getElem] using sameOrigin.trans getMapped.symm
    · intro originDifferent sameNode
      have nodeExact : node = mapped := List.mem_singleton.mp sameNode
      subst node
      exact originDifferent getMapped
  have filteredExact :
      (Data.Finite.allFin first.length).filter
          (fun node => decide (node ∉ [mapped])) =
        (Data.Finite.allFin first.length).filter
          (fun node => decide (first.get node ≠ other)) :=
    congrArg (fun selection =>
      (Data.Finite.allFin first.length).filter selection) predicate
  rw [filteredExact]
  have mappedFilter :
      ((Data.Finite.allFin first.length).filter
        (fun node => decide (first.get node ≠ other))).map first.get =
      ((Data.Finite.allFin first.length).map first.get).filter
        (fun node => decide (node ≠ other)) := by
    simpa only [Function.comp_apply] using
      (List.filter_map
        (f := first.get)
        (p := fun node => decide (node ≠ other))
        (l := Data.Finite.allFin first.length)).symm
  rw [mappedFilter]
  rw [map_allFin_get]
  simp only [first, retainedNodes, List.filter_filter,
    List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
  apply List.filter_congr
  intro node _
  rw [← Bool.decide_and]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨notOther, notRemoved⟩ (sameRemoved | sameOther)
    · exact notRemoved sameRemoved
    · exact notOther sameOther
  · intro neither
    exact ⟨fun same => neither (Or.inr same),
      fun same => neither (Or.inl same)⟩

private def dropRetainedWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : DropEligibility source removed) :
    Data.Finite.FiniteEquiv source.val.WireId
      (dropCandidate source removed eligible).WireId where
  toFun := eraseNodeWire source removed
  invFun := fun wire => source.val.wiresList.get wire
  left_inv := by
    intro wire
    apply Fin.ext
    simp [eraseNodeWire, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  right_inv := by
    intro wire
    apply Fin.ext
    simp [eraseNodeWire, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]

@[simp] private theorem dropSourceWire_retained
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (wire : source.val.WireId) :
    source.val.wiresList.get (dropRetainedWire source removed eligible wire) =
      wire := by
  exact (dropRetainedWire source removed eligible).left_inv wire

private theorem dropIdentityIncident_mem_iff
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (different : other ≠ removed)
    (wire : source.val.WireId) :
    dropRetainedWire source removed eligible wire ∈
        (dropCandidate source removed eligible).identityIncidentWires
          (dropRetainedNode source removed other eligible different) ↔
      wire ∈ source.val.identityIncidentWires other := by
  constructor
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires
        (dropCandidate source removed eligible)
        (dropRetainedNode source removed other eligible different)
        (dropRetainedWire source removed eligible wire)).mp incident
    have sourceMember :=
      (dropCandidate_endpoint_mem_iff source removed eligible
        (dropRetainedWire source removed eligible wire) endpoint).mp
        endpointMember
    refine (mem_identityIncidentWires source.val other wire).mpr
      ⟨dropSourceEndpoint source removed endpoint, ?_, ?_⟩
    · rw [dropSourceWire_retained] at sourceMember
      exact sourceMember
    · change dropSourceNode source removed endpoint.node = other
      rw [endpointNode, dropSourceNode_retained]
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires source.val other wire).mp incident
    have endpointDifferent : endpoint.node ≠ removed := by
      intro same
      exact different (endpointNode.symm.trans same)
    let mapped := eraseNodeEndpoint source removed endpoint endpointDifferent
    have mappedMember : mapped ∈
        ((dropCandidate source removed eligible).wires
          (dropRetainedWire source removed eligible wire)).endpoints := by
      have raw := eraseNodeEndpoint_mem source removed wire endpoint
        endpointDifferent endpointMember
      change mapped ∈
        ((eraseNodeCandidate source removed).wires
          (dropRetainedWire source removed eligible wire)).endpoints
      exact raw
    apply (mem_identityIncidentWires
      (dropCandidate source removed eligible)
      (dropRetainedNode source removed other eligible different)
      (dropRetainedWire source removed eligible wire)).mpr
    refine ⟨mapped, mappedMember, ?_⟩
    unfold mapped eraseNodeEndpoint dropRetainedNode
    apply Fin.ext
    simp only
    simpa only [endpointNode]

private theorem dropIncident_length_eq
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : DropEligibility source removed)
    (different : other ≠ removed) :
    ((dropCandidate source removed eligible).identityIncidentWires
      (dropRetainedNode source removed other eligible different)).length =
      (source.val.identityIncidentWires other).length := by
  let equivalence := dropRetainedWire source removed eligible
  let sourceWires := source.val.identityIncidentWires other
  let targetWires :=
    (dropCandidate source removed eligible).identityIncidentWires
      (dropRetainedNode source removed other eligible different)
  apply Nat.le_antisymm
  · let restricted := Data.Finite.FiniteEquiv.restrictLists equivalence.symm
      targetWires sourceWires
      ((dropCandidate source removed eligible).identityIncidentWires_nodup _)
      (source.val.identityIncidentWires_nodup other)
      (fun wire => by
        simpa only [equivalence, sourceWires, targetWires,
          Data.Finite.FiniteEquiv.apply_symm_apply] using
          (dropIdentityIncident_mem_iff source removed other eligible different
            (equivalence.symm wire)).symm)
    exact Data.Finite.fin_card_le_of_injective restricted restricted.injective
  · let restricted := Data.Finite.FiniteEquiv.restrictLists equivalence
      sourceWires targetWires
      (source.val.identityIncidentWires_nodup other)
      ((dropCandidate source removed eligible).identityIncidentWires_nodup _)
      (dropIdentityIncident_mem_iff source removed other eligible different)
    exact Data.Finite.fin_card_le_of_injective restricted restricted.injective

/-- A distinct Rule-1 candidate remains Rule-1 eligible after the first
deletion, so priority recomputation stays in the drop class. -/
def dropEligibilityAfter
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (removedEligible : DropEligibility source removed)
    (otherEligible : DropEligibility source other)
    (different : other ≠ removed) :
    DropEligibility
      (⟨dropCandidate source removed removedEligible,
        dropCandidate_wellFormed source removed removedEligible⟩ :
        CheckedDiagram definitions)
      (dropRetainedNode source removed other removedEligible different) where
  identity :=
    { region := eraseNodeRegion source removed otherEligible.identity.region
      signature := otherEligible.identity.signature
      arity := otherEligible.identity.arity
      node_eq := by
        change (eraseNodeCandidate source removed).nodes
            (eraseNodeIndex source removed other _) = _
        rw [eraseNodeIndex_data source removed other]
        rw [otherEligible.identity.node_eq]
        rfl }
  incident_lt_two := by
    rw [dropIncident_length_eq source removed other removedEligible different]
    exact otherEligible.incident_lt_two

/-- Checked endpoint of deleting two distinct Rule-1 candidates in the named
order. -/
def doubleDropTarget
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first) : CheckedDiagram definitions :=
  let firstTarget : CheckedDiagram definitions :=
    ⟨dropCandidate source first firstEligible,
      dropCandidate_wellFormed source first firstEligible⟩
  let mapped :=
    dropRetainedNode source first second firstEligible different
  let mappedEligible :=
    dropEligibilityAfter source first second firstEligible secondEligible
      different
  ⟨dropCandidate firstTarget mapped mappedEligible,
    dropCandidate_wellFormed firstTarget mapped mappedEligible⟩

private theorem retainedNodes_pair_comm
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    retainedNodes source.val [left, right] =
      retainedNodes source.val [right, left] := by
  unfold retainedNodes
  apply List.filter_congr
  intro node _
  rw [decide_eq_decide]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact not_congr or_comm

private def doubleDropOrigins
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (different : second ≠ first) : List source.val.NodeId :=
  (retainedNodes (dropCandidate source first firstEligible)
    [dropRetainedNode source first second firstEligible different]).map
      (retainedNodes source.val [first]).get

private theorem doubleDropOrigins_exact
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (different : second ≠ first) :
    doubleDropOrigins source first second firstEligible different =
      retainedNodes source.val [first, second] :=
  doubleDropNodeOrigins source first second firstEligible different

private theorem doubleDropOrigins_perm
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left) :
    (doubleDropOrigins source left right leftEligible different).Perm
      (doubleDropOrigins source right left rightEligible
        (fun same => different same.symm)) := by
  rw [doubleDropOrigins_exact, doubleDropOrigins_exact,
    retainedNodes_pair_comm]

private theorem doubleDropOrigins_length
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first) :
    (doubleDropTarget source first second firstEligible secondEligible
        different).val.nodeCount =
      (doubleDropOrigins source first second firstEligible different).length := by
  simp [doubleDropTarget, doubleDropOrigins, dropRetainedNode,
    dropEligibilityAfter, dropCandidate, eraseNodeCandidate]

private def doubleDropOriginNode
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (node : (doubleDropTarget source first second firstEligible secondEligible
      different).val.NodeId) : source.val.NodeId :=
  (doubleDropOrigins source first second firstEligible different).get
    (Fin.cast
      (doubleDropOrigins_length source first second firstEligible
        secondEligible different)
      node)

/-- Dense node correspondence between the two deletion orders, selected by
the common original source node carried at each position. -/
noncomputable def doubleDropNodeEquiv
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left) :
    Data.Finite.FiniteEquiv
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.NodeId
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.NodeId :=
  let leftCast := Data.Finite.FiniteEquiv.finCast
    (doubleDropOrigins_length source left right leftEligible rightEligible
      different)
  let origins :=
    (Data.Finite.FiniteEquiv.ofListPermStable
      (doubleDropOrigins_perm source left right leftEligible rightEligible
        different)).val
  let rightCast := Data.Finite.FiniteEquiv.finCast
    (doubleDropOrigins_length source right left rightEligible leftEligible
      (fun same => different same.symm))
  leftCast.trans (origins.trans rightCast.symm)

private theorem doubleDropNodeEquiv_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (node : (doubleDropTarget source left right leftEligible rightEligible
      different).val.NodeId) :
    doubleDropOriginNode source right left rightEligible leftEligible
        (fun same => different same.symm)
        (doubleDropNodeEquiv source left right leftEligible rightEligible
          different node) =
      doubleDropOriginNode source left right leftEligible rightEligible
        different node := by
  let leftCast := Data.Finite.FiniteEquiv.finCast
    (doubleDropOrigins_length source left right leftEligible rightEligible
      different)
  let origins :=
    Data.Finite.FiniteEquiv.ofListPermStable
      (doubleDropOrigins_perm source left right leftEligible rightEligible
        different)
  have exact := origins.property (leftCast node)
  simpa [doubleDropNodeEquiv, doubleDropOriginNode, leftCast, origins,
    Data.Finite.FiniteEquiv.trans_apply] using exact

private def doubleDropSourceWire
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (wire : (doubleDropTarget source first second firstEligible secondEligible
      different).val.WireId) : source.val.WireId :=
  let firstTarget : CheckedDiagram definitions :=
    ⟨dropCandidate source first firstEligible,
      dropCandidate_wellFormed source first firstEligible⟩
  source.val.wiresList.get (firstTarget.val.wiresList.get wire)

private def doubleDropSourceEndpoint
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (endpoint : CEndpoint
      (doubleDropTarget source first second firstEligible secondEligible
        different).val.nodeCount) : CEndpoint source.val.nodeCount :=
  let firstTarget : CheckedDiagram definitions :=
    ⟨dropCandidate source first firstEligible,
      dropCandidate_wellFormed source first firstEligible⟩
  let mapped := dropRetainedNode source first second firstEligible different
  dropSourceEndpoint source first
    (dropSourceEndpoint firstTarget mapped endpoint)

private theorem doubleDrop_node_source
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (node : (doubleDropTarget source first second firstEligible secondEligible
      different).val.NodeId) :
    (doubleDropTarget source first second firstEligible secondEligible
      different).val.nodes node =
      source.val.nodes
        (doubleDropOriginNode source first second firstEligible secondEligible
          different node) := by
  simp only [doubleDropTarget, dropCandidate_node_source]
  unfold doubleDropOriginNode doubleDropOrigins
  simp only [List.get_eq_getElem, List.getElem_map]
  congr 2 <;> apply Fin.ext <;> rfl

private theorem doubleDrop_endpoint_mem_iff
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (wire : (doubleDropTarget source first second firstEligible secondEligible
      different).val.WireId)
    (endpoint : CEndpoint
      (doubleDropTarget source first second firstEligible secondEligible
        different).val.nodeCount) :
    endpoint ∈
        ((doubleDropTarget source first second firstEligible secondEligible
          different).val.wires wire).endpoints ↔
      doubleDropSourceEndpoint source first second firstEligible secondEligible
          different endpoint ∈
        (source.val.wires
          (doubleDropSourceWire source first second firstEligible secondEligible
            different wire)).endpoints := by
  simp only [doubleDropTarget, doubleDropSourceEndpoint,
    doubleDropSourceWire]
  let firstTarget : CheckedDiagram definitions :=
    ⟨dropCandidate source first firstEligible,
      dropCandidate_wellFormed source first firstEligible⟩
  let mapped := dropRetainedNode source first second firstEligible different
  let mappedEligible :=
    dropEligibilityAfter source first second firstEligible secondEligible
      different
  constructor
  · intro member
    have inner := (dropCandidate_endpoint_mem_iff firstTarget mapped
      mappedEligible wire endpoint).mp member
    exact (dropCandidate_endpoint_mem_iff source first firstEligible
      (firstTarget.val.wiresList.get wire)
      (dropSourceEndpoint firstTarget mapped endpoint)).mp inner
  · intro member
    have outer := (dropCandidate_endpoint_mem_iff source first firstEligible
      (firstTarget.val.wiresList.get wire)
      (dropSourceEndpoint firstTarget mapped endpoint)).mpr member
    exact (dropCandidate_endpoint_mem_iff firstTarget mapped mappedEligible
      wire endpoint).mpr outer

private theorem doubleDropSourceEndpoint_node
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first)
    (endpoint : CEndpoint
      (doubleDropTarget source first second firstEligible secondEligible
        different).val.nodeCount) :
    (doubleDropSourceEndpoint source first second firstEligible secondEligible
      different endpoint).node =
      doubleDropOriginNode source first second firstEligible secondEligible
        different endpoint.node := by
  unfold doubleDropSourceEndpoint dropSourceEndpoint
  unfold doubleDropOriginNode doubleDropOrigins
  simp only [List.get_eq_getElem, List.getElem_map]
  congr 1 <;> apply Fin.ext <;> rfl

private def doubleDropRegionEquiv
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left) :
    Data.Finite.FiniteEquiv
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.RegionId
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.RegionId := by
  change Data.Finite.FiniteEquiv source.val.RegionId source.val.RegionId
  exact Data.Finite.FiniteEquiv.refl _

private theorem doubleDropWireCount
    (source : CheckedDiagram definitions)
    (first second : source.val.NodeId)
    (firstEligible : DropEligibility source first)
    (secondEligible : DropEligibility source second)
    (different : second ≠ first) :
    (doubleDropTarget source first second firstEligible secondEligible
      different).val.wireCount = source.val.wireCount := by
  simp [doubleDropTarget, dropCandidate, eraseNodeCandidate,
    ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]

private def doubleDropWireEquiv
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left) :
    Data.Finite.FiniteEquiv
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.WireId
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.WireId := by
  exact Data.Finite.FiniteEquiv.finCast
    ((doubleDropWireCount source left right leftEligible rightEligible
      different).trans
      (doubleDropWireCount source right left rightEligible leftEligible
        (fun same => different same.symm)).symm)

noncomputable def doubleDropMapEndpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (endpoint : CEndpoint
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.nodeCount) :
    CEndpoint
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.nodeCount :=
  ⟨doubleDropNodeEquiv source left right leftEligible rightEligible
      different endpoint.node,
    endpoint.port⟩

private noncomputable def doubleDropInverseEndpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (endpoint : CEndpoint
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.nodeCount) :
    CEndpoint
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.nodeCount :=
  ⟨(doubleDropNodeEquiv source left right leftEligible rightEligible
      different).symm endpoint.node,
    endpoint.port⟩

private theorem doubleDropSourceWire_map
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (wire : (doubleDropTarget source left right leftEligible rightEligible
      different).val.WireId) :
    doubleDropSourceWire source right left rightEligible leftEligible
        (fun same => different same.symm)
        (doubleDropWireEquiv source left right leftEligible rightEligible
          different wire) =
      doubleDropSourceWire source left right leftEligible rightEligible
        different wire := by
  apply Fin.ext
  rfl

private theorem doubleDropSourceEndpoint_map
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (endpoint : CEndpoint
      (doubleDropTarget source left right leftEligible rightEligible
        different).val.nodeCount) :
    doubleDropSourceEndpoint source right left rightEligible leftEligible
        (fun same => different same.symm)
        (doubleDropMapEndpoint source left right leftEligible rightEligible
          different endpoint) =
      doubleDropSourceEndpoint source left right leftEligible rightEligible
        different endpoint := by
  apply endpoint_eq
  · rw [doubleDropSourceEndpoint_node, doubleDropSourceEndpoint_node]
    exact doubleDropNodeEquiv_origin source left right leftEligible
      rightEligible different endpoint.node
  · rfl

private theorem doubleDropSourceEndpoint_inverse
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (endpoint : CEndpoint
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val.nodeCount) :
    doubleDropSourceEndpoint source left right leftEligible rightEligible
        different
        (doubleDropInverseEndpoint source left right leftEligible rightEligible
          different endpoint) =
      doubleDropSourceEndpoint source right left rightEligible leftEligible
        (fun same => different same.symm) endpoint := by
  have mapped := doubleDropSourceEndpoint_map source left right leftEligible
    rightEligible different
    (doubleDropInverseEndpoint source left right leftEligible rightEligible
      different endpoint)
  have mapInverse :
      doubleDropMapEndpoint source left right leftEligible rightEligible
          different
          (doubleDropInverseEndpoint source left right leftEligible
            rightEligible different endpoint) = endpoint := by
    apply endpoint_eq
    · exact (doubleDropNodeEquiv source left right leftEligible
        rightEligible different).right_inv endpoint.node
    · rfl
  rw [mapInverse] at mapped
  exact mapped.symm

noncomputable def doubleDropEndpointFiber
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left)
    (wire : (doubleDropTarget source left right leftEligible rightEligible
      different).val.WireId) :
    ConcreteIso.EndpointFiberEquiv
      (doubleDropNodeEquiv source left right leftEligible rightEligible
        different)
      (doubleDropWireEquiv source left right leftEligible rightEligible
        different) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨doubleDropMapEndpoint source left right leftEligible rightEligible
          different endpoint.1, by
            apply (doubleDrop_endpoint_mem_iff source right left rightEligible
              leftEligible (fun same => different same.symm) _ _).mpr
            rw [doubleDropSourceWire_map, doubleDropSourceEndpoint_map]
            exact (doubleDrop_endpoint_mem_iff source left right leftEligible
              rightEligible different wire endpoint.1).mp endpoint.2⟩
      invFun := fun endpoint =>
        ⟨doubleDropInverseEndpoint source left right leftEligible
          rightEligible different endpoint.1, by
            apply (doubleDrop_endpoint_mem_iff source left right leftEligible
              rightEligible different _ _).mpr
            rw [doubleDropSourceEndpoint_inverse]
            exact (doubleDrop_endpoint_mem_iff source right left rightEligible
              leftEligible (fun same => different same.symm) _ endpoint.1).mp
                endpoint.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        apply endpoint_eq
        · exact (doubleDropNodeEquiv source left right leftEligible
            rightEligible different).left_inv endpoint.1.node
        · rfl
      right_inv := by
        intro endpoint
        apply Subtype.ext
        apply endpoint_eq
        · exact (doubleDropNodeEquiv source left right leftEligible
            rightEligible different).right_inv endpoint.1.node
        · rfl }
  corresponds := by
    intro endpoint
    unfold PortCorresponds doubleDropMapEndpoint
    constructor
    · rfl
    · have required := ConcreteDiagram.incident_port_required definitions
        (doubleDropTarget source left right leftEligible rightEligible
          different).val
        (doubleDropTarget source left right leftEligible rightEligible
          different).property wire endpoint.1 endpoint.2
      have nodeExact :
          (doubleDropTarget source right left rightEligible leftEligible
            (fun same => different same.symm)).val.nodes
              (doubleDropNodeEquiv source left right leftEligible rightEligible
                different endpoint.1.node) =
            (doubleDropTarget source left right leftEligible rightEligible
              different).val.nodes endpoint.1.node := by
        rw [doubleDrop_node_source, doubleDrop_node_source,
          doubleDropNodeEquiv_origin]
      cases nodeData :
          (doubleDropTarget source left right leftEligible rightEligible
            different).val.nodes endpoint.1.node with
      | atom => simp [nodeExact, nodeData]
      | ref => simp [nodeExact, nodeData]
      | identity region signature arity =>
          simp [ConcreteDiagram.requiredPorts, nodeData] at required
          obtain ⟨index, _, exact⟩ := required
          simp [nodeExact, nodeData]
          exact ⟨index, exact.symm⟩

/-- Deleting two distinct Rule-1 candidates commutes up to the concrete
isomorphism induced by their shared original node, wire, and endpoint
origins. -/
noncomputable def doubleDropCandidateIso
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (leftEligible : DropEligibility source left)
    (rightEligible : DropEligibility source right)
    (different : right ≠ left) :
    ConcreteIso
      (doubleDropTarget source left right leftEligible rightEligible
        different).val
      (doubleDropTarget source right left rightEligible leftEligible
        (fun same => different same.symm)).val :=
  ConcreteIso.ofEquivs
    (doubleDropRegionEquiv source left right leftEligible rightEligible
      different)
    (doubleDropNodeEquiv source left right leftEligible rightEligible
      different)
    (doubleDropWireEquiv source left right leftEligible rightEligible
      different)
    (by apply Fin.ext; rfl)
    (by
      intro region
      change source.val.regions _ =
        (source.val.regions region).rename _
      have regionExact :
          doubleDropRegionEquiv source left right leftEligible rightEligible
            different region = region := by
        apply Fin.ext
        rfl
      rw [regionExact]
      cases data : source.val.regions region with
      | sheet => simp only [CRegion.rename]
      | cut parent =>
          simp only [CRegion.rename]
          congr)
    (by
      intro node
      rw [doubleDrop_node_source, doubleDrop_node_source,
        doubleDropNodeEquiv_origin]
      cases data : source.val.nodes
          (doubleDropOriginNode source left right leftEligible rightEligible
            different node) <;>
        simp only [CNode.rename] <;>
        congr 1 <;>
        apply Fin.ext <;>
        rfl)
    (by
      intro wire
      change
        (source.val.wires
          (doubleDropSourceWire source right left rightEligible leftEligible
            (fun same => different same.symm)
            (doubleDropWireEquiv source left right leftEligible rightEligible
              different wire))).sig =
        (source.val.wires
          (doubleDropSourceWire source left right leftEligible rightEligible
            different wire)).sig
      rw [doubleDropSourceWire_map])
    (by
      intro wire
      change
        (source.val.wires
          (doubleDropSourceWire source right left rightEligible leftEligible
            (fun same => different same.symm)
            (doubleDropWireEquiv source left right leftEligible rightEligible
              different wire))).scope =
        doubleDropRegionEquiv source left right leftEligible rightEligible
          different
          (source.val.wires
            (doubleDropSourceWire source left right leftEligible rightEligible
              different wire)).scope
      rw [doubleDropSourceWire_map]
      apply Fin.ext
      rfl)
    (doubleDropEndpointFiber source left right leftEligible rightEligible
      different)

/-- A paired Rule-1 rewrite constructs its target isomorphism directly
from the retained carrier tables and restricted endpoint fibers. -/
def transportDropCandidate
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    ConcreteIso
      (dropCandidate left removed eligible)
      (dropCandidate right (iso.nodes removed)
        (transportDropEligibility iso eligible)) :=
  ConcreteIso.ofEquivs
    (dropRegionEquiv iso removed eligible)
    (dropNodeEquiv iso removed eligible)
    (dropWireEquiv iso removed eligible)
    (drop_root iso removed eligible)
    (drop_region_table iso removed eligible)
    (drop_node_table iso removed eligible)
    (drop_wire_signature iso removed eligible)
    (drop_wire_scope iso removed eligible)
    (dropEndpointFiber iso removed eligible)

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
