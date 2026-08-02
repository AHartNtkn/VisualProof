import VisualProof.Diagram.Concrete.DenseIdentityNormalization

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace DenseIdentityNormalization

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

private theorem drop_nodeCount_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    (dropCandidate left removed eligible).nodeCount =
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount := by
  simpa [dropCandidate, eraseNodeCandidate] using
    congrArg List.length (map_retainedNodes_singleton dense removed)

private theorem drop_regionCount_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    (dropCandidate left removed eligible).regionCount =
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).regionCount := by
  simpa [dropCandidate, eraseNodeCandidate] using dense.iso.regionCount_eq

private theorem drop_wireCount_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    (dropCandidate left removed eligible).wireCount =
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).wireCount := by
  simpa [dropCandidate, eraseNodeCandidate, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange] using dense.iso.wireCount_eq

private def dropRegionEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :=
  DenseConcreteIso.finEquivOfEq
    (drop_regionCount_eq dense removed eligible)

private def dropNodeEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :=
  DenseConcreteIso.finEquivOfEq (drop_nodeCount_eq dense removed eligible)

private def dropWireEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :=
  DenseConcreteIso.finEquivOfEq (drop_wireCount_eq dense removed eligible)

private theorem dropRegionEquiv_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (region : (dropCandidate left removed eligible).RegionId) :
    dropRegionEquiv dense removed eligible region =
      dense.iso.regions
        ⟨region.val, by
          simpa [dropCandidate, eraseNodeCandidate] using region.isLt⟩ := by
  apply Fin.ext
  calc
    (dropRegionEquiv dense removed eligible region).val = region.val :=
      DenseConcreteIso.finEquivOfEq_val _ _
    _ = (dense.iso.regions
        ⟨region.val, by
          simpa [dropCandidate, eraseNodeCandidate] using region.isLt⟩).val :=
      (dense.region_val _).symm

private theorem dropSourceNode_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (node : (dropCandidate left removed eligible).NodeId) :
    dropSourceNode right (dense.iso.nodes removed)
        (dropNodeEquiv dense removed eligible node) =
      dense.iso.nodes (dropSourceNode left removed node) := by
  have mapped := map_retainedNodes_singleton dense removed
  have positioned :
      ((retainedNodes left.val [removed]).map dense.iso.nodes).get
          (Fin.cast (by simp [dropCandidate, eraseNodeCandidate]) node) =
        dense.iso.nodes
          ((retainedNodes left.val [removed]).get node) := by simp
  let mappedIndex : Fin
      ((retainedNodes left.val [removed]).map dense.iso.nodes).length :=
    Fin.cast (by simp [dropCandidate, eraseNodeCandidate]) node
  have mappedGet := List.get_of_eq mapped mappedIndex
  let targetIndex : Fin
      (retainedNodes right.val [dense.iso.nodes removed]).length :=
    ⟨mappedIndex.val, by
      have lengths := congrArg List.length mapped
      have bound := mappedIndex.isLt
      omega⟩
  unfold dropSourceNode
  calc
    (retainedNodes right.val [dense.iso.nodes removed]).get
        (dropNodeEquiv dense removed eligible node) =
      (retainedNodes right.val [dense.iso.nodes removed]).get
        targetIndex := by
        apply congrArg
          (fun index =>
            (retainedNodes right.val [dense.iso.nodes removed]).get index)
        apply Fin.ext
        exact (DenseConcreteIso.finEquivOfEq_val _ node).trans
          (by simp [targetIndex, mappedIndex])
    _ = ((retainedNodes left.val [removed]).map dense.iso.nodes).get
        mappedIndex := by simpa [targetIndex] using mappedGet.symm
    _ = dense.iso.nodes
        ((retainedNodes left.val [removed]).get node) := by
      simpa [mappedIndex] using positioned

private theorem dropSourceWire_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    right.val.wiresList.get (dropWireEquiv dense removed eligible wire) =
      dense.iso.wires (left.val.wiresList.get wire) := by
  apply Fin.ext
  calc
    (right.val.wiresList.get
      (dropWireEquiv dense removed eligible wire)).val =
        (dropWireEquiv dense removed eligible wire).val := by
      simp [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]
    _ = wire.val := DenseConcreteIso.finEquivOfEq_val _ _
    _ = (left.val.wiresList.get wire).val := by
        simp [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]
    _ = (dense.iso.wires (left.val.wiresList.get wire)).val :=
      (dense.wire_val _).symm

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
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount) :
    CEndpoint
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount :=
  let sourceEndpoint := dropSourceEndpoint left removed endpoint
  let mapped := dense.iso.endpointMap
    (dropLeftWire left removed eligible wire) sourceEndpoint
  ⟨dropNodeEquiv dense removed eligible endpoint.node, mapped.port⟩

private def dropInverseEndpoint
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount) :
    CEndpoint (dropCandidate left removed eligible).nodeCount :=
  let targetEndpoint := dropSourceEndpoint right
    (dense.iso.nodes removed) endpoint
  let mapped := dense.iso.endpointInverse
    (dropLeftWire left removed eligible wire) targetEndpoint
  ⟨(dropNodeEquiv dense removed eligible).symm endpoint.node, mapped.port⟩

private theorem dropMapEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropSourceEndpoint right (dense.iso.nodes removed)
        (dropMapEndpoint dense removed eligible wire endpoint) =
      dense.iso.endpointMap (dropLeftWire left removed eligible wire)
        (dropSourceEndpoint left removed endpoint) := by
  apply endpoint_eq
  · change dropSourceNode right (dense.iso.nodes removed)
        (dropNodeEquiv dense removed eligible endpoint.node) = _
    rw [dropSourceNode_map dense removed eligible endpoint.node]
    exact (dense.iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint)
      ((dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
        member)).1.symm
  · rfl

private theorem dropMapEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropMapEndpoint dense removed eligible wire endpoint ∈
      ((dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).wires
          (dropWireEquiv dense removed eligible wire)).endpoints := by
  apply (dropCandidate_endpoint_mem_iff right (dense.iso.nodes removed)
    (transportDropEligibility dense eligible)
    (dropWireEquiv dense removed eligible wire)
    (dropMapEndpoint dense removed eligible wire endpoint)).mpr
  rw [dropMapEndpoint_source dense removed eligible wire endpoint member]
  rw [dropSourceWire_map dense removed eligible wire]
  exact dense.iso.endpointMap_mem (dropLeftWire left removed eligible wire)
    (dropSourceEndpoint left removed endpoint)
    ((dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
      member)

private theorem dropInverseEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).wires
          (dropWireEquiv dense removed eligible wire)).endpoints) :
    dropSourceEndpoint left removed
        (dropInverseEndpoint dense removed eligible wire endpoint) =
      dense.iso.endpointInverse (dropLeftWire left removed eligible wire)
        (dropSourceEndpoint right (dense.iso.nodes removed) endpoint) := by
  apply endpoint_eq
  · have targetMember :=
      (dropCandidate_endpoint_mem_iff right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)
        (dropWireEquiv dense removed eligible wire) endpoint).mp member
    rw [dropSourceWire_map dense removed eligible wire] at targetMember
    let sourceEndpoint := dense.iso.endpointInverse
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (dense.iso.nodes removed) endpoint)
    have sourceMember := dense.iso.endpointInverse_mem
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (dense.iso.nodes removed) endpoint) targetMember
    have corresponds := dense.iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire) sourceEndpoint sourceMember
    rw [dense.iso.endpointMap_right_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (dense.iso.nodes removed) endpoint)
      targetMember] at corresponds
    have mappedSource := dropSourceNode_map dense removed eligible
      ((dropNodeEquiv dense removed eligible).symm endpoint.node)
    rw [Data.Finite.FiniteEquiv.apply_symm_apply] at mappedSource
    change dropSourceNode left removed
      ((dropNodeEquiv dense removed eligible).symm endpoint.node) =
        sourceEndpoint.node
    exact dense.iso.nodes.injective
      (mappedSource.symm.trans corresponds.1)
  · rfl

private theorem dropInverseEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).wires
          (dropWireEquiv dense removed eligible wire)).endpoints) :
    dropInverseEndpoint dense removed eligible wire endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints := by
  apply (dropCandidate_endpoint_mem_iff left removed eligible wire
    (dropInverseEndpoint dense removed eligible wire endpoint)).mpr
  rw [dropInverseEndpoint_source dense removed eligible wire endpoint member]
  have targetMember :=
    (dropCandidate_endpoint_mem_iff right (dense.iso.nodes removed)
      (transportDropEligibility dense eligible)
      (dropWireEquiv dense removed eligible wire) endpoint).mp member
  rw [dropSourceWire_map dense removed eligible wire] at targetMember
  exact dense.iso.endpointInverse_mem (dropLeftWire left removed eligible wire)
    (dropSourceEndpoint right (dense.iso.nodes removed) endpoint) targetMember

private theorem dropInverse_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint (dropCandidate left removed eligible).nodeCount)
    (member : endpoint ∈
      ((dropCandidate left removed eligible).wires wire).endpoints) :
    dropInverseEndpoint dense removed eligible wire
        (dropMapEndpoint dense removed eligible wire endpoint) = endpoint := by
  apply endpoint_eq
  · exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
  · have sourceMember :=
      (dropCandidate_endpoint_mem_iff left removed eligible wire endpoint).mp
        member
    have sourceExact := dropMapEndpoint_source dense removed eligible wire
      endpoint member
    change (dense.iso.endpointInverse
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (dense.iso.nodes removed)
        (dropMapEndpoint dense removed eligible wire endpoint))).port =
      endpoint.port
    rw [sourceExact]
    rw [dense.iso.endpointMap_left_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint) sourceMember]
    rfl

private theorem dropMap_inverse
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId)
    (endpoint : CEndpoint
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).nodeCount)
    (member : endpoint ∈
      ((dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).wires
          (dropWireEquiv dense removed eligible wire)).endpoints) :
    dropMapEndpoint dense removed eligible wire
        (dropInverseEndpoint dense removed eligible wire endpoint) = endpoint := by
  apply endpoint_eq
  · exact Data.Finite.FiniteEquiv.apply_symm_apply _ _
  · have targetMember :=
      (dropCandidate_endpoint_mem_iff right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)
        (dropWireEquiv dense removed eligible wire) endpoint).mp member
    rw [dropSourceWire_map dense removed eligible wire] at targetMember
    have sourceExact := dropInverseEndpoint_source dense removed eligible wire
      endpoint member
    change (dense.iso.endpointMap
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed
        (dropInverseEndpoint dense removed eligible wire endpoint))).port =
      endpoint.port
    rw [sourceExact]
    rw [dense.iso.endpointMap_right_inv
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint right (dense.iso.nodes removed) endpoint)
      targetMember]
    rfl

private def dropEndpointFiber
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ConcreteIso.EndpointFiberEquiv
      (dropNodeEquiv dense removed eligible)
      (dropWireEquiv dense removed eligible) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨dropMapEndpoint dense removed eligible wire endpoint.1,
          dropMapEndpoint_mem dense removed eligible wire endpoint.1
            endpoint.2⟩
      invFun := fun endpoint =>
        ⟨dropInverseEndpoint dense removed eligible wire endpoint.1,
          dropInverseEndpoint_mem dense removed eligible wire endpoint.1
            endpoint.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact dropInverse_map dense removed eligible wire endpoint.1 endpoint.2
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact dropMap_inverse dense removed eligible wire endpoint.1 endpoint.2 }
  corresponds := by
    intro endpoint
    have sourceMember :=
      (dropCandidate_endpoint_mem_iff left removed eligible wire endpoint.1).mp
        endpoint.2
    have original := dense.iso.endpointMap_corresponds
      (dropLeftWire left removed eligible wire)
      (dropSourceEndpoint left removed endpoint.1) sourceMember
    change PortCorresponds
      (dropCandidate left removed eligible)
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible))
      (dropNodeEquiv dense removed eligible) endpoint.1
      (dropMapEndpoint dense removed eligible wire endpoint.1)
    unfold PortCorresponds at original ⊢
    have originalPort := original.2
    rw [original.1] at originalPort
    constructor
    · rfl
    · have sourceNodeMap := dropSourceNode_map dense removed eligible
        endpoint.1.node
      rw [show (dropMapEndpoint dense removed eligible wire endpoint.1).node =
        dropNodeEquiv dense removed eligible endpoint.1.node by rfl]
      rw [dropCandidate_node_source, dropCandidate_node_source]
      rw [sourceNodeMap]
      have nodeTable := dense.iso.node_table
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
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    dropRegionEquiv dense removed eligible
        (dropCandidate left removed eligible).root =
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)).root := by
  apply Fin.ext
  calc
    (dropRegionEquiv dense removed eligible
      (dropCandidate left removed eligible).root).val =
        left.val.root.val := DenseConcreteIso.finEquivOfEq_val _ _
    _ = (dense.iso.regions left.val.root).val :=
      (dense.region_val left.val.root).symm
    _ = right.val.root.val := congrArg Fin.val dense.iso.root

private theorem drop_region_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (region : (dropCandidate left removed eligible).RegionId) :
    (dropCandidate right (dense.iso.nodes removed)
      (transportDropEligibility dense eligible)).regions
        (dropRegionEquiv dense removed eligible region) =
      ((dropCandidate left removed eligible).regions region).rename
        (dropRegionEquiv dense removed eligible) := by
  let sourceRegion : left.val.RegionId :=
    ⟨region.val, by
      simpa [dropCandidate, eraseNodeCandidate] using region.isLt⟩
  change right.val.regions (dropRegionEquiv dense removed eligible region) =
    (left.val.regions sourceRegion).rename
      (dropRegionEquiv dense removed eligible)
  rw [dropRegionEquiv_eq dense removed eligible region]
  rw [dense.iso.region_table sourceRegion]
  cases data : left.val.regions sourceRegion with
  | sheet => rfl
  | cut parent =>
      simp only [CRegion.rename]
      apply congrArg CRegion.cut
      apply Fin.ext
      calc
        (dense.iso.regions parent).val = parent.val := dense.region_val parent
        _ = (dropRegionEquiv dense removed eligible
          ⟨parent.val, by
            simpa [dropCandidate, eraseNodeCandidate] using parent.isLt⟩).val :=
          (DenseConcreteIso.finEquivOfEq_val _ _).symm

private theorem drop_node_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (node : (dropCandidate left removed eligible).NodeId) :
    (dropCandidate right (dense.iso.nodes removed)
      (transportDropEligibility dense eligible)).nodes
        (dropNodeEquiv dense removed eligible node) =
      ((dropCandidate left removed eligible).nodes node).rename
        (dropRegionEquiv dense removed eligible) := by
  rw [dropCandidate_node_source, dropCandidate_node_source]
  rw [dropSourceNode_map dense removed eligible node]
  rw [dense.iso.node_table]
  have regionExact (region : left.val.RegionId) :
      dense.iso.regions region =
        dropRegionEquiv dense removed eligible
          ⟨region.val, by
            simpa [dropCandidate, eraseNodeCandidate] using region.isLt⟩ := by
    apply Fin.ext
    exact (dense.region_val region).trans
      (DenseConcreteIso.finEquivOfEq_val _ _).symm
  cases data : left.val.nodes (dropSourceNode left removed node) with
  | atom region arguments =>
      simp only [CNode.rename]
      exact congrArg (fun target => CNode.atom target arguments)
        (regionExact region)
  | ref region definition arguments =>
      simp only [CNode.rename]
      exact congrArg (fun target => CNode.ref target definition arguments)
        (regionExact region)
  | identity region signature arity =>
      simp only [CNode.rename]
      exact congrArg (fun target => CNode.identity target signature arity)
        (regionExact region)

private theorem drop_wire_signature
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ((dropCandidate right (dense.iso.nodes removed)
      (transportDropEligibility dense eligible)).wires
        (dropWireEquiv dense removed eligible wire)).sig =
      ((dropCandidate left removed eligible).wires wire).sig := by
  change (right.val.wires
      (right.val.wiresList.get (dropWireEquiv dense removed eligible wire))).sig =
    (left.val.wires (left.val.wiresList.get wire)).sig
  rw [dropSourceWire_map dense removed eligible wire]
  exact dense.iso.wire_signature _

private theorem drop_wire_scope
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed)
    (wire : (dropCandidate left removed eligible).WireId) :
    ((dropCandidate right (dense.iso.nodes removed)
      (transportDropEligibility dense eligible)).wires
        (dropWireEquiv dense removed eligible wire)).scope =
      dropRegionEquiv dense removed eligible
        ((dropCandidate left removed eligible).wires wire).scope := by
  let sourceWire := left.val.wiresList.get wire
  change (right.val.wires
      (right.val.wiresList.get (dropWireEquiv dense removed eligible wire))).scope = _
  rw [dropSourceWire_map dense removed eligible wire]
  rw [dense.iso.wire_scope sourceWire]
  apply Fin.ext
  calc
    (dense.iso.regions (left.val.wires sourceWire).scope).val =
        (left.val.wires sourceWire).scope.val := dense.region_val _
    _ = (dropRegionEquiv dense removed eligible
        ((dropCandidate left removed eligible).wires wire).scope).val :=
      (DenseConcreteIso.finEquivOfEq_val _ _).symm

/-- A paired Rule-1 rewrite constructs its dense target isomorphism directly
from the retained carrier tables and restricted endpoint fibers. -/
def transportDropCandidate
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (removed : left.val.NodeId)
    (eligible : DropEligibility left removed) :
    DenseConcreteIso
      (dropCandidate left removed eligible)
      (dropCandidate right (dense.iso.nodes removed)
        (transportDropEligibility dense eligible)) where
  iso := ConcreteIso.ofEquivs
    (dropRegionEquiv dense removed eligible)
    (dropNodeEquiv dense removed eligible)
    (dropWireEquiv dense removed eligible)
    (drop_root dense removed eligible)
    (drop_region_table dense removed eligible)
    (drop_node_table dense removed eligible)
    (drop_wire_signature dense removed eligible)
    (drop_wire_scope dense removed eligible)
    (dropEndpointFiber dense removed eligible)
  region_val := DenseConcreteIso.finEquivOfEq_val _
  node_val := DenseConcreteIso.finEquivOfEq_val _
  wire_val := DenseConcreteIso.finEquivOfEq_val _

end DenseIdentityNormalization

end ConcreteDiagram

end VisualProof
