import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof

open Data.Finite

namespace ConcreteIso

/--
Construction-owned correspondence between the incident endpoints of one
already-corresponding wire.  The subtype carriers make incidence and both
inverse laws structural, leaving only semantic port correspondence to prove.
-/
structure EndpointFiberEquiv
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (wires : Data.Finite.FiniteEquiv left.WireId right.WireId)
    (wire : left.WireId) where
  equivalence :
    Data.Finite.FiniteEquiv
      { endpoint // endpoint ∈ (left.wires wire).endpoints }
      { candidate //
        candidate ∈ (right.wires (wires wire)).endpoints }
  corresponds :
    ∀ endpoint,
      PortCorresponds left right nodes endpoint.1
        (equivalence endpoint).1

/--
Assemble a raw concrete isomorphism from exact identifier tables and total
per-wire endpoint fibers.  This is the non-searching construction boundary;
callers provide the correspondences their construction receipts already own.
-/
def ofEquivs
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (regions : Data.Finite.FiniteEquiv left.RegionId right.RegionId)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (wires : Data.Finite.FiniteEquiv left.WireId right.WireId)
    (root : regions left.root = right.root)
    (regionTable :
      ∀ region,
        right.regions (regions region) =
          (left.regions region).rename regions)
    (nodeTable :
      ∀ node,
        right.nodes (nodes node) =
          (left.nodes node).rename regions)
    (wireSignature :
      ∀ wire, (right.wires (wires wire)).sig = (left.wires wire).sig)
    (wireScope :
      ∀ wire,
        (right.wires (wires wire)).scope =
          regions (left.wires wire).scope)
    (endpointFibers :
      ∀ wire, EndpointFiberEquiv nodes wires wire) :
    ConcreteIso left right where
  regions := regions
  nodes := nodes
  wires := wires
  root := root
  region_table := regionTable
  node_table := nodeTable
  wire_signature := wireSignature
  wire_scope := wireScope
  endpointMap := fun wire endpoint =>
    if member : endpoint ∈ (left.wires wire).endpoints then
      (endpointFibers wire).equivalence ⟨endpoint, member⟩
    else
      ⟨nodes endpoint.node, endpoint.port⟩
  endpointInverse := fun wire candidate =>
    if member : candidate ∈ (right.wires (wires wire)).endpoints then
      (endpointFibers wire).equivalence.symm ⟨candidate, member⟩
    else
      ⟨nodes.symm candidate.node, candidate.port⟩
  endpointMap_mem := by
    intro wire endpoint member
    simp only [dif_pos member]
    exact ((endpointFibers wire).equivalence ⟨endpoint, member⟩).2
  endpointInverse_mem := by
    intro wire candidate member
    simp only [dif_pos member]
    exact
      ((endpointFibers wire).equivalence.symm ⟨candidate, member⟩).2
  endpointMap_left_inv := by
    intro wire endpoint member
    simp only [dif_pos member]
    rw [dif_pos
      ((endpointFibers wire).equivalence ⟨endpoint, member⟩).2]
    exact congrArg Subtype.val
      ((endpointFibers wire).equivalence.left_inv ⟨endpoint, member⟩)
  endpointMap_right_inv := by
    intro wire candidate member
    simp only [dif_pos member]
    rw [dif_pos
      ((endpointFibers wire).equivalence.symm ⟨candidate, member⟩).2]
    exact congrArg Subtype.val
      ((endpointFibers wire).equivalence.right_inv ⟨candidate, member⟩)
  endpointMap_corresponds := by
    intro wire endpoint member
    simp only [dif_pos member]
    exact (endpointFibers wire).corresponds ⟨endpoint, member⟩

private theorem portCorresponds_symm
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {endpoint : CEndpoint left.nodeCount}
    {candidate : CEndpoint right.nodeCount}
    (corresponds : PortCorresponds left right iso.nodes endpoint candidate) :
    PortCorresponds right left iso.nodes.symm candidate endpoint := by
  unfold PortCorresponds at corresponds ⊢
  have nodeEquality : endpoint.node = iso.nodes.symm candidate.node :=
    (iso.nodes.left_inv endpoint.node).symm.trans
      (congrArg iso.nodes.symm corresponds.1.symm)
  refine ⟨nodeEquality, ?_⟩
  cases leftNode : left.nodes endpoint.node <;>
    cases rightNode : right.nodes candidate.node <;>
    simp [leftNode, rightNode] at corresponds ⊢
  all_goals try exact corresponds.2.symm
  exact ⟨corresponds.2.1.symm, corresponds.2.2.1.symm,
    corresponds.2.2.2.2, corresponds.2.2.2.1⟩

theorem regionCount_eq
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) :
    left.regionCount = right.regionCount := by
  apply Nat.le_antisymm
  · exact Data.Finite.fin_card_le_of_injective iso.regions
      iso.regions.injective
  · exact Data.Finite.fin_card_le_of_injective iso.regions.invFun
      (by
        intro first second equality
        have := congrArg iso.regions.toFun equality
        simpa only [iso.regions.right_inv] using this)

theorem nodeCount_eq
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) :
    left.nodeCount = right.nodeCount := by
  apply Nat.le_antisymm
  · exact Data.Finite.fin_card_le_of_injective iso.nodes iso.nodes.injective
  · exact Data.Finite.fin_card_le_of_injective iso.nodes.invFun
      (by
        intro first second equality
        have := congrArg iso.nodes.toFun equality
        simpa only [iso.nodes.right_inv] using this)

theorem wireCount_eq
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) :
    left.wireCount = right.wireCount := by
  apply Nat.le_antisymm
  · exact Data.Finite.fin_card_le_of_injective iso.wires iso.wires.injective
  · exact Data.Finite.fin_card_le_of_injective iso.wires.invFun
      (by
        intro first second equality
        have := congrArg iso.wires.toFun equality
        simpa only [iso.wires.right_inv] using this)

theorem target_region
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) (region : right.RegionId) :
    right.regions region =
      (left.regions (iso.regions.symm region)).rename iso.regions := by
  calc
    right.regions region =
        right.regions (iso.regions (iso.regions.symm region)) :=
      congrArg right.regions (iso.regions.right_inv region).symm
    _ = (left.regions (iso.regions.symm region)).rename iso.regions :=
      iso.region_table _

theorem target_node
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) (node : right.NodeId) :
    right.nodes node =
      (left.nodes (iso.nodes.symm node)).rename iso.regions := by
  calc
    right.nodes node = right.nodes (iso.nodes (iso.nodes.symm node)) :=
      congrArg right.nodes (iso.nodes.right_inv node).symm
    _ = (left.nodes (iso.nodes.symm node)).rename iso.regions :=
      iso.node_table _

theorem endpoint_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (wire : left.WireId) (endpoint : CEndpoint left.nodeCount)
    (member : endpoint ∈ (left.wires wire).endpoints) :
    ∃ candidate,
      candidate ∈ (right.wires (iso.wires wire)).endpoints ∧
        PortCorresponds left right iso.nodes endpoint candidate :=
  ⟨iso.endpointMap wire endpoint, iso.endpointMap_mem wire endpoint member,
    iso.endpointMap_corresponds wire endpoint member⟩

theorem endpoint_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (wire : left.WireId) (candidate : CEndpoint right.nodeCount)
    (member : candidate ∈ (right.wires (iso.wires wire)).endpoints) :
    ∃ endpoint,
      endpoint ∈ (left.wires wire).endpoints ∧
        PortCorresponds left right iso.nodes endpoint candidate := by
  let endpoint := iso.endpointInverse wire candidate
  have endpointMember := iso.endpointInverse_mem wire candidate member
  refine ⟨endpoint, endpointMember, ?_⟩
  have corresponds := iso.endpointMap_corresponds wire endpoint endpointMember
  rw [iso.endpointMap_right_inv wire candidate member] at corresponds
  exact corresponds

def symm
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) :
    ConcreteIso right left where
  regions := iso.regions.symm
  nodes := iso.nodes.symm
  wires := iso.wires.symm
  root := (congrArg iso.regions.symm iso.root.symm).trans
    (iso.regions.left_inv left.root)
  region_table := by
    intro region
    have target := iso.target_region region
    cases sourceData : left.regions (iso.regions.symm region) with
    | sheet =>
        rw [sourceData] at target
        rw [target]
        rfl
    | cut parent =>
        rw [sourceData] at target
        rw [target]
        simp [CRegion.rename]
  node_table := by
    intro node
    have target := iso.target_node node
    cases sourceData : left.nodes (iso.nodes.symm node) with
    | atom region args =>
        rw [sourceData] at target
        rw [target]
        simp [CNode.rename]
    | ref region definition args =>
        rw [sourceData] at target
        rw [target]
        simp [CNode.rename]
    | identity region sig arity =>
        rw [sourceData] at target
        rw [target]
        simp [CNode.rename]
  wire_signature := by
    intro wire
    calc
      (left.wires (iso.wires.symm wire)).sig =
          (right.wires (iso.wires (iso.wires.symm wire))).sig :=
        (iso.wire_signature (iso.wires.symm wire)).symm
      _ = (right.wires wire).sig :=
        congrArg (fun target => (right.wires target).sig)
          (iso.wires.right_inv wire)
  wire_scope := by
    intro wire
    calc
      (left.wires (iso.wires.symm wire)).scope =
          iso.regions.symm
            (iso.regions (left.wires (iso.wires.symm wire)).scope) :=
        (iso.regions.left_inv _).symm
      _ = iso.regions.symm
          (right.wires (iso.wires (iso.wires.symm wire))).scope :=
        congrArg iso.regions.symm
          (iso.wire_scope (iso.wires.symm wire)).symm
      _ = iso.regions.symm (right.wires wire).scope :=
        congrArg (fun target =>
          iso.regions.symm (right.wires target).scope)
          (iso.wires.right_inv wire)
  endpointMap := fun wire candidate =>
    iso.endpointInverse (iso.wires.symm wire) candidate
  endpointInverse := fun wire endpoint =>
    iso.endpointMap (iso.wires.symm wire) endpoint
  endpointMap_mem := by
    intro wire candidate member
    have mappedMember : candidate ∈
        (right.wires (iso.wires (iso.wires.symm wire))).endpoints := by
      exact Eq.mp (congrArg
        (fun target => candidate ∈ (right.wires target).endpoints)
        (iso.wires.right_inv wire).symm) member
    exact iso.endpointInverse_mem (iso.wires.symm wire) candidate
      mappedMember
  endpointInverse_mem := by
    intro wire endpoint member
    have candidateMember := iso.endpointMap_mem
      (iso.wires.symm wire) endpoint member
    have wireEquality : iso.wires (iso.wires.symm wire) = wire :=
      iso.wires.right_inv wire
    rw [wireEquality] at candidateMember
    exact candidateMember
  endpointMap_left_inv := by
    intro wire candidate member
    have mappedMember : candidate ∈
        (right.wires (iso.wires (iso.wires.symm wire))).endpoints := by
      exact Eq.mp (congrArg
        (fun target => candidate ∈ (right.wires target).endpoints)
        (iso.wires.right_inv wire).symm) member
    exact iso.endpointMap_right_inv (iso.wires.symm wire) candidate
      mappedMember
  endpointMap_right_inv := by
    intro wire endpoint member
    exact iso.endpointMap_left_inv (iso.wires.symm wire) endpoint member
  endpointMap_corresponds := by
    intro wire candidate member
    have mappedMember : candidate ∈
        (right.wires (iso.wires (iso.wires.symm wire))).endpoints := by
      exact Eq.mp (congrArg
        (fun target => candidate ∈ (right.wires target).endpoints)
        (iso.wires.right_inv wire).symm) member
    let endpoint := iso.endpointInverse (iso.wires.symm wire) candidate
    have endpointMember := iso.endpointInverse_mem
      (iso.wires.symm wire) candidate mappedMember
    have corresponds := iso.endpointMap_corresponds
      (iso.wires.symm wire) endpoint endpointMember
    rw [iso.endpointMap_right_inv (iso.wires.symm wire) candidate
      mappedMember] at corresponds
    exact portCorresponds_symm iso corresponds

private theorem portCorresponds_trans
    {definitions : List (List Sig)}
    {first second third : ConcreteDiagram definitions.length}
    (left : ConcreteIso first second)
    (right : ConcreteIso second third)
    {source : CEndpoint first.nodeCount}
    {middle : CEndpoint second.nodeCount}
    {target : CEndpoint third.nodeCount}
    (sourceMiddle :
      PortCorresponds first second left.nodes source middle)
    (middleTarget :
      PortCorresponds second third right.nodes middle target) :
    PortCorresponds first third (left.nodes.trans right.nodes)
      source target := by
  rcases source with ⟨sourceNode, sourcePort⟩
  rcases middle with ⟨middleNode, middlePort⟩
  rcases target with ⟨targetNode, targetPort⟩
  have sourceNodeExact := sourceMiddle.1
  change middleNode = left.nodes sourceNode at sourceNodeExact
  subst middleNode
  have middleNodeExact := middleTarget.1
  change targetNode = right.nodes (left.nodes sourceNode) at middleNodeExact
  subst targetNode
  refine ⟨rfl, ?_⟩
  have secondData := left.node_table sourceNode
  have thirdData := right.node_table (left.nodes sourceNode)
  unfold PortCorresponds at sourceMiddle middleTarget
  cases firstNode : first.nodes sourceNode with
  | atom region arguments =>
      rw [firstNode] at secondData
      rw [secondData] at thirdData
      simp [firstNode, secondData, thirdData] at sourceMiddle middleTarget ⊢
      exact middleTarget.trans sourceMiddle
  | ref region definition arguments =>
      rw [firstNode] at secondData
      rw [secondData] at thirdData
      simp [firstNode, secondData, thirdData] at sourceMiddle middleTarget ⊢
      exact middleTarget.trans sourceMiddle
  | identity region signature arity =>
      rw [firstNode] at secondData
      rw [secondData] at thirdData
      simp [firstNode, secondData, thirdData] at sourceMiddle middleTarget ⊢
      exact ⟨sourceMiddle.1, sourceMiddle.2.1,
        sourceMiddle.2.2.1, middleTarget.2.2.2⟩

/-- Compose two proved concrete isomorphisms directly.  The carrier maps and
endpoint bijections compose definitionally; no checker or map discovery is
involved. -/
def trans
    {definitions : List (List Sig)}
    {first second third : ConcreteDiagram definitions.length}
    (left : ConcreteIso first second)
    (right : ConcreteIso second third) :
    ConcreteIso first third where
  regions := left.regions.trans right.regions
  nodes := left.nodes.trans right.nodes
  wires := left.wires.trans right.wires
  root := by
    change right.regions (left.regions first.root) = third.root
    rw [left.root, right.root]
  region_table := by
    intro region
    change third.regions (right.regions (left.regions region)) = _
    rw [right.region_table, left.region_table]
    cases first.regions region <;> rfl
  node_table := by
    intro node
    change third.nodes (right.nodes (left.nodes node)) = _
    rw [right.node_table, left.node_table]
    cases first.nodes node <;> rfl
  wire_signature := by
    intro wire
    change (third.wires (right.wires (left.wires wire))).sig = _
    rw [right.wire_signature, left.wire_signature]
  wire_scope := by
    intro wire
    change (third.wires (right.wires (left.wires wire))).scope = _
    rw [right.wire_scope, left.wire_scope]
    rfl
  endpointMap := fun wire endpoint =>
    right.endpointMap (left.wires wire) (left.endpointMap wire endpoint)
  endpointInverse := fun wire endpoint =>
    left.endpointInverse wire
      (right.endpointInverse (left.wires wire) endpoint)
  endpointMap_mem := by
    intro wire endpoint member
    exact right.endpointMap_mem (left.wires wire)
      (left.endpointMap wire endpoint)
      (left.endpointMap_mem wire endpoint member)
  endpointInverse_mem := by
    intro wire endpoint member
    exact left.endpointInverse_mem wire
      (right.endpointInverse (left.wires wire) endpoint)
      (right.endpointInverse_mem (left.wires wire) endpoint member)
  endpointMap_left_inv := by
    intro wire endpoint member
    rw [right.endpointMap_left_inv (left.wires wire)
      (left.endpointMap wire endpoint)
      (left.endpointMap_mem wire endpoint member)]
    exact left.endpointMap_left_inv wire endpoint member
  endpointMap_right_inv := by
    intro wire endpoint member
    rw [left.endpointMap_right_inv wire
      (right.endpointInverse (left.wires wire) endpoint)
      (right.endpointInverse_mem (left.wires wire) endpoint member)]
    exact right.endpointMap_right_inv (left.wires wire) endpoint member
  endpointMap_corresponds := by
    intro wire endpoint member
    apply portCorresponds_trans left right
    · exact left.endpointMap_corresponds wire endpoint member
    · exact right.endpointMap_corresponds (left.wires wire)
        (left.endpointMap wire endpoint)
        (left.endpointMap_mem wire endpoint member)

/-- Transport one endpoint occurrence through the constructive equivalence
owned by an explicitly supplied isomorphism. -/
def transportEndpointOnWire
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (wire : left.WireId)
    (endpoint : CEndpoint left.nodeCount)
    (_member : endpoint ∈ (left.wires wire).endpoints) :
    CEndpoint right.nodeCount :=
  iso.endpointMap wire endpoint

@[simp] theorem transportEndpointOnWire_mem
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (wire : left.WireId)
    (endpoint : CEndpoint left.nodeCount)
    (member : endpoint ∈ (left.wires wire).endpoints) :
    iso.transportEndpointOnWire wire endpoint member ∈
      (right.wires (iso.wires wire)).endpoints :=
  iso.endpointMap_mem wire endpoint member

/-- Transport an ordered endpoint selection totally. The membership premise
selects occurrences from the named source wire; list mapping preserves order
and multiplicity. -/
def transportEndpointsOnWire
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (wire : left.WireId)
    (endpoints : List (CEndpoint left.nodeCount))
    (members : ∀ endpoint, endpoint ∈ endpoints →
      endpoint ∈ (left.wires wire).endpoints) :
    List (CEndpoint right.nodeCount) :=
  endpoints.attach.map fun endpoint =>
    iso.transportEndpointOnWire wire endpoint.val
      (members endpoint.val endpoint.property)

theorem node_region
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) (node : left.NodeId) :
    (right.nodes (iso.nodes node)).region =
      iso.regions (left.nodes node).region := by
  rw [iso.node_table]
  exact CNode.region_rename _ _

theorem climb_transport
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) (steps : Nat)
    (region : left.RegionId) :
    right.climb steps (iso.regions region) =
      (left.climb steps region).map iso.regions := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [ConcreteDiagram.climb]
      rw [iso.region_table]
      cases data : left.regions region with
      | sheet => rfl
      | cut parent =>
          simp only [CRegion.rename]
          exact ih parent

theorem encloses_transport
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {ancestor descendant : left.RegionId}
    (encloses : left.Encloses ancestor descendant) :
    right.Encloses (iso.regions ancestor) (iso.regions descendant) := by
  unfold ConcreteDiagram.Encloses at encloses ⊢
  rw [List.any_eq_true] at encloses ⊢
  obtain ⟨steps, _, climbed⟩ := encloses
  let targetSteps : Fin (right.regionCount + 1) :=
    Fin.cast (congrArg (fun count => count + 1) iso.regionCount_eq) steps
  refine ⟨targetSteps, Data.Finite.mem_allFin targetSteps, ?_⟩
  change (right.climb steps.val (iso.regions descendant) ==
    some (iso.regions ancestor)) = true
  rw [iso.climb_transport, eq_of_beq climbed]
  simp

theorem wiresAt_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region : left.RegionId} {wire : left.WireId}
    (member : wire ∈ left.wiresAt region) :
    iso.wires wire ∈ right.wiresAt (iso.regions region) := by
  rw [ConcreteDiagram.wiresAt, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  have scope := iso.wire_scope wire
  have leftScope := eq_of_beq member
  apply beq_iff_eq.mpr
  exact scope.trans (congrArg iso.regions leftScope)

theorem wiresAt_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region : right.RegionId} {wire : right.WireId}
    (member : wire ∈ right.wiresAt region) :
    iso.wires.symm wire ∈ left.wiresAt (iso.regions.symm region) := by
  rw [ConcreteDiagram.wiresAt, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  apply beq_iff_eq.mpr
  have scope := iso.wire_scope (iso.wires.symm wire)
  have targetScope := eq_of_beq member
  have mapped :
      iso.regions (left.wires (iso.wires.symm wire)).scope = region := by
    calc
      iso.regions (left.wires (iso.wires.symm wire)).scope =
          (right.wires (iso.wires (iso.wires.symm wire))).scope :=
        scope.symm
      _ = (right.wires wire).scope :=
        congrArg (fun targetWire => (right.wires targetWire).scope)
          (iso.wires.right_inv wire)
      _ = region := targetScope
  have pulled := congrArg iso.regions.invFun mapped
  simpa only [iso.regions.left_inv] using pulled

theorem nodesAt_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region : left.RegionId} {node : left.NodeId}
    (member : node ∈ left.nodesAt region) :
    iso.nodes node ∈ right.nodesAt (iso.regions region) := by
  rw [ConcreteDiagram.nodesAt, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  apply beq_iff_eq.mpr
  rw [iso.node_region]
  exact congrArg iso.regions (eq_of_beq member)

theorem nodesAt_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region : right.RegionId} {node : right.NodeId}
    (member : node ∈ right.nodesAt region) :
    iso.nodes.symm node ∈ left.nodesAt (iso.regions.symm region) := by
  rw [ConcreteDiagram.nodesAt, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  apply beq_iff_eq.mpr
  have mapped :
      iso.regions (left.nodes (iso.nodes.symm node)).region = region := by
    calc
      iso.regions (left.nodes (iso.nodes.symm node)).region =
          (right.nodes (iso.nodes (iso.nodes.symm node))).region :=
        (iso.node_region (iso.nodes.symm node)).symm
      _ = (right.nodes node).region :=
        congrArg (fun targetNode => (right.nodes targetNode).region)
          (iso.nodes.right_inv node)
      _ = region := eq_of_beq member
  have pulled := congrArg iso.regions.invFun mapped
  simpa only [iso.regions.left_inv] using pulled

theorem childrenOf_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region child : left.RegionId}
    (member : child ∈ left.childrenOf region) :
    iso.regions child ∈ right.childrenOf (iso.regions region) := by
  rw [ConcreteDiagram.childrenOf, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  cases childData : left.regions child with
  | sheet => simp [childData] at member
  | cut parent =>
      simp only [childData] at member
      have parentEq : parent = region := by
        exact eq_of_beq member
      rw [iso.region_table, childData]
      simp [CRegion.rename, parentEq]

theorem childrenOf_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {region child : right.RegionId}
    (member : child ∈ right.childrenOf region) :
    iso.regions.symm child ∈ left.childrenOf (iso.regions.symm region) := by
  have targetData := iso.target_region child
  rw [ConcreteDiagram.childrenOf, List.mem_filter] at member ⊢
  rcases member with ⟨_, member⟩
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  cases sourceData : left.regions (iso.regions.symm child) with
  | sheet =>
      rw [sourceData] at targetData
      simp [targetData] at member
  | cut parent =>
      rw [sourceData] at targetData
      rw [targetData] at member
      simp only [CRegion.rename] at member
      have mappedParent : iso.regions parent = region := by
        exact eq_of_beq member
      have parentEq : parent = iso.regions.symm region := by
        have pulled := congrArg iso.regions.invFun mappedParent
        simpa only [iso.regions.left_inv] using pulled
      exact beq_iff_eq.mpr parentEq

theorem requiredPorts_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {node : left.NodeId} {port : CPort}
    (required : port ∈ left.requiredPorts node) :
    port ∈ right.requiredPorts (iso.nodes node) := by
  unfold ConcreteDiagram.requiredPorts at required ⊢
  rw [iso.node_table]
  cases nodeData : left.nodes node <;>
    simpa [nodeData, CNode.rename] using required

theorem atom_owner_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    {port : CPort} {wire : left.WireId}
    (owner : left.endpointOwner? ⟨node, port⟩ = some wire) :
    right.endpointOwner? ⟨iso.nodes node, port⟩ =
      some (iso.wires wire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident left ⟨node, port⟩ wire owner
  obtain ⟨candidate, candidateMember, corresponds⟩ :=
    iso.endpoint_forward wire ⟨node, port⟩ incident
  have nodeEquality : candidate.node = iso.nodes node :=
    corresponds.1
  have rightNode :
      right.nodes candidate.node =
        .atom (iso.regions region) args := by
    rw [corresponds.1, iso.node_table, nodeData]
    rfl
  have portEquality : candidate.port = port := by
    unfold PortCorresponds at corresponds
    rw [nodeData, rightNode] at corresponds
    exact corresponds.2
  have candidateEquality :
      candidate = (⟨iso.nodes node, port⟩ :
        CEndpoint right.nodeCount) := by
    cases candidate with
    | mk candidateNode candidatePort =>
        simp only at nodeEquality portEquality ⊢
        subst candidateNode
        subst candidatePort
        rfl
  subst candidate
  exact ConcreteDiagram.endpointOwner?_eq_of_incident definitions right
    rightWellFormed (iso.nodes node) port
    (iso.requiredPorts_forward
      (ConcreteDiagram.incident_port_required definitions left
        leftWellFormed
        wire ⟨node, port⟩ incident))
    (iso.wires wire) candidateMember

theorem atom_owner_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    {port : CPort} {targetWire : right.WireId}
    (owner : right.endpointOwner? ⟨iso.nodes node, port⟩ =
      some targetWire) :
    left.endpointOwner? ⟨node, port⟩ =
      some (iso.wires.symm targetWire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident right
      ⟨iso.nodes node, port⟩ targetWire owner
  have mappedIncident :
      (⟨iso.nodes node, port⟩ : CEndpoint right.nodeCount) ∈
        (right.wires
          (iso.wires (iso.wires.symm targetWire))).endpoints := by
    change (⟨iso.nodes node, port⟩ : CEndpoint right.nodeCount) ∈
      (right.wires
        (iso.wires (iso.wires.invFun targetWire))).endpoints
    rw [iso.wires.right_inv]
    exact incident
  obtain ⟨endpoint, endpointMember, corresponds⟩ :=
    iso.endpoint_backward (iso.wires.symm targetWire)
      ⟨iso.nodes node, port⟩ mappedIncident
  have endpointNode : endpoint.node = node := by
    apply iso.nodes.injective
    exact corresponds.1.symm
  have rightNode :
      right.nodes
          (⟨iso.nodes node, port⟩ :
            CEndpoint right.nodeCount).node =
        .atom (iso.regions region) args := by
    rw [iso.node_table, nodeData]
    rfl
  have endpointPort : endpoint.port = port := by
    unfold PortCorresponds at corresponds
    rw [endpointNode, nodeData, rightNode] at corresponds
    exact corresponds.2.symm
  have endpointEquality :
      endpoint = (⟨node, port⟩ : CEndpoint left.nodeCount) := by
    cases endpoint with
    | mk sourceNode sourcePort =>
        simp only at endpointNode endpointPort ⊢
        subst sourceNode
        subst sourcePort
        rfl
  subst endpoint
  have required :=
    ConcreteDiagram.incident_port_required definitions left
      leftWellFormed (iso.wires.symm targetWire)
      ⟨node, port⟩ endpointMember
  exact ConcreteDiagram.endpointOwner?_eq_of_incident definitions left
    leftWellFormed node port required
    (iso.wires.symm targetWire) endpointMember

theorem ref_owner_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
    {port : CPort} {wire : left.WireId}
    (owner : left.endpointOwner? ⟨node, port⟩ = some wire) :
    right.endpointOwner? ⟨iso.nodes node, port⟩ =
      some (iso.wires wire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident left ⟨node, port⟩ wire owner
  obtain ⟨candidate, candidateMember, corresponds⟩ :=
    iso.endpoint_forward wire ⟨node, port⟩ incident
  have nodeEquality : candidate.node = iso.nodes node :=
    corresponds.1
  have rightNode :
      right.nodes candidate.node =
        .ref (iso.regions region) definition args := by
    rw [nodeEquality, iso.node_table, nodeData]
    rfl
  have portEquality : candidate.port = port := by
    unfold PortCorresponds at corresponds
    rw [nodeData, rightNode] at corresponds
    exact corresponds.2
  have candidateEquality :
      candidate = (⟨iso.nodes node, port⟩ :
        CEndpoint right.nodeCount) := by
    cases candidate with
    | mk candidateNode candidatePort =>
        simp only at nodeEquality portEquality ⊢
        subst candidateNode
        subst candidatePort
        rfl
  subst candidate
  exact ConcreteDiagram.endpointOwner?_eq_of_incident definitions right
    rightWellFormed (iso.nodes node) port
    (iso.requiredPorts_forward
      (ConcreteDiagram.incident_port_required definitions left
        leftWellFormed wire ⟨node, port⟩ incident))
    (iso.wires wire) candidateMember

theorem ref_owner_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
    {port : CPort} {targetWire : right.WireId}
    (owner : right.endpointOwner? ⟨iso.nodes node, port⟩ =
      some targetWire) :
    left.endpointOwner? ⟨node, port⟩ =
      some (iso.wires.symm targetWire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident right
      ⟨iso.nodes node, port⟩ targetWire owner
  have mappedIncident :
      (⟨iso.nodes node, port⟩ : CEndpoint right.nodeCount) ∈
        (right.wires
          (iso.wires (iso.wires.symm targetWire))).endpoints := by
    change (⟨iso.nodes node, port⟩ : CEndpoint right.nodeCount) ∈
      (right.wires
        (iso.wires (iso.wires.invFun targetWire))).endpoints
    rw [iso.wires.right_inv]
    exact incident
  obtain ⟨endpoint, endpointMember, corresponds⟩ :=
    iso.endpoint_backward (iso.wires.symm targetWire)
      ⟨iso.nodes node, port⟩ mappedIncident
  have endpointNode : endpoint.node = node := by
    apply iso.nodes.injective
    exact corresponds.1.symm
  have rightNode :
      right.nodes
          (⟨iso.nodes node, port⟩ :
            CEndpoint right.nodeCount).node =
        .ref (iso.regions region) definition args := by
    rw [iso.node_table, nodeData]
    rfl
  have endpointPort : endpoint.port = port := by
    unfold PortCorresponds at corresponds
    rw [endpointNode, nodeData, rightNode] at corresponds
    exact corresponds.2.symm
  have endpointEquality :
      endpoint = (⟨node, port⟩ : CEndpoint left.nodeCount) := by
    cases endpoint with
    | mk sourceNode sourcePort =>
        simp only at endpointNode endpointPort ⊢
        subst sourceNode
        subst sourcePort
        rfl
  subst endpoint
  have required :=
    ConcreteDiagram.incident_port_required definitions left
      leftWellFormed (iso.wires.symm targetWire)
      ⟨node, port⟩ endpointMember
  exact ConcreteDiagram.endpointOwner?_eq_of_incident definitions left
    leftWellFormed node port required
    (iso.wires.symm targetWire) endpointMember

theorem identity_owner_forward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (rightWellFormed : right.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    {index : Nat} {wire : left.WireId}
    (owner : left.endpointOwner? ⟨node, .identity index⟩ = some wire) :
    ∃ targetIndex,
      right.endpointOwner? ⟨iso.nodes node, .identity targetIndex⟩ =
        some (iso.wires wire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident left
      ⟨node, .identity index⟩ wire owner
  obtain ⟨candidate, candidateMember, corresponds⟩ :=
    iso.endpoint_forward wire ⟨node, .identity index⟩ incident
  have nodeEquality : candidate.node = iso.nodes node :=
    corresponds.1
  have rightNode :
      right.nodes candidate.node =
        .identity (iso.regions region) sig arity := by
    rw [nodeEquality, iso.node_table, nodeData]
    rfl
  unfold PortCorresponds at corresponds
  rw [nodeData, rightNode] at corresponds
  rcases corresponds with
    ⟨_, _, _, ⟨leftIndex, rightIndex, _, candidatePort⟩⟩
  have candidateEquality :
      candidate = (⟨iso.nodes node, .identity rightIndex⟩ :
        CEndpoint right.nodeCount) := by
    cases candidate with
    | mk candidateNode candidatePortValue =>
        simp only at nodeEquality candidatePort ⊢
        subst candidateNode
        subst candidatePortValue
        rfl
  subst candidate
  have required :=
    ConcreteDiagram.incident_port_required definitions right
      rightWellFormed (iso.wires wire)
      ⟨iso.nodes node, .identity rightIndex⟩ candidateMember
  exact ⟨rightIndex,
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions right
      rightWellFormed (iso.nodes node) (.identity rightIndex) required
      (iso.wires wire) candidateMember⟩

theorem identity_owner_backward
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    {targetIndex : Nat} {targetWire : right.WireId}
    (owner : right.endpointOwner?
      ⟨iso.nodes node, .identity targetIndex⟩ = some targetWire) :
    ∃ sourceIndex,
      left.endpointOwner?
        ⟨node, .identity sourceIndex⟩ =
          some (iso.wires.symm targetWire) := by
  have incident :=
    ConcreteDiagram.endpointOwner?_incident right
      ⟨iso.nodes node, .identity targetIndex⟩ targetWire owner
  have mappedIncident :
      (⟨iso.nodes node, .identity targetIndex⟩ :
        CEndpoint right.nodeCount) ∈
        (right.wires (iso.wires (iso.wires.symm targetWire))).endpoints := by
    change (⟨iso.nodes node, .identity targetIndex⟩ :
      CEndpoint right.nodeCount) ∈
        (right.wires (iso.wires (iso.wires.invFun targetWire))).endpoints
    rw [iso.wires.right_inv]
    exact incident
  obtain ⟨endpoint, endpointMember, corresponds⟩ :=
    iso.endpoint_backward (iso.wires.symm targetWire)
      ⟨iso.nodes node, .identity targetIndex⟩ mappedIncident
  have nodeEquality : endpoint.node = node := by
    apply iso.nodes.injective
    calc
      iso.nodes endpoint.node =
          (⟨iso.nodes node, .identity targetIndex⟩ :
            CEndpoint right.nodeCount).node := corresponds.1.symm
      _ = iso.nodes node := rfl
  have rightNode :
      right.nodes
          (⟨iso.nodes node, .identity targetIndex⟩ :
            CEndpoint right.nodeCount).node =
        .identity (iso.regions region) sig arity := by
    rw [iso.node_table, nodeData]
    rfl
  unfold PortCorresponds at corresponds
  rw [nodeEquality, nodeData, rightNode] at corresponds
  rcases corresponds with
    ⟨_, _, _, ⟨sourceIndex, _, endpointPort, _⟩⟩
  have endpointEquality :
      endpoint = (⟨node, .identity sourceIndex⟩ :
        CEndpoint left.nodeCount) := by
    cases endpoint with
    | mk endpointNode endpointPortValue =>
        simp only at nodeEquality endpointPort ⊢
        subst endpointNode
        subst endpointPortValue
        rfl
  subst endpoint
  have required :=
    ConcreteDiagram.incident_port_required definitions left
      leftWellFormed (iso.wires.symm targetWire)
      ⟨node, .identity sourceIndex⟩ endpointMember
  exact ⟨sourceIndex,
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions left
      leftWellFormed node (.identity sourceIndex) required
      (iso.wires.symm targetWire) endpointMember⟩

theorem identity_incidence_orderless
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {wire : left.WireId} {endpoint : CEndpoint left.nodeCount}
    (member : endpoint ∈ (left.wires wire).endpoints) :
    ∃ candidate,
      candidate ∈ (right.wires (iso.wires wire)).endpoints ∧
        PortCorresponds left right iso.nodes endpoint candidate :=
  iso.endpoint_forward wire endpoint member

private def explicitPortCorresponds
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (endpoint : CEndpoint left.nodeCount)
    (candidate : CEndpoint right.nodeCount) : Bool :=
  decide (candidate.node = nodes endpoint.node) &&
    match left.nodes endpoint.node, right.nodes candidate.node with
    | .identity _ leftSig leftArity, .identity _ rightSig rightArity =>
        decide (leftSig = rightSig) && decide (leftArity = rightArity) &&
          match endpoint.port, candidate.port with
          | .identity _, .identity _ => true
          | _, _ => false
    | _, _ => decide (candidate.port = endpoint.port)

private theorem explicitPortCorresponds_of_true
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (endpoint : CEndpoint left.nodeCount)
    (candidate : CEndpoint right.nodeCount)
    (accepted :
      explicitPortCorresponds left right nodes endpoint candidate = true) :
    PortCorresponds left right nodes endpoint candidate := by
  rcases endpoint with ⟨endpointNode, endpointPort⟩
  rcases candidate with ⟨candidateNode, candidatePort⟩
  unfold explicitPortCorresponds at accepted
  rcases Bool.and_eq_true_iff.mp accepted with ⟨nodeExact, rest⟩
  refine ⟨of_decide_eq_true nodeExact, ?_⟩
  cases leftNode : left.nodes endpointNode <;>
    cases rightNode : right.nodes candidateNode
  all_goals rw [leftNode, rightNode] at rest
  all_goals simp only at rest ⊢
  all_goals try exact of_decide_eq_true rest
  rename_i leftRegion leftSig leftArity rightRegion rightSig rightArity
  rcases Bool.and_eq_true_iff.mp rest with ⟨sigArity, ports⟩
  rcases Bool.and_eq_true_iff.mp sigArity with ⟨sigExact, arityExact⟩
  cases endpointPort <;> cases candidatePort <;> simp_all

private def explicitEndpointFiber
    (endpoints : List (CEndpoint nodeCount))
    (node : Fin nodeCount) (port : CPort) :
    List (CEndpoint nodeCount) :=
  endpoints.filter fun candidate =>
    decide (candidate.node = node) &&
      match port, candidate.port with
      | .identity _, .identity _ => true
      | _, _ => decide (candidate.port = port)

private def explicitEndpointMap?
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (wire : left.WireId)
    (targetWire : right.WireId)
    (endpoint : CEndpoint left.nodeCount) :
    Option (CEndpoint right.nodeCount) :=
  let sourceFiber := explicitEndpointFiber (left.wires wire).endpoints
    endpoint.node endpoint.port
  let targetFiber := explicitEndpointFiber
    (right.wires targetWire).endpoints (nodes endpoint.node) endpoint.port
  targetFiber[sourceFiber.idxOf endpoint]?

private def explicitEndpointInverse?
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (wire : left.WireId)
    (targetWire : right.WireId)
    (candidate : CEndpoint right.nodeCount) :
    Option (CEndpoint left.nodeCount) :=
  let targetFiber := explicitEndpointFiber
    (right.wires targetWire).endpoints candidate.node candidate.port
  let sourceFiber := explicitEndpointFiber (left.wires wire).endpoints
    (nodes.symm candidate.node) candidate.port
  sourceFiber[targetFiber.idxOf candidate]?

/-- Validate an explicitly supplied finite identifier correspondence.  This
checker proves table and incidence preservation but never enumerates or
discovers a map. -/
def checkEquivs?
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (regions : Data.Finite.FiniteEquiv left.RegionId right.RegionId)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (wires : Data.Finite.FiniteEquiv left.WireId right.WireId) :
    Option (ConcreteIso left right) := by
  let rootValid := decide (regions left.root = right.root)
  let regionsValid :=
    (Data.Finite.allFin left.regionCount).all fun region =>
      decide (right.regions (regions region) =
        (left.regions region).rename regions)
  let nodesValid :=
    (Data.Finite.allFin left.nodeCount).all fun node =>
      decide (right.nodes (nodes node) =
        (left.nodes node).rename regions)
  let signaturesValid :=
    (Data.Finite.allFin left.wireCount).all fun wire =>
      decide ((right.wires (wires wire)).sig = (left.wires wire).sig)
  let scopesValid :=
    (Data.Finite.allFin left.wireCount).all fun wire =>
      decide ((right.wires (wires wire)).scope =
        regions (left.wires wire).scope)
  let forwardValid :=
    (Data.Finite.allFin left.wireCount).all fun wire =>
      (left.wires wire).endpoints.all fun endpoint =>
        match explicitEndpointMap? left right nodes wire (wires wire)
            endpoint with
        | none => false
        | some candidate =>
            decide (candidate ∈
              (right.wires (wires wire)).endpoints) &&
            explicitPortCorresponds left right nodes endpoint candidate &&
            decide (explicitEndpointInverse? left right nodes wire
              (wires wire) candidate = some endpoint)
  let backwardValid :=
    (Data.Finite.allFin left.wireCount).all fun wire =>
      (right.wires (wires wire)).endpoints.all fun candidate =>
        match explicitEndpointInverse? left right nodes wire (wires wire)
            candidate with
        | none => false
        | some endpoint =>
            decide (endpoint ∈ (left.wires wire).endpoints) &&
            decide (explicitEndpointMap? left right nodes wire
              (wires wire) endpoint = some candidate)
  if accepted : rootValid && regionsValid && nodesValid &&
      signaturesValid && scopesValid && forwardValid && backwardValid then
    have parts := Bool.and_eq_true_iff.mp accepted
    have backwardAccepted := parts.2
    have parts := Bool.and_eq_true_iff.mp parts.1
    have forwardAccepted := parts.2
    have parts := Bool.and_eq_true_iff.mp parts.1
    have scopesAccepted := parts.2
    have parts := Bool.and_eq_true_iff.mp parts.1
    have signaturesAccepted := parts.2
    have parts := Bool.and_eq_true_iff.mp parts.1
    have nodesAccepted := parts.2
    have parts := Bool.and_eq_true_iff.mp parts.1
    have rootAccepted := parts.1
    have regionsAccepted := parts.2
    exact some
      { regions := regions
        nodes := nodes
        wires := wires
        root := of_decide_eq_true rootAccepted
        region_table := by
          intro region
          exact of_decide_eq_true
            (List.all_eq_true.mp regionsAccepted region
              (Data.Finite.mem_allFin region))
        node_table := by
          intro node
          exact of_decide_eq_true
            (List.all_eq_true.mp nodesAccepted node
              (Data.Finite.mem_allFin node))
        wire_signature := by
          intro wire
          exact of_decide_eq_true
            (List.all_eq_true.mp signaturesAccepted wire
              (Data.Finite.mem_allFin wire))
        wire_scope := by
          intro wire
          exact of_decide_eq_true
            (List.all_eq_true.mp scopesAccepted wire
              (Data.Finite.mem_allFin wire))
        endpointMap := fun wire endpoint =>
          (explicitEndpointMap? left right nodes wire (wires wire)
            endpoint).getD ⟨nodes endpoint.node, endpoint.port⟩
        endpointInverse := fun wire candidate =>
          (explicitEndpointInverse? left right nodes wire (wires wire)
            candidate).getD ⟨nodes.symm candidate.node, candidate.port⟩
        endpointMap_mem := by
          intro wire endpoint member
          have wireAccepted :=
            List.all_eq_true.mp forwardAccepted wire
              (Data.Finite.mem_allFin wire)
          have endpointAccepted :=
            List.all_eq_true.mp wireAccepted endpoint member
          cases mapped : explicitEndpointMap? left right nodes wire
              (wires wire) endpoint with
          | none => simp [mapped] at endpointAccepted
          | some candidate =>
              simp only [mapped, Bool.and_eq_true] at endpointAccepted
              simpa [mapped] using
                of_decide_eq_true endpointAccepted.1.1
        endpointInverse_mem := by
          intro wire candidate member
          have wireAccepted :=
            List.all_eq_true.mp backwardAccepted wire
              (Data.Finite.mem_allFin wire)
          have endpointAccepted :=
            List.all_eq_true.mp wireAccepted candidate member
          cases mapped : explicitEndpointInverse? left right nodes wire
              (wires wire) candidate with
          | none => simp [mapped] at endpointAccepted
          | some endpoint =>
              simp only [mapped, Bool.and_eq_true] at endpointAccepted
              simpa [mapped] using
                of_decide_eq_true endpointAccepted.1
        endpointMap_left_inv := by
          intro wire endpoint member
          have wireAccepted := List.all_eq_true.mp forwardAccepted wire
            (Data.Finite.mem_allFin wire)
          have endpointAccepted :=
            List.all_eq_true.mp wireAccepted endpoint member
          cases mapped : explicitEndpointMap? left right nodes wire
              (wires wire) endpoint with
          | none => simp [mapped] at endpointAccepted
          | some candidate =>
              simp only [mapped, Bool.and_eq_true] at endpointAccepted
              have inverseExact := of_decide_eq_true endpointAccepted.2
              simpa [mapped, inverseExact]
        endpointMap_right_inv := by
          intro wire candidate member
          have wireAccepted := List.all_eq_true.mp backwardAccepted wire
            (Data.Finite.mem_allFin wire)
          have endpointAccepted :=
            List.all_eq_true.mp wireAccepted candidate member
          cases mapped : explicitEndpointInverse? left right nodes wire
              (wires wire) candidate with
          | none => simp [mapped] at endpointAccepted
          | some endpoint =>
              simp only [mapped, Bool.and_eq_true] at endpointAccepted
              have forwardExact := of_decide_eq_true endpointAccepted.2
              simpa [mapped, forwardExact]
        endpointMap_corresponds := by
          intro wire endpoint member
          have wireAccepted := List.all_eq_true.mp forwardAccepted wire
            (Data.Finite.mem_allFin wire)
          have endpointAccepted :=
            List.all_eq_true.mp wireAccepted endpoint member
          cases mapped : explicitEndpointMap? left right nodes wire
              (wires wire) endpoint with
          | none => simp [mapped] at endpointAccepted
          | some candidate =>
              simp only [mapped, Bool.and_eq_true] at endpointAccepted
              simpa [mapped] using
                explicitPortCorresponds_of_true left right nodes endpoint
                  candidate endpointAccepted.1.2 }
  else
    exact none

end ConcreteIso

end VisualProof
