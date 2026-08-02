import VisualProof.Diagram.Concrete.DenseIsomorphism
import VisualProof.Diagram.Concrete.IdentityNormalization

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace DenseIdentityNormalization

private def isIdentityNode
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) : Bool :=
  match diagram.nodes node with
  | .identity _ _ _ => true
  | _ => false

private theorem isIdentityNode_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (node : left.NodeId) :
    isIdentityNode right (dense.iso.nodes node) =
      isIdentityNode left node := by
  rw [isIdentityNode, isIdentityNode]
  rw [dense.iso.node_table node]
  cases left.nodes node <;> rfl

/-- A dense isomorphism maps the deterministic identity-node enumeration
position for position. -/
theorem map_identityNodeIds
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right) :
    (identityNodeIds left).map dense.iso.nodes = identityNodeIds right := by
  change
    (left.nodesList.filter (isIdentityNode left)).map dense.iso.nodes =
      right.nodesList.filter (isIdentityNode right)
  rw [← dense.map_nodesList]
  rw [List.filter_map]
  apply congrArg (List.map dense.iso.nodes)
  apply congrArg (fun predicate => left.nodesList.filter predicate)
  funext node
  exact (isIdentityNode_map dense node).symm

/-- Dense endpoint fibers preserve physical identity incidence. -/
theorem mem_identityIncidentWires_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (node : left.NodeId)
    (wire : left.WireId) :
    dense.iso.wires wire ∈
        right.identityIncidentWires (dense.iso.nodes node) ↔
      wire ∈ left.identityIncidentWires node := by
  constructor
  · intro incident
    obtain ⟨candidate, candidateMember, candidateNode⟩ :=
      (mem_identityIncidentWires right (dense.iso.nodes node)
        (dense.iso.wires wire)).mp incident
    obtain ⟨endpoint, endpointMember, corresponds⟩ :=
      dense.iso.endpoint_backward wire candidate candidateMember
    have nodeExact : endpoint.node = node := by
      have mapped := corresponds.1
      rw [candidateNode] at mapped
      exact dense.iso.nodes.injective mapped.symm
    exact (mem_identityIncidentWires left node wire).mpr
      ⟨endpoint, endpointMember, nodeExact⟩
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires left node wire).mp incident
    obtain ⟨candidate, candidateMember, corresponds⟩ :=
      dense.iso.endpoint_forward wire endpoint endpointMember
    refine (mem_identityIncidentWires right (dense.iso.nodes node)
      (dense.iso.wires wire)).mpr ⟨candidate, candidateMember, ?_⟩
    exact corresponds.1.trans (congrArg dense.iso.nodes endpointNode)

private def isIncident
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId)
    (wire : diagram.WireId) : Bool :=
  (diagram.wires wire).endpoints.any fun endpoint =>
    decide (endpoint.node = node)

private theorem isIncident_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (node : left.NodeId)
    (wire : left.WireId) :
    isIncident right (dense.iso.nodes node) (dense.iso.wires wire) =
      isIncident left node wire := by
  apply Bool.eq_iff_iff.mpr
  simp only [isIncident, List.any_eq_true, decide_eq_true_eq]
  simpa only [mem_identityIncidentWires] using
    mem_identityIncidentWires_map dense node wire

/-- The dense wire map preserves deterministic incident-wire order. -/
theorem map_identityIncidentWires
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (node : left.NodeId) :
    (left.identityIncidentWires node).map dense.iso.wires =
      right.identityIncidentWires (dense.iso.nodes node) := by
  change
    (left.wiresList.filter (isIncident left node)).map dense.iso.wires =
      right.wiresList.filter (isIncident right (dense.iso.nodes node))
  rw [← dense.map_wiresList]
  rw [List.filter_map]
  apply congrArg (List.map dense.iso.wires)
  apply congrArg (fun predicate => left.wiresList.filter predicate)
  funext wire
  exact (isIncident_map dense node wire).symm

private def isRetainedNode
    (diagram : ConcreteDiagram definitionCount)
    (removed candidate : diagram.NodeId) : Bool :=
  decide (candidate ≠ removed)

private theorem isRetainedNode_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (removed candidate : left.NodeId) :
    isRetainedNode right (dense.iso.nodes removed)
        (dense.iso.nodes candidate) =
      isRetainedNode left removed candidate := by
  apply Bool.eq_iff_iff.mpr
  simp only [isRetainedNode, decide_eq_true_eq]
  exact not_congr dense.iso.nodes.injective.eq_iff

/-- Deleting corresponding dense node ids leaves corresponding node order. -/
theorem map_retainedNodes_singleton
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (removed : left.NodeId) :
    (retainedNodes left [removed]).map dense.iso.nodes =
      retainedNodes right [dense.iso.nodes removed] := by
  unfold retainedNodes
  simp only [List.mem_singleton]
  change
    (left.nodesList.filter (isRetainedNode left removed)).map
        dense.iso.nodes =
      right.nodesList.filter
        (isRetainedNode right (dense.iso.nodes removed))
  rw [← dense.map_nodesList]
  rw [List.filter_map]
  apply congrArg (List.map dense.iso.nodes)
  apply congrArg (fun predicate => left.nodesList.filter predicate)
  funext node
  exact (isRetainedNode_map dense removed node).symm

private def isOuter
    (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId)
    (wire : diagram.WireId) : Bool :=
  decide ((diagram.wires wire).scope ≠ region)

private theorem isOuter_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (region : left.RegionId)
    (wire : left.WireId) :
  isOuter right (dense.iso.regions region) (dense.iso.wires wire) =
      isOuter left region wire := by
  apply Bool.eq_iff_iff.mpr
  simp only [isOuter, decide_eq_true_eq]
  rw [dense.iso.wire_scope wire]
  exact not_congr dense.iso.regions.injective.eq_iff

private theorem map_outerIncidentWires
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (region : left.val.RegionId) :
    ((left.val.identityIncidentWires node).filter
      (isOuter left.val region)).map dense.iso.wires =
    (right.val.identityIncidentWires (dense.iso.nodes node)).filter
      (isOuter right.val (dense.iso.regions region)) := by
  rw [← map_identityIncidentWires dense node]
  rw [List.filter_map]
  apply congrArg (List.map dense.iso.wires)
  apply congrArg
    (fun predicate => (left.val.identityIncidentWires node).filter predicate)
  funext wire
  exact (isOuter_map dense region wire).symm

private theorem map_innerIncidentWires
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (region : left.val.RegionId) :
    ((left.val.identityIncidentWires node).filter
      (fun wire => !isOuter left.val region wire)).map dense.iso.wires =
    (right.val.identityIncidentWires (dense.iso.nodes node)).filter
      (fun wire => !isOuter right.val (dense.iso.regions region) wire) := by
  rw [← map_identityIncidentWires dense node]
  rw [List.filter_map]
  apply congrArg (List.map dense.iso.wires)
  apply congrArg
    (fun predicate => (left.val.identityIncidentWires node).filter predicate)
  funext wire
  simp only [Function.comp_apply, isOuter_map dense region wire]

/-- Dense correspondence preserves the survivor-first collapse enumeration. -/
theorem map_collapseIncidentWires
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (region : left.val.RegionId) :
    (collapseIncidentWires left node region).map dense.iso.wires =
      collapseIncidentWires right (dense.iso.nodes node)
        (dense.iso.regions region) := by
  simp only [collapseIncidentWires, List.map_append]
  have outer := map_outerIncidentWires dense node region
  have inner := map_innerIncidentWires dense node region
  have pairExact :
      ( ((left.val.identityIncidentWires node).filter
          (isOuter left.val region)).map dense.iso.wires
      , ((left.val.identityIncidentWires node).filter
          (fun wire => !isOuter left.val region wire)).map dense.iso.wires ) =
      ( (right.val.identityIncidentWires (dense.iso.nodes node)).filter
          (isOuter right.val (dense.iso.regions region))
      , (right.val.identityIncidentWires (dense.iso.nodes node)).filter
          (fun wire =>
            !isOuter right.val (dense.iso.regions region) wire) ) :=
    Prod.ext outer inner
  simpa only [isOuter] using
    congrArg (fun parts => parts.1 ++ parts.2) pairExact

/-- Transport the complete identity-node data through a dense isomorphism. -/
def transportIdentityNodeInfo
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (info : IdentityNodeInfo left node) :
    IdentityNodeInfo right (dense.iso.nodes node) where
  region := dense.iso.regions info.region
  signature := info.signature
  arity := info.arity
  node_eq := by
    rw [dense.iso.node_table node, info.node_eq]
    rfl

/-- Rule-1 eligibility is invariant under dense concrete isomorphism. -/
def transportDropEligibility
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (eligible : DropEligibility left node) :
    DropEligibility right (dense.iso.nodes node) where
  identity := transportIdentityNodeInfo dense eligible.identity
  incident_lt_two := by
    rw [← map_identityIncidentWires dense node]
    simpa only [List.length_map] using eligible.incident_lt_two

/-- Rule-2 eligibility is invariant under dense concrete isomorphism. -/
def transportCollapseEligibility
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (dense : DenseConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (eligible : CollapseEligibility left node) :
    CollapseEligibility right (dense.iso.nodes node) where
  identity := transportIdentityNodeInfo dense eligible.identity
  survivor := dense.iso.wires eligible.survivor
  second := dense.iso.wires eligible.second
  rest := eligible.rest.map dense.iso.wires
  incident_eq := by
    change collapseIncidentWires right (dense.iso.nodes node)
      (dense.iso.regions eligible.identity.region) = _
    rw [← map_collapseIncidentWires dense node eligible.identity.region]
    rw [eligible.incident_eq]
    rfl
  absorbedCoScoped := by
    intro wire member
    have sourceMember :
        dense.iso.wires.symm wire ∈ eligible.second :: eligible.rest := by
      simp only [List.mem_cons] at member
      rcases member with member | member
      · have wireExact : wire = dense.iso.wires eligible.second := member
        subst wire
        have sourceMember :
            eligible.second ∈ eligible.second :: eligible.rest := by simp
        simpa only [Data.Finite.FiniteEquiv.symm_apply_apply] using sourceMember
      · rcases List.mem_map.mp member with ⟨source, sourceMember, exact⟩
        subst wire
        simpa only [Data.Finite.FiniteEquiv.symm_apply_apply] using
          List.mem_cons_of_mem eligible.second sourceMember
    have sourceScope := eligible.absorbedCoScoped _ sourceMember
    change (right.val.wires wire).scope =
      dense.iso.regions eligible.identity.region
    calc
      (right.val.wires wire).scope =
          (right.val.wires
            (dense.iso.wires (dense.iso.wires.symm wire))).scope :=
        congrArg (fun target => (right.val.wires target).scope)
          (dense.iso.wires.right_inv wire).symm
      _ = dense.iso.regions
          (left.val.wires (dense.iso.wires.symm wire)).scope :=
        dense.iso.wire_scope _
      _ = dense.iso.regions eligible.identity.region :=
        congrArg dense.iso.regions sourceScope

end DenseIdentityNormalization

end ConcreteDiagram

end VisualProof
