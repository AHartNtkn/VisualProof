import VisualProof.Diagram.Concrete.IdentityIncidence
import VisualProof.Diagram.Concrete.DenseErasure

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

open DenseErasure

/-- The stored identity data witnessed by one checked node. -/
structure IdentityNodeInfo
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) where
  region : source.val.RegionId
  signature : Sig
  arity : Nat
  node_eq :
    source.val.nodes node = .identity region signature arity

/--
Stable one-point-collapse order: wires scoped outside the identity region come
first, followed by the co-scoped wires, with concrete order preserved inside
each class.  Eligibility therefore chooses the unique outer wire as survivor
when one exists, without making physical identity-port order authoritative.
-/
def collapseIncidentWires
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) :
    List source.val.WireId :=
  let incident := source.val.identityIncidentWires node
  let outer : source.val.WireId → Bool :=
    fun wire => decide ((source.val.wires wire).scope ≠ region)
  incident.filter outer ++ incident.filter (fun wire => !outer wire)

theorem collapseIncidentWires_perm
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) :
    (collapseIncidentWires source node region).Perm
      (source.val.identityIncidentWires node) := by
  exact List.filter_append_perm _ _

@[simp] theorem mem_collapseIncidentWires
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId)
    (wire : source.val.WireId) :
    wire ∈ collapseIncidentWires source node region ↔
      wire ∈ source.val.identityIncidentWires node :=
  (collapseIncidentWires_perm source node region).mem_iff

theorem collapseIncidentWires_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) :
    (collapseIncidentWires source node region).Nodup :=
  (collapseIncidentWires_perm source node region).nodup_iff.mpr
    (source.val.identityIncidentWires_nodup node)

/-- The complete eligibility receipt for Rule 1. -/
structure DropEligibility
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) where
  identity : IdentityNodeInfo source node
  incident_lt_two :
    (source.val.identityIncidentWires node).length < 2

/-- The complete eligibility receipt for Rule 2. -/
structure CollapseEligibility
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) where
  identity : IdentityNodeInfo source node
  survivor : source.val.WireId
  second : source.val.WireId
  rest : List source.val.WireId
  incident_eq :
    collapseIncidentWires source node identity.region =
      survivor :: second :: rest
  absorbedCoScoped :
    ∀ wire, wire ∈ second :: rest →
      (source.val.wires wire).scope = identity.region

/-- The complete eligibility receipt for Rule 3. -/
structure FusionEligibility
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) where
  leftIdentity : IdentityNodeInfo source left
  rightIdentity : IdentityNodeInfo source right
  distinct : left ≠ right
  sameRegion : leftIdentity.region = rightIdentity.region
  shared :
    ∃ wire,
      wire ∈ source.val.identityIncidentWires left ∧
      wire ∈ source.val.identityIncidentWires right
  union_at_least_two :
    2 ≤
      (source.val.identityIncidentWires left ++
        source.val.identityIncidentWires right).eraseDups.length

/-- Decide Rule 1 eligibility and retain every fact used by construction. -/
def dropEligibility?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Option (DropEligibility source node) := by
  match nodeData : source.val.nodes node with
  | .identity region sig arity =>
      if incidentLt :
          (source.val.identityIncidentWires node).length < 2 then
        exact some
          { identity :=
              { region := region
                signature := sig
                arity := arity
                node_eq := nodeData }
            incident_lt_two := incidentLt }
      else
        exact none
  | .atom _ _ => exact none
  | .ref _ _ _ => exact none

/-- Decide Rule 2 eligibility and retain every fact used by construction. -/
def collapseEligibility?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Option (CollapseEligibility source node) := by
  match nodeData : source.val.nodes node with
  | .identity region sig arity =>
      match incidentEq :
          collapseIncidentWires source node region with
      | survivor :: second :: rest =>
          if absorbedCoScoped :
              ∀ wire, wire ∈ second :: rest →
                (source.val.wires wire).scope = region then
            exact some
              { identity :=
                  { region := region
                    signature := sig
                    arity := arity
                    node_eq := nodeData }
                survivor := survivor
                second := second
                rest := rest
                incident_eq := incidentEq
                absorbedCoScoped := absorbedCoScoped }
          else
            exact none
      | _ => exact none
  | .atom _ _ => exact none
  | .ref _ _ _ => exact none

/-- Decide Rule 3 eligibility and retain every fact used by construction. -/
def fusionEligibility?
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    Option (FusionEligibility source left right) := by
  match leftData : source.val.nodes left,
      rightData : source.val.nodes right with
  | .identity leftRegion leftSig leftArity,
      .identity rightRegion rightSig rightArity =>
      if distinct : left ≠ right then
        if sameRegion : leftRegion = rightRegion then
          if shared :
              ∃ wire,
                wire ∈ source.val.identityIncidentWires left ∧
                wire ∈ source.val.identityIncidentWires right then
            if unionAtLeastTwo :
                2 ≤
                  (source.val.identityIncidentWires left ++
                    source.val.identityIncidentWires right).eraseDups.length then
              exact some
                { leftIdentity :=
                    { region := leftRegion
                      signature := leftSig
                      arity := leftArity
                      node_eq := leftData }
                  rightIdentity :=
                    { region := rightRegion
                      signature := rightSig
                      arity := rightArity
                      node_eq := rightData }
                  distinct := distinct
                  sameRegion := sameRegion
                  shared := shared
                  union_at_least_two := unionAtLeastTwo }
            else
              exact none
          else
            exact none
        else
          exact none
      else
        exact none
  | _, _ => exact none

/-- Every propositional Rule-1 receipt is rediscovered by the executable
eligibility checker.  The returned receipt may differ only in proof fields. -/
theorem dropEligibility?_complete
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    ∃ found, dropEligibility? source node = some found := by
  unfold dropEligibility?
  split
  next region sig arity nodeData =>
    split
    next _ => exact ⟨_, rfl⟩
    next rejected => exact False.elim (rejected eligible.incident_lt_two)
  next _ _ nodeData =>
    exact False.elim (by
      rw [eligible.identity.node_eq] at nodeData
      contradiction)
  next _ _ _ nodeData =>
    exact False.elim (by
      rw [eligible.identity.node_eq] at nodeData
      contradiction)

/-- Every propositional Rule-2 receipt is rediscovered by the executable
eligibility checker. -/
theorem collapseEligibility?_complete
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    ∃ found, collapseEligibility? source node = some found := by
  unfold collapseEligibility?
  split
  next region sig arity nodeData =>
    split
    next survivor second rest incidentEq =>
      split
      next _ => exact ⟨_, rfl⟩
      next rejected =>
        have sameRegion : region = eligible.identity.region := by
          have sameNode := nodeData.symm.trans eligible.identity.node_eq
          exact (CNode.identity.inj sameNode).1
        subst region
        have sameIncident := eligible.incident_eq
        rw [incidentEq] at sameIncident
        obtain ⟨rfl, rfl, rfl⟩ := List.cons.inj sameIncident
        exact False.elim (rejected eligible.absorbedCoScoped)
    next noPair =>
      have sameRegion : region = eligible.identity.region := by
        have sameNode := nodeData.symm.trans eligible.identity.node_eq
        exact (CNode.identity.inj sameNode).1
      subst region
      exact False.elim
        (noPair eligible.survivor eligible.second eligible.rest
          eligible.incident_eq)
  next _ _ nodeData =>
    exact False.elim (by
      rw [eligible.identity.node_eq] at nodeData
      contradiction)
  next _ _ _ nodeData =>
    exact False.elim (by
      rw [eligible.identity.node_eq] at nodeData
      contradiction)

/-- Erasing duplicates makes the union cardinality insensitive to the order
of its two input lists. -/
private theorem eraseDups_append_length_comm
    (left right : List α) [BEq α] [LawfulBEq α] :
    (left ++ right).eraseDups.length =
      (right ++ left).eraseDups.length := by
  apply List.Perm.length_eq
  rw [List.perm_iff_count]
  intro value
  rw [(VisualProof.Data.Finite.eraseDups_nodup _).count,
    (VisualProof.Data.Finite.eraseDups_nodup _).count]
  simp only [List.mem_eraseDups, List.mem_append, or_comm]

/-- Fusion eligibility is unordered even though the construction retains its
left node. -/
def FusionEligibility.symm
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {left right : source.val.NodeId}
    (eligible : FusionEligibility source left right) :
    FusionEligibility source right left where
  leftIdentity := eligible.rightIdentity
  rightIdentity := eligible.leftIdentity
  distinct := eligible.distinct.symm
  sameRegion := eligible.sameRegion.symm
  shared := by
    obtain ⟨wire, leftMember, rightMember⟩ := eligible.shared
    exact ⟨wire, rightMember, leftMember⟩
  union_at_least_two := by
    rw [eraseDups_append_length_comm]
    exact eligible.union_at_least_two

/-- Every propositional Rule-3 receipt is rediscovered by the executable
eligibility checker. -/
theorem fusionEligibility?_complete
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ∃ found, fusionEligibility? source left right = some found := by
  unfold fusionEligibility?
  split
  next leftRegion leftSig leftArity rightRegion rightSig rightArity
      leftData rightData =>
    split
    next _ =>
      split
      next _ =>
        split
        next _ =>
          split
          next _ => exact ⟨_, rfl⟩
          next rejected =>
            exact False.elim (rejected eligible.union_at_least_two)
        next rejected => exact False.elim (rejected eligible.shared)
      next rejected =>
        exact False.elim (rejected (by
          have leftParts := CNode.identity.inj
            (leftData.symm.trans eligible.leftIdentity.node_eq)
          have rightParts := CNode.identity.inj
            (rightData.symm.trans eligible.rightIdentity.node_eq)
          exact leftParts.1.trans
            (eligible.sameRegion.trans rightParts.1.symm)))
    next rejected => exact False.elim (rejected eligible.distinct)
  next noPair =>
    exact False.elim
      (noPair eligible.leftIdentity.region eligible.leftIdentity.signature
        eligible.leftIdentity.arity eligible.rightIdentity.region
        eligible.rightIdentity.signature eligible.rightIdentity.arity
        eligible.leftIdentity.node_eq eligible.rightIdentity.node_eq)

def identityNodeIds
    (diagram : ConcreteDiagram definitionCount) :
    List diagram.NodeId :=
  diagram.nodesList.filter fun node =>
    match diagram.nodes node with
    | .identity _ _ _ => true
    | _ => false

/-- A stored identity-table receipt places its node in the executable
identity enumeration. -/
theorem IdentityNodeInfo.mem_identityNodeIds
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {node : source.val.NodeId}
    (info : IdentityNodeInfo source node) :
    node ∈ identityNodeIds source.val := by
  simp only [identityNodeIds, List.mem_filter]
  exact ⟨Data.Finite.mem_allFin node, by rw [info.node_eq]⟩

/-- Raw Rule 1 candidate. Its sole consumer is the preservation proof layer. -/
def dropCandidate
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (_eligible : DropEligibility source node) :
    ConcreteDiagram definitions.length :=
  eraseNodeCandidate source node

/-- Raw Rule 2 candidate. Its sole consumer is the preservation proof layer. -/
def collapseCandidate
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    ConcreteDiagram definitions.length :=
  let incident := source.val.identityIncidentWires node
  let absorbed := eligible.second :: eligible.rest
  let nodes := retainedNodes source.val [node]
  let wires := retainedWires source.val absorbed
  let joinedEndpoints :=
    incident.flatMap fun wire =>
      eraseNodeEndpoints node (source.val.wires wire).endpoints
  { regionCount := source.val.regionCount
    nodeCount := nodes.length
    wireCount := wires.length
    root := source.val.root
    regions := source.val.regions
    nodes := fun targetNode =>
      source.val.nodes (nodes.get targetNode)
    wires := fun targetWire =>
      let sourceWire := wires.get targetWire
      let data := source.val.wires sourceWire
      { sig := data.sig
        scope := data.scope
        endpoints :=
          reindexEndpoints nodes
            (if sourceWire = eligible.survivor then
              joinedEndpoints
            else
              eraseNodeEndpoints node data.endpoints) } }

/-- Raw Rule 3 candidate. Its sole consumer is the preservation proof layer. -/
def fusionCandidate
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ConcreteDiagram definitions.length :=
  let incident :=
    (source.val.identityIncidentWires left ++
      source.val.identityIncidentWires right).eraseDups
  let nodes := retainedNodes source.val [right]
  let wires := source.val.wiresList
  { regionCount := source.val.regionCount
    nodeCount := nodes.length
    wireCount := wires.length
    root := source.val.root
    regions := source.val.regions
    nodes := fun targetNode =>
      let sourceNode := nodes.get targetNode
      if sourceNode = left then
        .identity eligible.leftIdentity.region
          eligible.leftIdentity.signature incident.length
      else
        source.val.nodes sourceNode
    wires := fun targetWire =>
      let sourceWire := wires.get targetWire
      let data := source.val.wires sourceWire
      let retainedEndpoints :=
        reindexEndpoints nodes
          (eraseTwoNodeEndpoints left right data.endpoints)
      let identityEndpoint : List (CEndpoint nodes.length) :=
        match Data.Finite.indexOf? nodes left,
            Data.Finite.indexOf? incident sourceWire with
        | some targetNode, some port =>
            [⟨targetNode, .identity port.val⟩]
        | _, _ => []
      { sig := data.sig
        scope := data.scope
        endpoints := retainedEndpoints ++ identityEndpoint } }

end IdentityNormalizationCore

end ConcreteDiagram

end VisualProof
