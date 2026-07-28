import VisualProof.Diagram.Concrete.IdentityIncidence

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

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
    source.val.identityIncidentWires node =
      survivor :: second :: rest
  coScoped :
    ∀ wire, wire ∈ source.val.identityIncidentWires node →
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
          source.val.identityIncidentWires node with
      | survivor :: second :: rest =>
          if coScoped :
              ∀ wire,
                wire ∈ source.val.identityIncidentWires node →
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
                coScoped := coScoped }
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

def identityNodeIds
    (diagram : ConcreteDiagram definitionCount) :
    List diagram.NodeId :=
  diagram.nodesList.filter fun node =>
    match diagram.nodes node with
    | .identity _ _ _ => true
    | _ => false

def retainedNodes
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.NodeId) :
    List diagram.NodeId :=
  diagram.nodesList.filter fun node => decide (node ∉ removed)

def retainedWires
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.WireId) :
    List diagram.WireId :=
  diagram.wiresList.filter fun wire => decide (wire ∉ removed)

private theorem filter_length_lt_of_mem_rejected
    (values : List α)
    (predicate : α → Bool)
    (value : α)
    (member : value ∈ values)
    (rejected : predicate value = false) :
    (values.filter predicate).length < values.length := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [List.filter_cons]
      split
      · rename_i accepted
        have headNe : value ≠ head := by
          intro equality
          subst head
          simp [rejected] at accepted
        have tailMember : value ∈ tail := member.resolve_left headNe
        simpa using Nat.succ_lt_succ (ih tailMember)
      · exact Nat.lt_succ_of_le (List.length_filter_le predicate tail)

/-- Removing a named node strictly decreases the concrete node carrier. -/
theorem retainedNodes_singleton_length_lt
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) :
    (retainedNodes diagram [node]).length < diagram.nodeCount := by
  have strict :=
    filter_length_lt_of_mem_rejected diagram.nodesList
      (fun candidate => decide (candidate ∉ [node]))
      node (Data.Finite.mem_allFin node) (by simp)
  simpa [retainedNodes, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange] using strict

def reindexEndpoint?
    {source : ConcreteDiagram definitionCount}
    (nodes : List source.NodeId)
    (endpoint : CEndpoint source.nodeCount) :
    Option (CEndpoint nodes.length) :=
  (Data.Finite.indexOf? nodes endpoint.node).map fun node =>
    ⟨node, endpoint.port⟩

def reindexEndpoints
    {source : ConcreteDiagram definitionCount}
    (nodes : List source.NodeId)
    (endpoints : List (CEndpoint source.nodeCount)) :
    List (CEndpoint nodes.length) :=
  endpoints.filterMap (reindexEndpoint? nodes)

def eraseNodeEndpoints
    {source : ConcreteDiagram definitionCount}
    (node : source.NodeId)
    (endpoints : List (CEndpoint source.nodeCount)) :
    List (CEndpoint source.nodeCount) :=
  endpoints.filter fun endpoint => decide (endpoint.node ≠ node)

def eraseTwoNodeEndpoints
    {source : ConcreteDiagram definitionCount}
    (left right : source.NodeId)
    (endpoints : List (CEndpoint source.nodeCount)) :
    List (CEndpoint source.nodeCount) :=
  endpoints.filter fun endpoint =>
    decide (endpoint.node ≠ left ∧ endpoint.node ≠ right)

/-- Raw Rule 1 candidate. Its sole consumer is the preservation proof layer. -/
def dropCandidate
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (_eligible : DropEligibility source node) :
    ConcreteDiagram definitions.length :=
  let nodes := retainedNodes source.val [node]
  let wires := source.val.wiresList
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
            (eraseNodeEndpoints node data.endpoints) } }

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
