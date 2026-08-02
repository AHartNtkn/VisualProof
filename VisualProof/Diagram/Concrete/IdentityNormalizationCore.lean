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

/--
Raw dense deletion of one node while retaining every region and wire.
Well-formedness is intentionally separate: identity normalization proves it
from Rule-1 eligibility, while other checked structural owners may retain an
independently checked candidate.
-/
@[reducible] def eraseNodeCandidate
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
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

/--
Raw dense deletion of one wire while retaining every region, node, and all
data of the other wires.  Well-formedness remains the responsibility of the
checked structural owner that produced the deletion.
-/
def eraseWireCandidate
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    ConcreteDiagram definitions.length :=
  let regions :=
    source.val.regionsList.filter fun region =>
      decide (region ∉ ([] : List source.val.RegionId))
  let nodes :=
    source.val.nodesList.filter fun node =>
      decide (node ∉ ([] : List source.val.NodeId))
  let wires :=
    retainedWires source.val [removed]
  let regionIndex (region : source.val.RegionId)
      (member : region ∈ regions) : Fin regions.length :=
    (Data.Finite.indexOf? regions region).get
      (Data.Finite.indexOf?_isSome_iff.mpr member)
  let nodeIndex (node : source.val.NodeId)
      (member : node ∈ nodes) : Fin nodes.length :=
    (Data.Finite.indexOf? nodes node).get
      (Data.Finite.indexOf?_isSome_iff.mpr member)
  let endpoint? (endpoint : CEndpoint source.val.nodeCount) :
      Option (CEndpoint nodes.length) :=
    if retained : endpoint.node ∈ nodes then
      some ⟨nodeIndex endpoint.node retained, endpoint.port⟩
    else
      none
  { regionCount := regions.length
    nodeCount := nodes.length
    wireCount := wires.length
    root :=
      regionIndex source.val.root (by
        simp [regions, ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin])
    regions := fun target =>
      match source.val.regions (regions.get target) with
      | .sheet => .sheet
      | .cut parent =>
          .cut
            (regionIndex parent (by
              simp [regions, ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin]))
    nodes := fun target =>
      let sourceNode := nodes.get target
      let region :=
        regionIndex (source.val.nodes sourceNode).region (by
          simp [regions, ConcreteDiagram.regionsList,
            Data.Finite.mem_allFin])
      match source.val.nodes sourceNode with
      | .atom _ args => .atom region args
      | .ref _ definition args => .ref region definition args
      | .identity _ sig arity => .identity region sig arity
    wires := fun target =>
      let sourceWire := wires.get target
      let data := source.val.wires sourceWire
      { sig := data.sig
        scope :=
          regionIndex data.scope (by
            simp [regions, ConcreteDiagram.regionsList,
              Data.Finite.mem_allFin])
        endpoints := data.endpoints.filterMap endpoint? } }

/-- Count-preserving region image into a raw singleton-node deletion. -/
def eraseNodeRegion
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) :
    (eraseNodeCandidate source node).RegionId :=
  ⟨region.val, by
    simpa [eraseNodeCandidate] using region.isLt⟩

theorem eraseNodeRegion_injective
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Function.Injective (eraseNodeRegion source node) := by
  intro left right same
  apply Fin.ext
  exact congrArg Fin.val same

/-- Singleton-node deletion preserves sheet-region data exactly. -/
theorem eraseNodeRegion_sheet
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId)
    (data : source.val.regions region = .sheet) :
    (eraseNodeCandidate source node).regions
        (eraseNodeRegion source node region) = .sheet := by
  simp [eraseNodeCandidate, eraseNodeRegion, data]

/-- Singleton-node deletion preserves cut-region data and parentage exactly. -/
theorem eraseNodeRegion_cut
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    (eraseNodeCandidate source node).regions
        (eraseNodeRegion source node region) =
      .cut (eraseNodeRegion source node parent) := by
  simp [eraseNodeCandidate, eraseNodeRegion, data]

theorem eraseNodeRegion_climb
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    ∀ (steps : Nat) (region : source.val.RegionId),
      (eraseNodeCandidate source node).climb steps
          (eraseNodeRegion source node region) =
        (source.val.climb steps region).map (eraseNodeRegion source node)
  | 0, _ => rfl
  | steps + 1, region => by
      cases data : source.val.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, eraseNodeCandidate,
            eraseNodeRegion, data]
      | cut parent =>
          simpa [ConcreteDiagram.climb, eraseNodeCandidate,
            eraseNodeRegion, data] using
            eraseNodeRegion_climb source node steps parent

theorem eraseNodeRegion_encloses_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (outer inner : source.val.RegionId) :
    (eraseNodeCandidate source node).Encloses
        (eraseNodeRegion source node outer)
        (eraseNodeRegion source node inner) ↔
      source.val.Encloses outer inner := by
  unfold ConcreteDiagram.Encloses
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨steps, member, climbed⟩
    have climbedExact :
        (eraseNodeCandidate source node).climb steps
            (eraseNodeRegion source node inner) =
          some (eraseNodeRegion source node outer) := by
      exact beq_iff_eq.mp climbed
    rw [eraseNodeRegion_climb] at climbedExact
    cases sourceClimb : source.val.climb steps inner with
    | none => simp [sourceClimb] at climbedExact
    | some reached =>
        rw [sourceClimb] at climbedExact
        have same :
            eraseNodeRegion source node reached =
              eraseNodeRegion source node outer :=
          Option.some.inj climbedExact
        refine ⟨steps, ?_, ?_⟩
        · simpa [eraseNodeCandidate] using member
        · apply beq_iff_eq.mpr
          exact sourceClimb.trans
            (congrArg some
              (eraseNodeRegion_injective source node same))
  · rintro ⟨steps, member, climbed⟩
    refine ⟨steps, ?_, ?_⟩
    · simpa [eraseNodeCandidate] using member
    · apply beq_iff_eq.mpr
      rw [eraseNodeRegion_climb]
      exact congrArg (Option.map (eraseNodeRegion source node))
        (beq_iff_eq.mp climbed)

/-- Count-preserving wire image into a raw singleton-node deletion. -/
def eraseNodeWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (wire : source.val.WireId) :
    (eraseNodeCandidate source node).WireId :=
  ⟨wire.val, by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, wire.isLt]⟩

theorem eraseNodeWire_injective
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Function.Injective (eraseNodeWire source node) := by
  intro left right same
  apply Fin.ext
  exact congrArg (fun value => value.val) same

@[simp] theorem eraseNodeWire_signature
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    ((eraseNodeCandidate source removed).wires
      (eraseNodeWire source removed wire)).sig =
      (source.val.wires wire).sig := by
  change
    (source.val.wires
      (source.val.wiresList.get
        (eraseNodeWire source removed wire))).sig =
      (source.val.wires wire).sig
  congr 2
  apply Fin.ext
  simp [eraseNodeWire, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange]

@[simp] theorem eraseNodeWire_scope
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    ((eraseNodeCandidate source removed).wires
      (eraseNodeWire source removed wire)).scope =
      (source.val.wires wire).scope := by
  change
    (source.val.wires
      (source.val.wiresList.get
        (eraseNodeWire source removed wire))).scope =
      (source.val.wires wire).scope
  congr 2
  apply Fin.ext
  simp [eraseNodeWire, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange]

/-- Dense image of one retained node in a raw singleton-node deletion. -/
def eraseNodeIndex
    (source : CheckedDiagram definitions)
    (removed candidate : source.val.NodeId)
    (retained : candidate ∈ retainedNodes source.val [removed]) :
    (eraseNodeCandidate source removed).NodeId :=
  (Data.Finite.indexOf?
    (retainedNodes source.val [removed]) candidate).get
      (Data.Finite.indexOf?_isSome_iff.mpr retained)

/-- A retained node keeps its constructor and payload under singleton-node
deletion; only its region carrier is transported. -/
theorem eraseNodeIndex_data
    (source : CheckedDiagram definitions)
    (removed candidate : source.val.NodeId)
    (retained : candidate ∈ retainedNodes source.val [removed]) :
    (eraseNodeCandidate source removed).nodes
        (eraseNodeIndex source removed candidate retained) =
      (source.val.nodes candidate).relocate
        (eraseNodeRegion source removed
          (source.val.nodes candidate).region) := by
  unfold eraseNodeCandidate eraseNodeIndex
  let retainedNodesList := retainedNodes source.val [removed]
  let hsome :
      (Data.Finite.indexOf? retainedNodesList candidate).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr retained
  obtain ⟨found, foundExact⟩ := Option.isSome_iff_exists.mp hsome
  have indexed :
      retainedNodesList.get
          ((Data.Finite.indexOf? retainedNodesList candidate).get hsome) =
        candidate := by
    rw [Option.get_of_eq_some hsome foundExact]
    simpa only [List.get_eq_getElem] using
      Data.Finite.indexOf?_sound foundExact
  change source.val.nodes
      (retainedNodesList.get
        ((Data.Finite.indexOf? retainedNodesList candidate).get hsome)) = _
  rw [indexed]
  cases source.val.nodes candidate <;> rfl

/-- Dense image of an endpoint whose node survives singleton deletion. -/
def eraseNodeEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (different : endpoint.node ≠ removed) :
    CEndpoint (eraseNodeCandidate source removed).nodeCount :=
  ⟨eraseNodeIndex source removed endpoint.node (by
      simp [retainedNodes, ConcreteDiagram.nodesList,
        Data.Finite.mem_allFin, different]),
    endpoint.port⟩

/-- Every surviving endpoint remains incident to the same dense wire after
singleton deletion. -/
theorem eraseNodeEndpoint_mem
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (different : endpoint.node ≠ removed)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    eraseNodeEndpoint source removed endpoint different ∈
      ((eraseNodeCandidate source removed).wires
        (eraseNodeWire source removed wire)).endpoints := by
  have wireExact :
      source.val.wiresList.get (eraseNodeWire source removed wire) = wire := by
    apply Fin.ext
    simp [eraseNodeWire, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  change eraseNodeEndpoint source removed endpoint different ∈
    reindexEndpoints (retainedNodes source.val [removed])
      (eraseNodeEndpoints removed
        (source.val.wires
          (source.val.wiresList.get
            (eraseNodeWire source removed wire))).endpoints)
  rw [wireExact]
  unfold reindexEndpoints
  apply List.mem_filterMap.mpr
  refine ⟨endpoint, ?_, ?_⟩
  · simpa [eraseNodeEndpoints, different] using incident
  · unfold reindexEndpoint? eraseNodeEndpoint
    have foundSome :
        (Data.Finite.indexOf?
          (retainedNodes source.val [removed]) endpoint.node).isSome = true :=
      Data.Finite.indexOf?_isSome_iff.mpr (by
        simp [retainedNodes, ConcreteDiagram.nodesList,
          Data.Finite.mem_allFin, different])
    obtain ⟨index, found⟩ := Option.isSome_iff_exists.mp foundSome
    rw [found]
    simp only [Option.map_some, Option.some.injEq]
    congr 2
    exact (Option.get_of_eq_some _ found).symm


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
