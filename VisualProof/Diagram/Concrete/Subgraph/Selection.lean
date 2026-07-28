import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof

namespace CheckedSelection

/-- A wire touches the selected content when one of its stored endpoints is on
one of the selected nodes. -/
def endpointTouchesNodes
    (host : CheckedDiagram definitions)
    (nodes : List host.val.NodeId)
    (wire : host.val.WireId) : Prop :=
  ∃ endpoint ∈ (host.val.wires wire).endpoints, endpoint.node ∈ nodes

instance (host : CheckedDiagram definitions)
    (nodes : List host.val.NodeId) (wire : host.val.WireId) :
    Decidable (endpointTouchesNodes host nodes wire) := by
  unfold endpointTouchesNodes
  infer_instance

end CheckedSelection

/--
A caller-supplied closed concrete selection. The fields are validation evidence,
not a search recipe: selected regions contain their complete descendant
subtrees, selected nodes are exactly those homed there, and selected wires are
exactly internally scoped or incident wires.
-/
structure CheckedSelection (host : CheckedDiagram definitions) where
  root : host.val.RegionId
  regions : List host.val.RegionId
  nodes : List host.val.NodeId
  wires : List host.val.WireId
  regions_nodup : regions.Nodup
  nodes_nodup : nodes.Nodup
  wires_nodup : wires.Nodup
  root_mem : root ∈ regions
  host_root_retained :
    host.val.root ∉ regions ∨ host.val.root = root
  root_parent_external :
    ∀ parent, host.val.regions root = .cut parent → parent ∉ regions
  below_root :
    ∀ region, region ∈ regions → host.val.Encloses root region
  descendants_closed :
    ∀ region, region ∈ regions → ∀ child,
      child ∈ host.val.childrenOf region → child ∈ regions
  nodes_exact :
    ∀ node, node ∈ nodes ↔ (host.val.nodes node).region ∈ regions
  wires_exact :
    ∀ wire, wire ∈ wires ↔
      (host.val.wires wire).scope ∈ regions ∨
        CheckedSelection.endpointTouchesNodes host nodes wire

namespace CheckedSelection

/-- A selected wire is internal exactly when its quantifier scope is selected. -/
def IsInternal (selection : CheckedSelection host)
    (wire : host.val.WireId) : Prop :=
  wire ∈ selection.wires ∧ (host.val.wires wire).scope ∈ selection.regions

/-- A selected wire touching selected content but quantified outside is boundary. -/
def IsBoundary (selection : CheckedSelection host)
    (wire : host.val.WireId) : Prop :=
  wire ∈ selection.wires ∧
    (host.val.wires wire).scope ∉ selection.regions

/--
A boundary crossing is a real stored incidence whose node is selected while
the incident wire is quantified outside the selected region carrier.
-/
def IsBoundaryCrossing (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (endpoint : CEndpoint host.val.nodeCount) : Prop :=
  wire ∈ selection.wires ∧
    endpoint ∈ (host.val.wires wire).endpoints ∧
    endpoint.node ∈ selection.nodes ∧
    (host.val.wires wire).scope ∉ selection.regions

instance (selection : CheckedSelection host) (wire : host.val.WireId) :
    Decidable (selection.IsInternal wire) := by
  unfold IsInternal
  infer_instance

instance (selection : CheckedSelection host) (wire : host.val.WireId) :
    Decidable (selection.IsBoundary wire) := by
  unfold IsBoundary
  infer_instance

instance (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (endpoint : CEndpoint host.val.nodeCount) :
    Decidable (selection.IsBoundaryCrossing wire endpoint) := by
  unfold IsBoundaryCrossing
  infer_instance

/-- The finite subtype of actual host incidences crossing this selection. -/
abbrev BoundaryCrossing (selection : CheckedSelection host) : Type :=
  { crossing : host.val.WireId × CEndpoint host.val.nodeCount //
      selection.IsBoundaryCrossing crossing.1 crossing.2 }

instance (selection : CheckedSelection host) :
    DecidableEq (BoundaryCrossing selection) :=
  inferInstance

namespace BoundaryCrossing

def wire {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) : host.val.WireId :=
  crossing.val.1

def endpoint {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) :
    CEndpoint host.val.nodeCount :=
  crossing.val.2

theorem wire_selected {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) :
    crossing.wire ∈ selection.wires :=
  crossing.property.1

theorem incident {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) :
    crossing.endpoint ∈ (host.val.wires crossing.wire).endpoints :=
  crossing.property.2.1

theorem node_selected {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) :
    crossing.endpoint.node ∈ selection.nodes :=
  crossing.property.2.2.1

theorem scope_external {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    (crossing : BoundaryCrossing selection) :
    (host.val.wires crossing.wire).scope ∉ selection.regions :=
  crossing.property.2.2.2

end BoundaryCrossing

/-- Distinct boundary wire classes in the caller's stable selected-wire order. -/
def boundaryClasses (selection : CheckedSelection host) :
    List host.val.WireId :=
  selection.wires.filter fun wire => decide (selection.IsBoundary wire)

theorem boundaryClasses_nodup (selection : CheckedSelection host) :
    selection.boundaryClasses.Nodup :=
  selection.wires_nodup.filter _

theorem internal_wire_selected (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (scope : (host.val.wires wire).scope ∈ selection.regions) :
    wire ∈ selection.wires :=
  (selection.wires_exact wire).mpr (.inl scope)

theorem incident_wire_selected (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (touches : endpointTouchesNodes host selection.nodes wire) :
    wire ∈ selection.wires :=
  (selection.wires_exact wire).mpr (.inr touches)

theorem selected_node_region (selection : CheckedSelection host)
    {node : host.val.NodeId} (selected : node ∈ selection.nodes) :
    (host.val.nodes node).region ∈ selection.regions :=
  (selection.nodes_exact node).mp selected

theorem selected_of_climb (selection : CheckedSelection host)
    {ancestor : host.val.RegionId}
    (ancestorSelected : ancestor ∈ selection.regions) :
    ∀ steps descendant,
      host.val.climb steps descendant = some ancestor →
        descendant ∈ selection.regions := by
  intro steps
  induction steps with
  | zero =>
      intro descendant reaches
      simp only [ConcreteDiagram.climb] at reaches
      rw [Option.some.inj reaches]
      exact ancestorSelected
  | succ steps ih =>
      intro descendant reaches
      cases regionData : host.val.regions descendant with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at reaches
      | cut parent =>
          have parentSelected : parent ∈ selection.regions :=
            ih parent (by
              simpa [ConcreteDiagram.climb, regionData] using reaches)
          apply selection.descendants_closed parent parentSelected descendant
          simp [ConcreteDiagram.childrenOf, ConcreteDiagram.regionsList,
            Data.Finite.mem_allFin, regionData]

theorem selected_of_encloses (selection : CheckedSelection host)
    {ancestor descendant : host.val.RegionId}
    (ancestorSelected : ancestor ∈ selection.regions)
    (encloses : host.val.Encloses ancestor descendant) :
    descendant ∈ selection.regions := by
  unfold ConcreteDiagram.Encloses at encloses
  rw [List.any_eq_true] at encloses
  rcases encloses with ⟨steps, _, reaches⟩
  exact selection.selected_of_climb ancestorSelected steps descendant
    (eq_of_beq reaches)

theorem internal_endpoint_selected
    (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (endpoint : CEndpoint host.val.nodeCount)
    (internal : (host.val.wires wire).scope ∈ selection.regions)
    (incident : endpoint ∈ (host.val.wires wire).endpoints) :
    endpoint.node ∈ selection.nodes := by
  have occurrenceMember :
      (wire, endpoint) ∈ host.val.endpointOccurrences := by
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  have enclosed :
      host.val.Encloses (host.val.wires wire).scope
        (host.val.nodes endpoint.node).region :=
    of_decide_eq_true
      ((List.all_eq_true.mp host.property.wire_scopes_enclose)
        (wire, endpoint) occurrenceMember)
  exact (selection.nodes_exact endpoint.node).mpr
    (selection.selected_of_encloses internal enclosed)

end CheckedSelection

end VisualProof
