import VisualProof.Diagram.Concrete.WellFormed
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

namespace ConcreteWireQuantifier

/-- Concrete construction failures owned below the rule-policy boundary. -/
inductive Error
  | expectedIota (wire : Nat)
  | expectedRelation (wire : Nat)
  | sameWire
  | invalidEndpointPartition
  | emptyRelationSites
  | overlappingRemoval
  | invalidRemoval
  | removedRoot
  | removedScope
  | removedSite
  | removedFormal (wire : Nat)
  | relationSignatureMismatch
  | boundaryArityMismatch
  | boundarySignatureMismatch (position : Nat)
  | dyingWireParameter
  | nonAppliedEndpoint (node : Nat) (port : CPort)
  | invalidApplication (node : Nat)
  | invalidAttachment
  | wellFormed (error : WFError)
  deriving Repr, DecidableEq


namespace Internal

def retainedRegions
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId) :
    List source.val.RegionId :=
  source.val.regionsList.filter fun region =>
    decide (region ∉ removed)

def retainedNodes
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (node ∉ removed)

def retainedWires
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun wire =>
    decide (wire ∉ removed)

/--
The complete structural evidence needed to densely remove a batch without a
repair fallback.  Only the executable checker below can construct this plan.
-/
structure BatchRemovalPlan
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) : Type where
  rootRetained :
    source.val.root ∈ retainedRegions source removedRegions
  parentRetained :
    ∀ target : Fin (retainedRegions source removedRegions).length,
      match source.val.regions
          ((retainedRegions source removedRegions).get target) with
      | .sheet => True
      | .cut parent =>
          parent ∈ retainedRegions source removedRegions
  nodeRegionRetained :
    ∀ target : Fin (retainedNodes source removedNodes).length,
      (source.val.nodes
          ((retainedNodes source removedNodes).get target)).region ∈
        retainedRegions source removedRegions
  wireScopeRetained :
    ∀ target : Fin (retainedWires source removedWires).length,
      (source.val.wires
          ((retainedWires source removedWires).get target)).scope ∈
        retainedRegions source removedRegions

def checkBatchRemovalPlan?
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    Option
      (BatchRemovalPlan source removedRegions removedNodes removedWires) := by
  if rootRetained :
      source.val.root ∈ retainedRegions source removedRegions then
    if parentRetained :
        (retainedRegions source removedRegions).all (fun region =>
          match source.val.regions region with
          | .sheet => true
          | .cut parent =>
              decide (parent ∈ retainedRegions source removedRegions)) =
            true then
      if nodeRegionRetained :
          (retainedNodes source removedNodes).all (fun node =>
            decide (
              (source.val.nodes node).region ∈
                retainedRegions source removedRegions)) = true then
        if wireScopeRetained :
            (retainedWires source removedWires).all (fun wire =>
              decide (
                (source.val.wires wire).scope ∈
                  retainedRegions source removedRegions)) = true then
          exact some
            { rootRetained := rootRetained
              parentRetained := by
                intro target
                have accepted :=
                  (List.all_eq_true.mp parentRetained)
                    ((retainedRegions source removedRegions).get target)
                    (List.get_mem _ target)
                cases regionData :
                    source.val.regions
                      ((retainedRegions source removedRegions).get target) with
                | sheet => trivial
                | cut parent =>
                    rw [regionData] at accepted
                    exact of_decide_eq_true accepted
              nodeRegionRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp nodeRegionRetained)
                    ((retainedNodes source removedNodes).get target)
                    (List.get_mem _ target))
              wireScopeRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp wireScopeRetained)
                    ((retainedWires source removedWires).get target)
                    (List.get_mem _ target)) }
        else
          exact none
      else
        exact none
    else
      exact none
  else
    exact none

def retainedRegionIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : source.val.RegionId)
    (member : region ∈ retainedRegions source removed) :
    Fin (retainedRegions source removed).length :=
  DenseList.index (retainedRegions source removed) region member

def retainedNodeIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : source.val.NodeId)
    (member : node ∈ retainedNodes source removed) :
    Fin (retainedNodes source removed).length :=
  DenseList.index (retainedNodes source removed) node member

def retainedWireIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : source.val.WireId)
    (member : wire ∈ retainedWires source removed) :
    Fin (retainedWires source removed).length :=
  DenseList.index (retainedWires source removed) wire member

def sourceRetainedRegion
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : Fin (retainedRegions source removed).length) :
    source.val.RegionId :=
  (retainedRegions source removed).get region

def sourceRetainedNode
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : Fin (retainedNodes source removed).length) :
    source.val.NodeId :=
  (retainedNodes source removed).get node

def sourceRetainedWire
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : Fin (retainedWires source removed).length) :
    source.val.WireId :=
  (retainedWires source removed).get wire

private theorem batchParentRetained
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length)
    (parent : source.val.RegionId)
    (regionData :
      source.val.regions
          (sourceRetainedRegion source removedRegions region) =
        .cut parent) :
    parent ∈ retainedRegions source removedRegions := by
  have retained := plan.parentRetained region
  have same :
      source.val.regions
          ((retainedRegions source removedRegions).get region) =
        .cut parent := by
    simpa [sourceRetainedRegion] using regionData
  rw [same] at retained
  exact retained

def batchRegionTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length) :
    CRegion (retainedRegions source removedRegions).length :=
  match regionData : source.val.regions
      (sourceRetainedRegion source removedRegions region) with
  | .sheet => .sheet
  | .cut parent =>
      .cut
        (retainedRegionIndex source removedRegions parent
          (batchParentRetained plan region parent regionData))

def batchNodeTable
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (node : Fin (retainedNodes source removedNodes).length) :
    CNode (retainedRegions source removedRegions).length definitions.length :=
  let sourceNode := sourceRetainedNode source removedNodes node
  let region :=
    retainedRegionIndex source removedRegions
      (source.val.nodes sourceNode).region
      (plan.nodeRegionRetained node)
  match source.val.nodes sourceNode with
  | .atom _ args => .atom region args
  | .ref _ definition args => .ref region definition args
  | .identity _ sig arity => .identity region sig arity

def batchEndpoint?
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (CEndpoint (retainedNodes source removedNodes).length) :=
  if retained : endpoint.node ∈ retainedNodes source removedNodes then
    some
      { node :=
          retainedNodeIndex source removedNodes endpoint.node retained
        port := endpoint.port }
  else
    none

def batchWireTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (wire : Fin (retainedWires source removedWires).length) :
    CWire
      (retainedRegions source removedRegions).length
      (retainedNodes source removedNodes).length :=
  let sourceWire := sourceRetainedWire source removedWires wire
  let data := source.val.wires sourceWire
  { sig := data.sig
    scope :=
      retainedRegionIndex source removedRegions data.scope
        (plan.wireScopeRetained wire)
    endpoints := data.endpoints.filterMap
      (batchEndpoint? source removedNodes) }

def batchRemovalCandidate
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    ConcreteDiagram definitions.length where
  regionCount := (retainedRegions source removedRegions).length
  nodeCount := (retainedNodes source removedNodes).length
  wireCount := (retainedWires source removedWires).length
  root :=
    retainedRegionIndex source removedRegions source.val.root
      plan.rootRetained
  regions := batchRegionTable plan
  nodes := batchNodeTable plan
  wires := batchWireTable plan

def checkedRegion
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.RegionId :=
  Fin.cast
    (congrArg ConcreteDiagram.regionCount generated).symm region

end Internal

theorem checkedRegion_injective
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    {left right : candidate.RegionId}
    (same :
      Internal.checkedRegion generated left = Internal.checkedRegion generated right) :
    left = right := by
  unfold Internal.checkedRegion at same
  apply Fin.ext
  simpa using congrArg Fin.val same

namespace Internal

theorem checkedRegion_encloses
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (outer inner : candidate.RegionId) :
    checked.val.Encloses
        (checkedRegion generated outer) (checkedRegion generated inner) ↔
      candidate.Encloses outer inner := by
  cases generated
  rfl

def checkedNode
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.NodeId :=
  Fin.cast
    (congrArg ConcreteDiagram.nodeCount generated).symm node

def checkedWire
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount generated).symm wire

theorem checkedWire_signature_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).sig =
      (candidate.wires wire).sig := by
  subst candidate
  rfl

def checkedEndpoint
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (endpoint : CEndpoint candidate.nodeCount) :
    CEndpoint checked.val.nodeCount :=
  { node := checkedNode generated endpoint.node
    port := endpoint.port }

theorem checkedWire_scope_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).scope =
      checkedRegion generated (candidate.wires wire).scope := by
  subst candidate
  rfl

theorem checkedWire_endpoints_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).endpoints =
      (candidate.wires wire).endpoints.map
        (checkedEndpoint generated) := by
  cases generated
  unfold checkedWire checkedEndpoint checkedNode
  simp

def checkedNodeData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CNode candidate.regionCount definitions.length →
      CNode checked.val.regionCount definitions.length
  | .atom region args =>
      .atom (checkedRegion generated region) args
  | .ref region definition args =>
      .ref (checkedRegion generated region) definition args
  | .identity region sig arity =>
      .identity (checkedRegion generated region) sig arity

private def checkedRegionData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CRegion candidate.regionCount → CRegion checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (checkedRegion generated parent)

theorem checkedRoot_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    checked.val.root = checkedRegion generated candidate.root := by
  cases generated
  rfl

theorem checkedRegion_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.regions (checkedRegion generated region) =
      checkedRegionData generated (candidate.regions region) := by
  cases generated
  cases data : checked.val.regions region <;>
    simp [checkedRegion, checkedRegionData, data]

theorem checkedNode_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.nodes (checkedNode generated node) =
      checkedNodeData generated (candidate.nodes node) := by
  cases generated
  cases data : checked.val.nodes node <;>
    simp [checkedNode, checkedNodeData, checkedRegion, data]

end Internal

end ConcreteWireQuantifier

end VisualProof
