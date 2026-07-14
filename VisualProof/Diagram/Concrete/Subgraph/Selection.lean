import VisualProof.Data.Finite
import VisualProof.Diagram.Concrete.Core

namespace VisualProof.Diagram

/--
A proof-free request for a subdiagram anchored at one concrete region.

Only whole direct-child subtrees, direct nodes, and explicitly designated
anchor-scoped wires are caller choices. Closure data is derived, never supplied.
-/
structure SelectionRequest (d : ConcreteDiagram) where
  anchor : Fin d.regionCount
  childRoots : List (Fin d.regionCount)
  directNodes : List (Fin d.nodeCount)
  explicitWires : List (Fin d.wireCount)

namespace SelectionRequest

/-- A region belongs to one of the requested direct-child subtrees. -/
def SelectsRegion (request : SelectionRequest d)
    (region : Fin d.regionCount) : Prop :=
  ∃ root, root ∈ request.childRoots ∧ d.Encloses root region

instance (request : SelectionRequest d) (region : Fin d.regionCount) :
    Decidable (request.SelectsRegion region) := by
  unfold SelectsRegion
  infer_instance

/--
The node predicate used while validating explicit wires. It is the closure of
the requested direct nodes under ownership by a selected child subtree.
-/
def SelectsNode (request : SelectionRequest d)
    (node : Fin d.nodeCount) : Prop :=
  node ∈ request.directNodes ∨
    request.SelectsRegion (d.nodes node).region

instance (request : SelectionRequest d) (node : Fin d.nodeCount) :
    Decidable (request.SelectsNode node) := by
  unfold SelectsNode
  infer_instance

/-- The exact declarative admissibility conditions for a selection request. -/
structure Valid (request : SelectionRequest d) : Prop where
  childRoots_nodup : request.childRoots.Nodup
  childRoots_direct : ∀ region, region ∈ request.childRoots →
    (d.regions region).parent? = some request.anchor
  directNodes_nodup : request.directNodes.Nodup
  directNodes_at_anchor : ∀ node, node ∈ request.directNodes →
    (d.nodes node).region = request.anchor
  explicitWires_nodup : request.explicitWires.Nodup
  explicitWires_at_anchor : ∀ wire, wire ∈ request.explicitWires →
    (d.wires wire).scope = request.anchor
  explicitWireEndpoints_selected : ∀ wire, wire ∈ request.explicitWires →
    ∀ endpoint, endpoint ∈ (d.wires wire).endpoints →
      request.SelectsNode endpoint.node

end SelectionRequest

/-- A valid operation input, distinct from whole-diagram well-formedness. -/
abbrev CheckedSelection (d : ConcreteDiagram) :=
  { request : SelectionRequest d // request.Valid }

namespace CheckedSelection

open VisualProof.Data.Finite

/-- Canonical enumeration of all regions in the selected child subtrees. -/
def selectedRegions (selection : CheckedSelection d) :
    List (Fin d.regionCount) :=
  filterFin fun region => decide (selection.val.SelectsRegion region)

/-- Canonical enumeration of direct and subtree-owned selected nodes. -/
def selectedNodes (selection : CheckedSelection d) :
    List (Fin d.nodeCount) :=
  filterFin fun node => decide (selection.val.SelectsNode node)

/--
Canonical enumeration of wires owned by the selection. Selected endpoint
incidence alone is intentionally absent from this predicate.
-/
def internalWires (selection : CheckedSelection d) :
    List (Fin d.wireCount) :=
  filterFin fun wire => decide
    (selection.val.SelectsRegion (d.wires wire).scope ∨
      wire ∈ selection.val.explicitWires)

/-- Canonical enumeration of noninternal wires incident to selected nodes. -/
def touchingWires (selection : CheckedSelection d) :
    List (Fin d.wireCount) :=
  filterFin fun wire => decide
    (¬ (selection.val.SelectsRegion (d.wires wire).scope ∨
        wire ∈ selection.val.explicitWires) ∧
      ∃ endpoint, endpoint ∈ (d.wires wire).endpoints ∧
        selection.val.SelectsNode endpoint.node)

@[simp] theorem mem_selectedRegions (selection : CheckedSelection d)
    (region : Fin d.regionCount) :
    region ∈ selection.selectedRegions ↔
      selection.val.SelectsRegion region := by
  simp [selectedRegions]

@[simp] theorem mem_selectedNodes (selection : CheckedSelection d)
    (node : Fin d.nodeCount) :
    node ∈ selection.selectedNodes ↔ selection.val.SelectsNode node := by
  simp [selectedNodes]

@[simp] theorem mem_internalWires (selection : CheckedSelection d)
    (wire : Fin d.wireCount) :
    wire ∈ selection.internalWires ↔
      selection.val.SelectsRegion (d.wires wire).scope ∨
        wire ∈ selection.val.explicitWires := by
  simp [internalWires]

@[simp] theorem mem_touchingWires (selection : CheckedSelection d)
    (wire : Fin d.wireCount) :
    wire ∈ selection.touchingWires ↔
      ¬ (selection.val.SelectsRegion (d.wires wire).scope ∨
          wire ∈ selection.val.explicitWires) ∧
        ∃ endpoint, endpoint ∈ (d.wires wire).endpoints ∧
          selection.val.SelectsNode endpoint.node := by
  simp [touchingWires]

theorem selectedRegions_nodup (selection : CheckedSelection d) :
    selection.selectedRegions.Nodup :=
  filterFin_nodup _

theorem selectedNodes_nodup (selection : CheckedSelection d) :
    selection.selectedNodes.Nodup :=
  filterFin_nodup _

theorem internalWires_nodup (selection : CheckedSelection d) :
    selection.internalWires.Nodup :=
  filterFin_nodup _

theorem touchingWires_nodup (selection : CheckedSelection d) :
    selection.touchingWires.Nodup :=
  filterFin_nodup _

theorem explicitWire_mem_internalWires (selection : CheckedSelection d)
    {wire : Fin d.wireCount} (hexplicit : wire ∈ selection.val.explicitWires) :
    wire ∈ selection.internalWires :=
  (selection.mem_internalWires wire).2 (Or.inr hexplicit)

theorem selectedScope_mem_internalWires (selection : CheckedSelection d)
    {wire : Fin d.wireCount}
    (hscope : selection.val.SelectsRegion (d.wires wire).scope) :
    wire ∈ selection.internalWires :=
  (selection.mem_internalWires wire).2 (Or.inl hscope)

theorem mem_touchingWires_consequences (selection : CheckedSelection d)
    {wire : Fin d.wireCount} (htouching : wire ∈ selection.touchingWires) :
    wire ∉ selection.internalWires ∧
      ∃ endpoint, endpoint ∈ (d.wires wire).endpoints ∧
        endpoint.node ∈ selection.selectedNodes := by
  obtain ⟨hnotInternal, endpoint, hendpoint, hselected⟩ :=
    (selection.mem_touchingWires wire).1 htouching
  constructor
  · intro hinternal
    exact hnotInternal ((selection.mem_internalWires wire).1 hinternal)
  · exact ⟨endpoint, hendpoint,
      (selection.mem_selectedNodes endpoint.node).2 hselected⟩

theorem internalWires_touchingWires_disjoint
    (selection : CheckedSelection d) :
    ∀ wire, wire ∈ selection.internalWires →
      wire ∉ selection.touchingWires := by
  intro wire hinternal htouching
  exact (selection.mem_touchingWires_consequences htouching).1 hinternal

theorem explicitWire_endpoint_selected (selection : CheckedSelection d)
    {wire : Fin d.wireCount} (hexplicit : wire ∈ selection.val.explicitWires)
    {endpoint : CEndpoint d.nodeCount}
    (hendpoint : endpoint ∈ (d.wires wire).endpoints) :
    endpoint.node ∈ selection.selectedNodes := by
  apply (selection.mem_selectedNodes endpoint.node).2
  exact selection.property.explicitWireEndpoints_selected wire hexplicit
    endpoint hendpoint

end CheckedSelection

/-- The first exact selection-input condition rejected by `checkSelection`. -/
inductive SelectionError
  | duplicateChildRoot
  | childRootNotDirect
  | duplicateDirectNode
  | directNodeNotAtAnchor
  | duplicateExplicitWire
  | explicitWireNotAtAnchor
  | explicitWireEndpointOutside
  deriving DecidableEq

/-- Decide the declarative selection-input contract with structured failure. -/
def checkSelection (request : SelectionRequest d) :
    Except SelectionError (CheckedSelection d) :=
  if hchildNodup : request.childRoots.Nodup then
    if hchildDirect : ∀ region, region ∈ request.childRoots →
        (d.regions region).parent? = some request.anchor then
      if hnodeNodup : request.directNodes.Nodup then
        if hnodeDirect : ∀ node, node ∈ request.directNodes →
            (d.nodes node).region = request.anchor then
          if hwireNodup : request.explicitWires.Nodup then
            if hwireScope : ∀ wire, wire ∈ request.explicitWires →
                (d.wires wire).scope = request.anchor then
              if hendpoints : ∀ wire, wire ∈ request.explicitWires →
                  ∀ endpoint, endpoint ∈ (d.wires wire).endpoints →
                    request.SelectsNode endpoint.node then
                .ok ⟨request, {
                  childRoots_nodup := hchildNodup
                  childRoots_direct := hchildDirect
                  directNodes_nodup := hnodeNodup
                  directNodes_at_anchor := hnodeDirect
                  explicitWires_nodup := hwireNodup
                  explicitWires_at_anchor := hwireScope
                  explicitWireEndpoints_selected := hendpoints
                }⟩
              else .error .explicitWireEndpointOutside
            else .error .explicitWireNotAtAnchor
          else .error .duplicateExplicitWire
        else .error .directNodeNotAtAnchor
      else .error .duplicateDirectNode
    else .error .childRootNotDirect
  else .error .duplicateChildRoot

theorem checkSelection_preserves_input
    (hcheck : checkSelection request = .ok checked) :
    checked.val = request := by
  unfold checkSelection at hcheck
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  · cases hcheck
    rfl
  all_goals contradiction

theorem checkSelection_sound
    (hcheck : checkSelection request = .ok checked) : request.Valid := by
  rw [← checkSelection_preserves_input hcheck]
  exact checked.property

theorem checkSelection_complete (hvalid : request.Valid) :
    checkSelection request = .ok ⟨request, hvalid⟩ := by
  unfold checkSelection
  simp only [dif_pos hvalid.childRoots_nodup,
    dif_pos hvalid.childRoots_direct,
    dif_pos hvalid.directNodes_nodup,
    dif_pos hvalid.directNodes_at_anchor,
    dif_pos hvalid.explicitWires_nodup,
    dif_pos hvalid.explicitWires_at_anchor,
    dif_pos hvalid.explicitWireEndpoints_selected]

theorem checkSelection_accepts_iff :
    (∃ checked, checkSelection request = .ok checked) ↔ request.Valid := by
  constructor
  · rintro ⟨checked, hcheck⟩
    exact checkSelection_sound hcheck
  · intro hvalid
    exact ⟨⟨request, hvalid⟩, checkSelection_complete hvalid⟩

end VisualProof.Diagram
