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

/-- A wire is owned exactly by selected scope or explicit caller designation. -/
def SelectsWire (request : SelectionRequest d)
    (wire : Fin d.wireCount) : Prop :=
  request.SelectsRegion (d.wires wire).scope ∨
    wire ∈ request.explicitWires

instance (request : SelectionRequest d) (wire : Fin d.wireCount) :
    Decidable (request.SelectsWire wire) := by
  unfold SelectsWire
  infer_instance

/-- Componentwise inclusion of caller choices; the anchor is not closure data. -/
structure IncludedIn (first second : SelectionRequest d) : Prop where
  childRoots : ∀ {region}, region ∈ first.childRoots →
    region ∈ second.childRoots
  directNodes : ∀ {node}, node ∈ first.directNodes →
    node ∈ second.directNodes
  explicitWires : ∀ {wire}, wire ∈ first.explicitWires →
    wire ∈ second.explicitWires

theorem SelectsRegion.mono {first second : SelectionRequest d}
    (included : first.IncludedIn second) {region : Fin d.regionCount}
    (selected : first.SelectsRegion region) : second.SelectsRegion region := by
  obtain ⟨root, hroot, hencloses⟩ := selected
  exact ⟨root, included.childRoots hroot, hencloses⟩

theorem SelectsNode.mono {first second : SelectionRequest d}
    (included : first.IncludedIn second) {node : Fin d.nodeCount}
    (selected : first.SelectsNode node) : second.SelectsNode node := by
  rcases selected with hdirect | hregion
  · exact Or.inl (included.directNodes hdirect)
  · exact Or.inr (hregion.mono included)

theorem SelectsWire.mono {first second : SelectionRequest d}
    (included : first.IncludedIn second) {wire : Fin d.wireCount}
    (selected : first.SelectsWire wire) : second.SelectsWire wire := by
  rcases selected with hscope | hexplicit
  · exact Or.inl (hscope.mono included)
  · exact Or.inr (included.explicitWires hexplicit)

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
  filterFin fun wire => decide (selection.val.SelectsWire wire)

/-- Canonical enumeration of noninternal wires incident to selected nodes. -/
def touchingWires (selection : CheckedSelection d) :
    List (Fin d.wireCount) :=
  filterFin fun wire => decide
    (¬ selection.val.SelectsWire wire ∧
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
      selection.val.SelectsWire wire := by
  simp [internalWires]

theorem mem_internalWires_expanded (selection : CheckedSelection d)
    (wire : Fin d.wireCount) :
    wire ∈ selection.internalWires ↔
      selection.val.SelectsRegion (d.wires wire).scope ∨
        wire ∈ selection.val.explicitWires := by
  rw [selection.mem_internalWires]
  rfl

@[simp] theorem mem_touchingWires (selection : CheckedSelection d)
    (wire : Fin d.wireCount) :
    wire ∈ selection.touchingWires ↔
      ¬ selection.val.SelectsWire wire ∧
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

theorem selectedRegions_mono {first second : CheckedSelection d}
    (included : first.val.IncludedIn second.val) :
    ∀ {region}, region ∈ first.selectedRegions →
      region ∈ second.selectedRegions := by
  intro region hregion
  exact (second.mem_selectedRegions region).2
    ((first.mem_selectedRegions region).1 hregion |>.mono included)

theorem selectedNodes_mono {first second : CheckedSelection d}
    (included : first.val.IncludedIn second.val) :
    ∀ {node}, node ∈ first.selectedNodes → node ∈ second.selectedNodes := by
  intro node hnode
  exact (second.mem_selectedNodes node).2
    ((first.mem_selectedNodes node).1 hnode |>.mono included)

theorem internalWires_mono {first second : CheckedSelection d}
    (included : first.val.IncludedIn second.val) :
    ∀ {wire}, wire ∈ first.internalWires → wire ∈ second.internalWires := by
  intro wire hwire
  exact (second.mem_internalWires wire).2
    (((first.mem_internalWires wire).1 hwire).mono included)

/-- Internal-or-touching membership is monotone even though touching alone is not. -/
theorem wireClosure_mono {first second : CheckedSelection d}
    (included : first.val.IncludedIn second.val) {wire : Fin d.wireCount}
    (member : wire ∈ first.internalWires ∨ wire ∈ first.touchingWires) :
    wire ∈ second.internalWires ∨ wire ∈ second.touchingWires := by
  rcases member with hinternal | htouching
  · exact Or.inl (first.internalWires_mono included hinternal)
  · obtain ⟨_, endpoint, hendpoint, hselected⟩ :=
      first.mem_touchingWires_consequences htouching
    by_cases hinternal : wire ∈ second.internalWires
    · exact Or.inl hinternal
    · right
      apply (second.mem_touchingWires wire).2
      refine ⟨?_, endpoint, hendpoint, ?_⟩
      · intro hsemantic
        exact hinternal ((second.mem_internalWires wire).2 hsemantic)
      · exact (second.mem_selectedNodes endpoint.node).1
          (first.selectedNodes_mono included hselected)

/-- List-level exact form of the touching-wire predicate. -/
theorem mem_touchingWires_exact (selection : CheckedSelection d)
    (wire : Fin d.wireCount) :
    wire ∈ selection.touchingWires ↔
      wire ∉ selection.internalWires ∧
        ∃ endpoint, endpoint ∈ (d.wires wire).endpoints ∧
          endpoint.node ∈ selection.selectedNodes := by
  constructor
  · exact selection.mem_touchingWires_consequences
  · rintro ⟨hnotInternal, endpoint, hendpoint, hselected⟩
    apply (selection.mem_touchingWires wire).2
    refine ⟨?_, endpoint, hendpoint, ?_⟩
    · intro hsemantic
      exact hnotInternal ((selection.mem_internalWires wire).2 hsemantic)
    · exact (selection.mem_selectedNodes endpoint.node).1 hselected

theorem noninternal_with_selectedEndpoint_mem_touching
    (selection : CheckedSelection d) {wire : Fin d.wireCount}
    (hnotInternal : wire ∉ selection.internalWires)
    (hincidence : ∃ endpoint, endpoint ∈ (d.wires wire).endpoints ∧
      endpoint.node ∈ selection.selectedNodes) :
    wire ∈ selection.touchingWires :=
  (selection.mem_touchingWires_exact wire).2 ⟨hnotInternal, hincidence⟩

/--
Even when every endpoint is selected, an anchor-scoped wire is touching rather
than internal unless its identity or scope is selected.
-/
theorem anchorWire_allEndpointsSelected_mem_touching
    (selection : CheckedSelection d) {wire : Fin d.wireCount}
    (hscope : (d.wires wire).scope = selection.val.anchor)
    (hnotExplicit : wire ∉ selection.val.explicitWires)
    (hanchor : ¬ selection.val.SelectsRegion selection.val.anchor)
    (hnonempty : (d.wires wire).endpoints ≠ [])
    (hallSelected : ∀ endpoint, endpoint ∈ (d.wires wire).endpoints →
      endpoint.node ∈ selection.selectedNodes) :
    wire ∈ selection.touchingWires := by
  apply selection.noninternal_with_selectedEndpoint_mem_touching
  · intro hinternal
    rcases (selection.mem_internalWires_expanded wire).1 hinternal with
      hselectedScope | hexplicit
    · apply hanchor
      rwa [hscope] at hselectedScope
    · exact hnotExplicit hexplicit
  · cases hends : (d.wires wire).endpoints with
    | nil => exact False.elim (hnonempty hends)
    | cons endpoint rest =>
        have hmem : endpoint ∈ (d.wires wire).endpoints := by
          rw [hends]
          simp
        exact ⟨endpoint, by simp, hallSelected endpoint hmem⟩

/-- A bare, unselected anchor wire with no incidence is outside both closures. -/
theorem bareAnchorWire_outsideClosure
    (selection : CheckedSelection d) {wire : Fin d.wireCount}
    (hscope : (d.wires wire).scope = selection.val.anchor)
    (hnotExplicit : wire ∉ selection.val.explicitWires)
    (hanchor : ¬ selection.val.SelectsRegion selection.val.anchor)
    (hbare : (d.wires wire).endpoints = []) :
    wire ∉ selection.internalWires ∧ wire ∉ selection.touchingWires := by
  constructor
  · intro hinternal
    rcases (selection.mem_internalWires_expanded wire).1 hinternal with
      hselectedScope | hexplicit
    · apply hanchor
      rwa [hscope] at hselectedScope
    · exact hnotExplicit hexplicit
  · intro htouching
    obtain ⟨_, endpoint, hendpoint, _⟩ :=
      selection.mem_touchingWires_consequences htouching
    simp [hbare] at hendpoint

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

namespace SelectionExamples

/-- A finite host exercising every selection-closure category. -/
def closureHost : ConcreteDiagram where
  regionCount := 3
  nodeCount := 4
  wireCount := 5
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .cut 0
    else .cut 1
  nodes := fun node =>
    if node = 0 then .named 0 0 1
    else if node = 1 then .named 1 0 1
    else if node = 2 then .named 2 0 1
    else .named 0 0 1
  wires := fun wire =>
    if wire = 0 then {
      scope := 0
      endpoints := [
        { node := 0, port := .arg 0 },
        { node := 2, port := .arg 0 }
      ]
    } else if wire = 1 then {
      scope := 0
      endpoints := [
        { node := 0, port := .arg 0 },
        { node := 1, port := .arg 0 },
        { node := 2, port := .arg 0 }
      ]
    } else if wire = 2 then {
      scope := 0
      endpoints := [
        { node := 1, port := .arg 0 },
        { node := 3, port := .arg 0 }
      ]
    } else if wire = 3 then {
      scope := 2
      endpoints := [{ node := 2, port := .arg 0 }]
    } else {
      scope := 0
      endpoints := []
    }

def regionId (index : Fin 3) : Fin closureHost.regionCount :=
  ⟨index.val, by simp [closureHost, index.isLt]⟩

def nodeId (index : Fin 4) : Fin closureHost.nodeCount :=
  ⟨index.val, by simp [closureHost, index.isLt]⟩

def wireId (index : Fin 5) : Fin closureHost.wireCount :=
  ⟨index.val, by simp [closureHost, index.isLt]⟩

def closureRequest : SelectionRequest closureHost where
  anchor := regionId 0
  childRoots := [regionId 1]
  directNodes := [nodeId 0]
  explicitWires := [wireId 0]

theorem closureRequest_valid : closureRequest.Valid := by
  constructor <;> decide

def closureSelection : CheckedSelection closureHost :=
  ⟨closureRequest, closureRequest_valid⟩

theorem closureRequest_check :
    checkSelection closureRequest = .ok closureSelection := by
  exact checkSelection_complete closureRequest_valid

theorem closureSelection_lists :
    closureSelection.selectedRegions = [regionId 1, regionId 2] ∧
      closureSelection.selectedNodes = [nodeId 0, nodeId 1, nodeId 2] ∧
      closureSelection.internalWires = [wireId 0, wireId 3] ∧
      closureSelection.touchingWires = [wireId 1, wireId 2] := by
  decide

theorem closureSelection_wire_categories :
    wireId 0 ∈ closureSelection.internalWires ∧
      wireId 1 ∈ closureSelection.touchingWires ∧
      wireId 2 ∈ closureSelection.touchingWires ∧
      wireId 3 ∈ closureSelection.internalWires ∧
      wireId 4 ∉ closureSelection.internalWires ∧
      wireId 4 ∉ closureSelection.touchingWires := by
  decide

theorem closureSelection_nonexplicit_allEndpointsSelected :
    wireId 1 ∉ closureRequest.explicitWires ∧
      ∀ endpoint, endpoint ∈ (closureHost.wires (wireId 1)).endpoints →
        endpoint.node ∈ closureSelection.selectedNodes := by
  decide

theorem closureSelection_crossingWire :
    (∃ endpoint, endpoint ∈ (closureHost.wires (wireId 2)).endpoints ∧
      endpoint.node ∈ closureSelection.selectedNodes) ∧
    (∃ endpoint, endpoint ∈ (closureHost.wires (wireId 2)).endpoints ∧
      endpoint.node ∉ closureSelection.selectedNodes) := by
  decide

end SelectionExamples

end VisualProof.Diagram
