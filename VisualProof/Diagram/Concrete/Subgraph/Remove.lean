import VisualProof.Diagram.Concrete.Subgraph.Selection
import VisualProof.Diagram.Concrete.Subgraph.Reindex
import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof.Diagram

/-- Dense survivor receipts shared by frame construction and decomposition. -/
structure FrameDomains (d : ConcreteDiagram) (selection : CheckedSelection d) where
  regions : SurvivorDomain d.regionCount :=
    ⟨fun region => decide (region = d.root ∨ region ∉ selection.selectedRegions)⟩
  regions_exact : ∀ region, regions.survives region =
      decide (region = d.root ∨ region ∉ selection.selectedRegions) := by
    intro region
    rfl
  nodes : SurvivorDomain d.nodeCount :=
    ⟨fun node => decide (node ∉ selection.selectedNodes)⟩
  nodes_exact : ∀ node, nodes.survives node =
      decide (node ∉ selection.selectedNodes) := by
    intro node
    rfl
  wires : SurvivorDomain d.wireCount :=
    ⟨fun wire => decide (wire ∉ selection.internalWires)⟩
  wires_exact : ∀ wire, wires.survives wire =
      decide (wire ∉ selection.internalWires) := by
    intro wire
    rfl

namespace FrameDomains

@[simp] theorem region_survives_iff (domains : FrameDomains d selection)
    (region : Fin d.regionCount) :
    domains.regions.survives region = true ↔
      region = d.root ∨ region ∉ selection.selectedRegions := by
  rw [domains.regions_exact]
  simp

@[simp] theorem node_survives_iff (domains : FrameDomains d selection)
    (node : Fin d.nodeCount) :
    domains.nodes.survives node = true ↔
      node ∉ selection.selectedNodes := by
  rw [domains.nodes_exact]
  simp

@[simp] theorem wire_survives_iff (domains : FrameDomains d selection)
    (wire : Fin d.wireCount) :
    domains.wires.survives wire = true ↔
      wire ∉ selection.internalWires := by
  rw [domains.wires_exact]
  simp

@[simp] theorem root_survives (domains : FrameDomains d selection) :
    domains.regions.survives d.root = true := by
  rw [domains.regions_exact]
  simp

/-- The compact identifier of the retained sheet root. -/
def root (domains : FrameDomains d selection) : domains.regions.Carrier :=
  domains.regions.index d.root domains.root_survives

@[simp] theorem root_origin (domains : FrameDomains d selection) :
    domains.regions.origin domains.root = d.root := by
  exact domains.regions.origin_index d.root domains.root_survives

end FrameDomains

namespace ConcreteDiagram

private def fallbackNode (domains : FrameDomains d selection) :
    CNode domains.regions.count :=
  .term domains.root 0 (.lam (.bvar 0))

private def frameRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (region : domains.regions.Carrier) : CRegion domains.regions.count :=
  (domains.regions.reindexRegion?
    (d.regions (domains.regions.origin region))).getD .sheet

private def frameNode (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (node : domains.nodes.Carrier) : CNode domains.regions.count :=
  (domains.regions.reindexNode?
    (d.nodes (domains.nodes.origin node))).getD (fallbackNode domains)

private def frameEndpoints (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (wire : domains.wires.Carrier) : List (CEndpoint domains.nodes.count) :=
  (d.wires (domains.wires.origin wire)).endpoints.filterMap
    domains.nodes.reindexEndpoint?

private def frameWire (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (wire : domains.wires.Carrier) :
    CWire domains.regions.count domains.nodes.count :=
  let original := d.wires (domains.wires.origin wire)
  {
    scope := (domains.regions.index? original.scope).getD domains.root
    endpoints := d.frameEndpoints selection domains wire
  }

/--
The deterministic raw frame. Selected regions and nodes and internal wires are
removed; surviving wire endpoints are restricted to surviving nodes. Dense
identifiers are exactly the accompanying survivor receipts.
-/
def removeRaw (d : ConcreteDiagram) (selection : CheckedSelection d)
    (domains : FrameDomains d selection := {}) : ConcreteDiagram where
  regionCount := domains.regions.count
  nodeCount := domains.nodes.count
  wireCount := domains.wires.count
  root := domains.root
  regions := d.frameRegion selection domains
  nodes := d.frameNode selection domains
  wires := d.frameWire selection domains

@[simp] theorem removeRaw_regionCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).regionCount = domains.regions.count := rfl

@[simp] theorem removeRaw_nodeCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).nodeCount = domains.nodes.count := rfl

@[simp] theorem removeRaw_wireCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).wireCount = domains.wires.count := rfl

@[simp] theorem removeRaw_root (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).root = domains.root := rfl

/-- Run the sole concrete well-formedness authority on the computed frame. -/
def removeChecked (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection := {}) :
    Except WFError (CheckedDiagram signature) :=
  checkWellFormed signature (host.val.removeRaw selection domains)

theorem removeChecked_sound
    (h : removeChecked signature host selection domains = .ok frame) :
    frame.val = host.val.removeRaw selection domains ∧
      frame.val.WellFormed signature := by
  constructor
  · exact checkWellFormed_preserves_input h
  · exact frame.property

end ConcreteDiagram

end VisualProof.Diagram
