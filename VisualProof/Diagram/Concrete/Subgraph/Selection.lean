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

/--
The node predicate used while validating explicit wires. It is the closure of
the requested direct nodes under ownership by a selected child subtree.
-/
def SelectsNode (request : SelectionRequest d)
    (node : Fin d.nodeCount) : Prop :=
  node ∈ request.directNodes ∨
    ∃ root, root ∈ request.childRoots ∧
      d.Encloses root (d.nodes node).region

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
