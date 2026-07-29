import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof

/-- Durable, untrusted selection input. -/
structure SelectionInput (host : CheckedDiagram definitions) where
  region : host.val.RegionId
  regions : List host.val.RegionId
  nodes : List host.val.NodeId
  wires : List host.val.WireId

/-- Stable refusal vocabulary for executable selection validation. -/
inductive SelectionError
  | duplicateSubtreeRoot
  | duplicateDirectNode
  | duplicateExplicitWire
  | subtreeRootNotDirectChild
  | directNodeNotAtAnchor
  | explicitWireNotAtAnchor
  | explicitWireEndpointOutsideSelection
  deriving Repr, DecidableEq

/--
The exact checked selection authority used by the concrete kernel.

Its constructor and validation fields are private. The sole public construction
path is `checkSelection`; callers can inspect only the validated input.
-/
structure CheckedSelection (host : CheckedDiagram definitions) where
  private mk ::
  input : SelectionInput host
  private subtreeRoots_nodup_proof : input.regions.Nodup
  private directNodes_nodup_proof : input.nodes.Nodup
  private explicitWires_nodup_proof : input.wires.Nodup
  private subtreeRoot_child_proof :
    ∀ child, child ∈ input.regions →
      host.val.regions child = .cut input.region
  private directNode_at_anchor_proof :
    ∀ node, node ∈ input.nodes →
      (host.val.nodes node).region = input.region
  private explicitWire_at_anchor_proof :
    ∀ wire, wire ∈ input.wires →
      (host.val.wires wire).scope = input.region
  private explicitWire_endpoints_selected_proof :
    ∀ wire, wire ∈ input.wires →
      ∀ endpoint, endpoint ∈ (host.val.wires wire).endpoints →
        endpoint.node ∈ input.nodes ∨
          ∃ root, root ∈ input.regions ∧
            host.val.Encloses root
              (host.val.nodes endpoint.node).region

/-- Validate a durable selection input without searching or repairing it. -/
def checkSelection
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    (input : SelectionInput host) :
    Except SelectionError (CheckedSelection host) := by
  if rootsNodup : input.regions.Nodup then
    if nodesNodup : input.nodes.Nodup then
      if wiresNodup : input.wires.Nodup then
        if rootsDirect :
            ∀ child, child ∈ input.regions →
              host.val.regions child = .cut input.region then
          if nodesDirect :
              ∀ node, node ∈ input.nodes →
                (host.val.nodes node).region = input.region then
            if wiresDirect :
                ∀ wire, wire ∈ input.wires →
                  (host.val.wires wire).scope = input.region then
              if endpointsSelected :
                  ∀ wire, wire ∈ input.wires →
                    ∀ endpoint,
                      endpoint ∈ (host.val.wires wire).endpoints →
                        endpoint.node ∈ input.nodes ∨
                          ∃ root, root ∈ input.regions ∧
                            host.val.Encloses root
                              (host.val.nodes endpoint.node).region then
                exact .ok
                  ⟨input, rootsNodup, nodesNodup, wiresNodup,
                    rootsDirect, nodesDirect, wiresDirect,
                    endpointsSelected⟩
              else
                exact .error .explicitWireEndpointOutsideSelection
            else
              exact .error .explicitWireNotAtAnchor
          else
            exact .error .directNodeNotAtAnchor
        else
          exact .error .subtreeRootNotDirectChild
      else
        exact .error .duplicateExplicitWire
    else
      exact .error .duplicateDirectNode
  else
    exact .error .duplicateSubtreeRoot

theorem checkSelection_preserves_input
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    (input : SelectionInput host)
    (checked : CheckedSelection host)
    (accepted : checkSelection input = .ok checked) :
    checked.input = input := by
  unfold checkSelection at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  exact congrArg CheckedSelection.input (Except.ok.inj accepted.symm)

namespace CheckedSelection

def region (selection : CheckedSelection host) : host.val.RegionId :=
  selection.input.region

def subtreeRoots (selection : CheckedSelection host) :
    List host.val.RegionId :=
  selection.input.regions

def directNodes (selection : CheckedSelection host) :
    List host.val.NodeId :=
  selection.input.nodes

def explicitWires (selection : CheckedSelection host) :
    List host.val.WireId :=
  selection.input.wires

theorem subtreeRoots_nodup (selection : CheckedSelection host) :
    selection.subtreeRoots.Nodup :=
  selection.subtreeRoots_nodup_proof

theorem directNodes_nodup (selection : CheckedSelection host) :
    selection.directNodes.Nodup :=
  selection.directNodes_nodup_proof

theorem explicitWires_nodup (selection : CheckedSelection host) :
    selection.explicitWires.Nodup :=
  selection.explicitWires_nodup_proof

theorem subtreeRoot_child (selection : CheckedSelection host) :
    ∀ region, region ∈ selection.subtreeRoots →
      host.val.regions region = .cut selection.region :=
  selection.subtreeRoot_child_proof

theorem directNode_at_anchor (selection : CheckedSelection host) :
    ∀ node, node ∈ selection.directNodes →
      (host.val.nodes node).region = selection.region :=
  selection.directNode_at_anchor_proof

theorem explicitWire_at_anchor (selection : CheckedSelection host) :
    ∀ wire, wire ∈ selection.explicitWires →
      (host.val.wires wire).scope = selection.region :=
  selection.explicitWire_at_anchor_proof

theorem explicitWire_endpoints_selected
    (selection : CheckedSelection host) :
    ∀ wire, wire ∈ selection.explicitWires →
      ∀ endpoint, endpoint ∈ (host.val.wires wire).endpoints →
        endpoint.node ∈ selection.directNodes ∨
          ∃ root, root ∈ selection.subtreeRoots ∧
            host.val.Encloses root
              (host.val.nodes endpoint.node).region :=
  selection.explicitWire_endpoints_selected_proof

/-- A region belongs to one of the explicitly selected child subtrees. -/
def IsSelectedRegion (selection : CheckedSelection host)
    (region : host.val.RegionId) : Prop :=
  ∃ root, root ∈ selection.subtreeRoots ∧
    host.val.Encloses root region

instance (selection : CheckedSelection host)
    (region : host.val.RegionId) :
    Decidable (selection.IsSelectedRegion region) := by
  unfold IsSelectedRegion
  infer_instance

/-- Canonical finite closure of the selected child subtree roots. -/
def allRegions (selection : CheckedSelection host) :
    List host.val.RegionId :=
  host.val.regionsList.filter fun region =>
    decide (selection.IsSelectedRegion region)

theorem allRegions_nodup (selection : CheckedSelection host) :
    selection.allRegions.Nodup :=
  Data.Finite.allFin_nodup host.val.regionCount |>.filter _

@[simp] theorem mem_allRegions
    (selection : CheckedSelection host)
    (region : host.val.RegionId) :
    region ∈ selection.allRegions ↔
      selection.IsSelectedRegion region := by
  simp [allRegions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin]

theorem subtreeRoot_mem_allRegions
    (selection : CheckedSelection host)
    (region : host.val.RegionId)
    (member : region ∈ selection.subtreeRoots) :
    region ∈ selection.allRegions := by
  rw [mem_allRegions]
  exact ⟨region, member, host.val.encloses_refl region⟩

/-- A selected node is direct at the anchor or lies in a selected subtree. -/
def IsSelectedNode (selection : CheckedSelection host)
    (node : host.val.NodeId) : Prop :=
  node ∈ selection.directNodes ∨
    (host.val.nodes node).region ∈ selection.allRegions

instance (selection : CheckedSelection host)
    (node : host.val.NodeId) :
    Decidable (selection.IsSelectedNode node) := by
  unfold IsSelectedNode
  infer_instance

/-- Canonical direct-node plus subtree-node closure. -/
def allNodes (selection : CheckedSelection host) :
    List host.val.NodeId :=
  host.val.nodesList.filter fun node =>
    decide (selection.IsSelectedNode node)

theorem allNodes_nodup (selection : CheckedSelection host) :
    selection.allNodes.Nodup :=
  Data.Finite.allFin_nodup host.val.nodeCount |>.filter _

@[simp] theorem mem_allNodes
    (selection : CheckedSelection host)
    (node : host.val.NodeId) :
    node ∈ selection.allNodes ↔ selection.IsSelectedNode node := by
  simp [allNodes, ConcreteDiagram.nodesList,
    Data.Finite.mem_allFin]

theorem directNode_mem_allNodes
    (selection : CheckedSelection host)
    (node : host.val.NodeId)
    (member : node ∈ selection.directNodes) :
    node ∈ selection.allNodes := by
  rw [mem_allNodes]
  exact .inl member

theorem subtreeNode_mem_allNodes
    (selection : CheckedSelection host)
    (node : host.val.NodeId)
    (member : (host.val.nodes node).region ∈ selection.allRegions) :
    node ∈ selection.allNodes := by
  rw [mem_allNodes]
  exact .inr member

/-- Internal wires are subtree-scoped or explicitly internalized at the anchor. -/
def IsInternal (selection : CheckedSelection host)
    (wire : host.val.WireId) : Prop :=
  (host.val.wires wire).scope ∈ selection.allRegions ∨
    wire ∈ selection.explicitWires

instance (selection : CheckedSelection host)
    (wire : host.val.WireId) :
    Decidable (selection.IsInternal wire) := by
  unfold IsInternal
  infer_instance

/-- A wire touches selected content when one of its endpoints is selected. -/
def TouchesSelectedNode (selection : CheckedSelection host)
    (wire : host.val.WireId) : Prop :=
  ∃ endpoint ∈ (host.val.wires wire).endpoints,
    endpoint.node ∈ selection.allNodes

instance (selection : CheckedSelection host)
    (wire : host.val.WireId) :
    Decidable (selection.TouchesSelectedNode wire) := by
  unfold TouchesSelectedNode
  infer_instance

/-- Touching boundary wires are precisely the touching wires not internalized. -/
def IsTouching (selection : CheckedSelection host)
    (wire : host.val.WireId) : Prop :=
  ¬ selection.IsInternal wire ∧ selection.TouchesSelectedNode wire

instance (selection : CheckedSelection host)
    (wire : host.val.WireId) :
    Decidable (selection.IsTouching wire) := by
  unfold IsTouching
  infer_instance

/-- Canonical internal-wire order is the host's finite wire order. -/
def internalWires (selection : CheckedSelection host) :
    List host.val.WireId :=
  host.val.wiresList.filter fun wire =>
    decide (selection.IsInternal wire)

/-- Canonical boundary-attachment order is the host's finite wire order. -/
def touchingWires (selection : CheckedSelection host) :
    List host.val.WireId :=
  host.val.wiresList.filter fun wire =>
    decide (selection.IsTouching wire)

theorem internalWires_nodup (selection : CheckedSelection host) :
    selection.internalWires.Nodup :=
  Data.Finite.allFin_nodup host.val.wireCount |>.filter _

theorem touchingWires_nodup (selection : CheckedSelection host) :
    selection.touchingWires.Nodup :=
  Data.Finite.allFin_nodup host.val.wireCount |>.filter _

@[simp] theorem mem_internalWires
    (selection : CheckedSelection host)
    (wire : host.val.WireId) :
    wire ∈ selection.internalWires ↔ selection.IsInternal wire := by
  simp [internalWires, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin]

@[simp] theorem mem_touchingWires
    (selection : CheckedSelection host)
    (wire : host.val.WireId) :
    wire ∈ selection.touchingWires ↔ selection.IsTouching wire := by
  simp [touchingWires, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin]

theorem internal_not_touching
    (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (internal : wire ∈ selection.internalWires) :
    wire ∉ selection.touchingWires := by
  rw [mem_internalWires] at internal
  rw [mem_touchingWires]
  exact fun touching => touching.1 internal

theorem explicitWire_internal
    (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (member : wire ∈ selection.explicitWires) :
    wire ∈ selection.internalWires := by
  rw [mem_internalWires]
  exact .inr member

theorem explicitWire_endpoint_selected
    (selection : CheckedSelection host)
    (wire : host.val.WireId)
    (wireMember : wire ∈ selection.explicitWires)
    (endpoint : CEndpoint host.val.nodeCount)
    (endpointMember : endpoint ∈ (host.val.wires wire).endpoints) :
    endpoint.node ∈ selection.allNodes := by
  rw [mem_allNodes]
  rcases selection.explicitWire_endpoints_selected wire wireMember
      endpoint endpointMember with direct | subtree
  · exact .inl direct
  · right
    rw [mem_allRegions]
    exact subtree

end CheckedSelection

end VisualProof
