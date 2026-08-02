import VisualProof.Diagram.Concrete.Subgraph.Selection
import VisualProof.Diagram.Concrete.IdentityIncidence

namespace VisualProof

local instance {α : Type} [DecidableEq α]
    (left right : List α) : Decidable (left.Perm right) :=
  List.decidablePerm left right

local instance {sourceCount targetCount : Nat}
    (function : Fin sourceCount → Fin targetCount) :
    Decidable (Function.Injective function) := by
  unfold Function.Injective
  infer_instance

/-- Identity storage indices collapse to one semantic incidence class. -/
inductive OccurrencePort
  | head
  | arg (index : Nat)
  | identity
  deriving Repr, DecidableEq

namespace OccurrencePort

def ofConcrete : CPort → OccurrencePort
  | .head => .head
  | .arg index => .arg index
  | .identity _ => .identity

end OccurrencePort

/-- Port-position key used by exact occurrence endpoint comparison. -/
abbrev OccurrenceEndpointKey (nodeCount : Nat) :=
  Fin nodeCount × OccurrencePort

def occurrenceEndpointKey
    (endpoint : CEndpoint nodeCount) :
    OccurrenceEndpointKey nodeCount :=
  (endpoint.node, OccurrencePort.ofConcrete endpoint.port)

def mappedOccurrenceEndpointKey
    (nodeMap : Fin sourceNodeCount → Fin targetNodeCount)
    (endpoint : CEndpoint sourceNodeCount) :
    OccurrenceEndpointKey targetNodeCount :=
  (nodeMap endpoint.node, OccurrencePort.ofConcrete endpoint.port)

/--
Consume every expected endpoint from the actual endpoint multiset.

Actual endpoints may remain, but one actual occurrence cannot satisfy two
equal expected occurrences.
-/
def occurrenceEndpointMultisetContains :
    List (OccurrenceEndpointKey nodeCount) →
      List (OccurrenceEndpointKey nodeCount) → Bool
  | [], _ => true
  | expected :: rest, actual =>
      if expected ∈ actual then
        occurrenceEndpointMultisetContains rest (actual.erase expected)
      else
        false

/-- Structural preservation of one node under an occurrence map. -/
def OccurrenceNodeCorresponds
    (pattern host : ConcreteDiagram definitionCount)
    (regionMap : pattern.RegionId → host.RegionId)
    (patternNode : pattern.NodeId) (hostNode : host.NodeId) : Prop :=
  match pattern.nodes patternNode with
  | .atom region args =>
      host.nodes hostNode = .atom (regionMap region) args
  | .ref region definition args =>
      host.nodes hostNode = .ref (regionMap region) definition args
  | .identity region sig arity =>
      host.nodes hostNode = .identity (regionMap region) sig arity

instance
    (pattern host : ConcreteDiagram definitionCount)
    (regionMap : pattern.RegionId → host.RegionId)
    (patternNode : pattern.NodeId) (hostNode : host.NodeId) :
    Decidable
      (OccurrenceNodeCorresponds pattern host regionMap
        patternNode hostNode) := by
  unfold OccurrenceNodeCorresponds
  split <;> infer_instance

/-- Direct child subtree roots selected by one open occurrence. -/
def occurrenceSubtreeRoots
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions)
    (regionMap :
      pattern.val.diagram.RegionId → host.val.RegionId) :
    List host.val.RegionId :=
  (pattern.val.diagram.childrenOf pattern.val.diagram.root).map regionMap

/-- Direct root nodes selected by one open occurrence. -/
def occurrenceDirectNodes
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions)
    (nodeMap :
      pattern.val.diagram.NodeId → host.val.NodeId) :
    List host.val.NodeId :=
  (pattern.val.diagram.nodesAt pattern.val.diagram.root).map nodeMap

/--
Root-scoped nonboundary wires are the explicitly internalized anchor wires.
Boundary membership is set-like here; its ordered multiplicity remains in the
open pattern's boundary list.
-/
def occurrenceExplicitWires
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions)
    (wireMap :
      pattern.val.diagram.WireId → host.val.WireId) :
    List host.val.WireId :=
  ((pattern.val.diagram.wiresAt pattern.val.diagram.root).filter
    fun wire => decide (wire ∉ pattern.val.boundary)).map wireMap

def occurrenceSelectionInput
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions)
    (region : host.val.RegionId)
    (regionMap :
      pattern.val.diagram.RegionId → host.val.RegionId)
    (nodeMap :
      pattern.val.diagram.NodeId → host.val.NodeId)
    (wireMap :
      pattern.val.diagram.WireId → host.val.WireId) :
    SelectionInput host where
  region := region
  regions := occurrenceSubtreeRoots pattern host regionMap
  nodes := occurrenceDirectNodes pattern host nodeMap
  wires := occurrenceExplicitWires pattern host wireMap

/-- Durable untrusted maps for one claimed open-pattern occurrence. -/
structure OccurrenceInput
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions) where
  region : host.val.RegionId
  regionMap : pattern.val.diagram.RegionId → host.val.RegionId
  nodeMap : pattern.val.diagram.NodeId → host.val.NodeId
  wireMap : pattern.val.diagram.WireId → host.val.WireId

inductive OccurrenceError
  | invalidEvidence
  | invalidSelection (error : SelectionError)
  deriving Repr, DecidableEq

/--
An exact checked occurrence of one open pattern.

The mapped pattern root is only an ambient anchor. Proper subtrees are exact;
root content is a subset. Internal wire images are exact and injective,
boundary images may alias, and the pattern boundary itself is the sole ordered
attachment authority.
-/
structure Occurrence
    (pattern : CheckedOpenDiagram definitions)
    (host : CheckedDiagram definitions) where
  private mk ::
  region : host.val.RegionId
  regionMap : pattern.val.diagram.RegionId → host.val.RegionId
  nodeMap : pattern.val.diagram.NodeId → host.val.NodeId
  wireMap : pattern.val.diagram.WireId → host.val.WireId
  private region_injective : Function.Injective regionMap
  private node_injective : Function.Injective nodeMap
  private root : regionMap pattern.val.diagram.root = region
  private parentage :
    ∀ region parent,
      pattern.val.diagram.regions region = .cut parent →
        host.val.regions (regionMap region) =
          .cut (regionMap parent)
  private node_corresponds :
    ∀ node,
      OccurrenceNodeCorresponds pattern.val.diagram host.val
        regionMap node (nodeMap node)
  private wire_signature :
    ∀ wire,
      (host.val.wires (wireMap wire)).sig =
        (pattern.val.diagram.wires wire).sig
  private internal_wire_injective :
    ∀ left right,
      left ∉ pattern.val.boundary →
      right ∉ pattern.val.boundary →
      wireMap left = wireMap right →
      left = right
  private internal_boundary_disjoint :
    ∀ internal boundary,
      internal ∉ pattern.val.boundary →
      boundary ∈ pattern.val.boundary →
      wireMap internal ≠ wireMap boundary
  private internal_wire_scope :
    ∀ wire, wire ∉ pattern.val.boundary →
      (host.val.wires (wireMap wire)).scope =
        regionMap (pattern.val.diagram.wires wire).scope
  private boundary_visible :
    ∀ wire, wire ∈ pattern.val.boundary →
      host.val.Encloses
        (host.val.wires (wireMap wire)).scope region
  private internal_endpoints_exact :
    ∀ wire, wire ∉ pattern.val.boundary →
      List.Perm
        ((pattern.val.diagram.wires wire).endpoints.map
          (mappedOccurrenceEndpointKey nodeMap))
        ((host.val.wires (wireMap wire)).endpoints.map
          occurrenceEndpointKey)
  private boundary_endpoints_contained :
    ∀ wire, wire ∈ pattern.val.boundary →
      occurrenceEndpointMultisetContains
        ((pattern.val.diagram.wires wire).endpoints.map
          (mappedOccurrenceEndpointKey nodeMap))
        ((host.val.wires (wireMap wire)).endpoints.map
          occurrenceEndpointKey) = true
  private identity_incidence :
    ∀ node,
      match pattern.val.diagram.nodes node with
      | .identity _ _ arity =>
          List.Perm
            ((pattern.val.diagram.identityOwners node arity).map wireMap)
            (host.val.identityOwners (nodeMap node) arity)
      | _ => True
  private proper_children_exact :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.childrenOf region).map regionMap)
        (host.val.childrenOf (regionMap region))
  private proper_nodes_exact :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.nodesAt region).map nodeMap)
        (host.val.nodesAt (regionMap region))
  private proper_wires_exact :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.wiresAt region).map wireMap)
        (host.val.wiresAt (regionMap region))
  private selection_subtreeRoots_nodup :
    (occurrenceSubtreeRoots pattern host regionMap).Nodup
  private selection_directNodes_nodup :
    (occurrenceDirectNodes pattern host nodeMap).Nodup
  private selection_explicitWires_nodup :
    (occurrenceExplicitWires pattern host wireMap).Nodup
  private selection_explicitWire_endpoints :
    ∀ wire,
      wire ∈ occurrenceExplicitWires pattern host wireMap →
      ∀ endpoint, endpoint ∈ (host.val.wires wire).endpoints →
        endpoint.node ∈ occurrenceDirectNodes pattern host nodeMap ∨
          ∃ subtree,
            subtree ∈ occurrenceSubtreeRoots pattern host regionMap ∧
              host.val.Encloses subtree
                (host.val.nodes endpoint.node).region
  private checkedSelection : CheckedSelection host
  private checkedSelection_input :
    checkedSelection.input =
      occurrenceSelectionInput pattern host region regionMap nodeMap wireMap

namespace OccurrenceInput

private def AnchorValid
    (input : OccurrenceInput pattern host) : Prop :=
  Function.Injective input.regionMap ∧
  Function.Injective input.nodeMap ∧
  input.regionMap pattern.val.diagram.root = input.region ∧
  (∀ child parent,
    pattern.val.diagram.regions child = .cut parent →
      host.val.regions (input.regionMap child) =
        .cut (input.regionMap parent)) ∧
  (∀ node,
    OccurrenceNodeCorresponds pattern.val.diagram host.val
      input.regionMap node (input.nodeMap node))

private def WireMapValid
    (input : OccurrenceInput pattern host) : Prop :=
  (∀ wire,
    (host.val.wires (input.wireMap wire)).sig =
      (pattern.val.diagram.wires wire).sig) ∧
  (∀ left right,
    left ∉ pattern.val.boundary →
    right ∉ pattern.val.boundary →
    input.wireMap left = input.wireMap right →
    left = right) ∧
  (∀ internal boundary,
    internal ∉ pattern.val.boundary →
    boundary ∈ pattern.val.boundary →
    input.wireMap internal ≠ input.wireMap boundary) ∧
  (∀ wire, wire ∉ pattern.val.boundary →
    (host.val.wires (input.wireMap wire)).scope =
      input.regionMap (pattern.val.diagram.wires wire).scope) ∧
  (∀ wire, wire ∈ pattern.val.boundary →
    host.val.Encloses
      (host.val.wires (input.wireMap wire)).scope input.region)

private def ContentValid
    (input : OccurrenceInput pattern host) : Prop :=
  (∀ wire, wire ∉ pattern.val.boundary →
    List.Perm
      ((pattern.val.diagram.wires wire).endpoints.map
        (mappedOccurrenceEndpointKey input.nodeMap))
      ((host.val.wires (input.wireMap wire)).endpoints.map
        occurrenceEndpointKey)) ∧
  (∀ wire, wire ∈ pattern.val.boundary →
    occurrenceEndpointMultisetContains
      ((pattern.val.diagram.wires wire).endpoints.map
        (mappedOccurrenceEndpointKey input.nodeMap))
      ((host.val.wires (input.wireMap wire)).endpoints.map
        occurrenceEndpointKey) = true) ∧
  (∀ node,
    match pattern.val.diagram.nodes node with
    | .identity _ _ arity =>
        List.Perm
          ((pattern.val.diagram.identityOwners node arity).map input.wireMap)
          (host.val.identityOwners (input.nodeMap node) arity)
    | _ => True) ∧
  (∀ region, region ≠ pattern.val.diagram.root →
    List.Perm
      ((pattern.val.diagram.childrenOf region).map input.regionMap)
      (host.val.childrenOf (input.regionMap region))) ∧
  (∀ region, region ≠ pattern.val.diagram.root →
    List.Perm
      ((pattern.val.diagram.nodesAt region).map input.nodeMap)
      (host.val.nodesAt (input.regionMap region))) ∧
  (∀ region, region ≠ pattern.val.diagram.root →
    List.Perm
      ((pattern.val.diagram.wiresAt region).map input.wireMap)
      (host.val.wiresAt (input.regionMap region)))

private def SelectionValid
    (input : OccurrenceInput pattern host) : Prop :=
  (occurrenceSubtreeRoots pattern host input.regionMap).Nodup ∧
  (occurrenceDirectNodes pattern host input.nodeMap).Nodup ∧
  (occurrenceExplicitWires pattern host input.wireMap).Nodup ∧
  (∀ wire,
    wire ∈ occurrenceExplicitWires pattern host input.wireMap →
    ∀ endpoint, endpoint ∈ (host.val.wires wire).endpoints →
      endpoint.node ∈ occurrenceDirectNodes pattern host input.nodeMap ∨
        ∃ subtree,
          subtree ∈ occurrenceSubtreeRoots pattern host input.regionMap ∧
            host.val.Encloses subtree
              (host.val.nodes endpoint.node).region)

def Valid (input : OccurrenceInput pattern host) : Prop :=
  AnchorValid input ∧ WireMapValid input ∧
    ContentValid input ∧ SelectionValid input

private instance (input : OccurrenceInput pattern host) :
    Decidable (AnchorValid input) := by
  unfold AnchorValid
  infer_instance

private instance (input : OccurrenceInput pattern host) :
    Decidable (WireMapValid input) := by
  unfold WireMapValid
  infer_instance

private instance (input : OccurrenceInput pattern host) :
    Decidable (ContentValid input) := by
  letI identityIncidenceDecidable
      (node : pattern.val.diagram.NodeId) :
      Decidable
        (match pattern.val.diagram.nodes node with
        | .identity _ _ arity =>
            List.Perm
              ((pattern.val.diagram.identityOwners node arity).map
                input.wireMap)
              (host.val.identityOwners (input.nodeMap node) arity)
        | _ => True) := by
    cases pattern.val.diagram.nodes node <;> infer_instance
  unfold ContentValid
  infer_instance

private instance (input : OccurrenceInput pattern host) :
    Decidable (SelectionValid input) := by
  unfold SelectionValid
  infer_instance

instance (input : OccurrenceInput pattern host) :
    Decidable input.Valid := by
  unfold Valid
  infer_instance

end OccurrenceInput

/-- Executably validate every supplied occurrence map and exactness gate. -/
def checkOccurrence
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (input : OccurrenceInput pattern host) :
    Except OccurrenceError (Occurrence pattern host) := by
  if valid : input.Valid then
    rcases valid with
      ⟨anchorValid, wireMapValid, contentValid, selectionValid⟩
    rcases anchorValid with
      ⟨regionInjective, nodeInjective, root, parentage,
        nodeCorresponds⟩
    rcases wireMapValid with
      ⟨wireSignature, internalWireInjective,
        internalBoundaryDisjoint, internalWireScope, boundaryVisible⟩
    rcases contentValid with
      ⟨
        internalEndpointsExact, boundaryEndpointsContained,
        identityIncidence, properChildrenExact, properNodesExact,
        properWiresExact⟩
    rcases selectionValid with
      ⟨rootsNodup, nodesNodup, wiresNodup,
        explicitEndpoints⟩
    let selectionInput :=
      occurrenceSelectionInput pattern host input.region
        input.regionMap input.nodeMap input.wireMap
    match accepted : checkSelection selectionInput with
    | .error error => exact .error (.invalidSelection error)
    | .ok selection =>
        exact .ok
          ⟨input.region, input.regionMap, input.nodeMap, input.wireMap,
            regionInjective, nodeInjective, root, parentage,
            nodeCorresponds, wireSignature, internalWireInjective,
            internalBoundaryDisjoint, internalWireScope, boundaryVisible,
            internalEndpointsExact, boundaryEndpointsContained,
            identityIncidence, properChildrenExact, properNodesExact,
            properWiresExact, rootsNodup, nodesNodup, wiresNodup,
            explicitEndpoints, selection,
            checkSelection_preserves_input selectionInput selection accepted⟩
  else
    exact .error .invalidEvidence

namespace Occurrence

/-- Recover the exact durable maps represented by a checked occurrence. -/
def toInput
    (occurrence : Occurrence pattern host) :
    OccurrenceInput pattern host where
  region := occurrence.region
  regionMap := occurrence.regionMap
  nodeMap := occurrence.nodeMap
  wireMap := occurrence.wireMap

theorem checkOccurrence_preserves_input
    (input : OccurrenceInput pattern host)
    (occurrence : Occurrence pattern host)
    (accepted : checkOccurrence input = .ok occurrence) :
    occurrence.toInput = input := by
  unfold checkOccurrence at accepted
  split at accepted
  · rename_i valid
    rcases valid with
      ⟨anchorValid, wireMapValid, contentValid, selectionValid⟩
    rcases anchorValid with
      ⟨regionInjective, nodeInjective, root, parentage,
        nodeCorresponds⟩
    rcases wireMapValid with
      ⟨wireSignature, internalWireInjective,
        internalBoundaryDisjoint, internalWireScope, boundaryVisible⟩
    rcases contentValid with
      ⟨internalEndpointsExact, boundaryEndpointsContained,
        identityIncidence, properChildrenExact, properNodesExact,
        properWiresExact⟩
    rcases selectionValid with
      ⟨rootsNodup, nodesNodup, wiresNodup, explicitEndpoints⟩
    dsimp only at accepted
    split at accepted
    · contradiction
    · have same := Except.ok.inj accepted
      cases same
      rfl
  · contradiction

theorem regionMap_injective
    (occurrence : Occurrence pattern host) :
    Function.Injective occurrence.regionMap :=
  occurrence.region_injective

theorem nodeMap_injective
    (occurrence : Occurrence pattern host) :
    Function.Injective occurrence.nodeMap :=
  occurrence.node_injective

@[simp] theorem maps_root
    (occurrence : Occurrence pattern host) :
    occurrence.regionMap pattern.val.diagram.root = occurrence.region :=
  occurrence.root

theorem maps_parentage
    (occurrence : Occurrence pattern host) :
    ∀ region parent,
      pattern.val.diagram.regions region = .cut parent →
        host.val.regions (occurrence.regionMap region) =
          .cut (occurrence.regionMap parent) :=
  occurrence.parentage

theorem node_correspondence
    (occurrence : Occurrence pattern host) :
    ∀ node,
      OccurrenceNodeCorresponds pattern.val.diagram host.val
        occurrence.regionMap node (occurrence.nodeMap node) :=
  occurrence.node_corresponds

/-- Exact occurrence node table in single-region relocation form. -/
theorem node_data
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId) :
    host.val.nodes (occurrence.nodeMap node) =
      (pattern.val.diagram.nodes node).relocate
        (occurrence.regionMap
          (pattern.val.diagram.nodes node).region) := by
  have corresponds := occurrence.node_correspondence node
  unfold OccurrenceNodeCorresponds at corresponds
  cases data : pattern.val.diagram.nodes node <;>
    simpa [data, CNode.relocate, CNode.region] using corresponds

theorem wire_signature_preserved
    (occurrence : Occurrence pattern host) :
    ∀ wire,
      (host.val.wires (occurrence.wireMap wire)).sig =
        (pattern.val.diagram.wires wire).sig :=
  occurrence.wire_signature

theorem internalWire_injective
    (occurrence : Occurrence pattern host) :
    ∀ left right,
      left ∉ pattern.val.boundary →
      right ∉ pattern.val.boundary →
      occurrence.wireMap left = occurrence.wireMap right →
      left = right :=
  occurrence.internal_wire_injective

theorem internalBoundary_disjoint
    (occurrence : Occurrence pattern host) :
    ∀ internal boundary,
      internal ∉ pattern.val.boundary →
      boundary ∈ pattern.val.boundary →
      occurrence.wireMap internal ≠ occurrence.wireMap boundary :=
  occurrence.internal_boundary_disjoint

theorem internalWire_scope
    (occurrence : Occurrence pattern host) :
    ∀ wire, wire ∉ pattern.val.boundary →
      (host.val.wires (occurrence.wireMap wire)).scope =
        occurrence.regionMap (pattern.val.diagram.wires wire).scope :=
  occurrence.internal_wire_scope

theorem boundaryWire_visible
    (occurrence : Occurrence pattern host) :
    ∀ wire, wire ∈ pattern.val.boundary →
      host.val.Encloses
        (host.val.wires (occurrence.wireMap wire)).scope occurrence.region :=
  occurrence.boundary_visible

theorem internalEndpoints_exact
    (occurrence : Occurrence pattern host) :
    ∀ wire, wire ∉ pattern.val.boundary →
      List.Perm
        ((pattern.val.diagram.wires wire).endpoints.map
          (mappedOccurrenceEndpointKey occurrence.nodeMap))
        ((host.val.wires (occurrence.wireMap wire)).endpoints.map
          occurrenceEndpointKey) :=
  occurrence.internal_endpoints_exact

theorem boundaryEndpoints_contained
    (occurrence : Occurrence pattern host) :
    ∀ wire, wire ∈ pattern.val.boundary →
      occurrenceEndpointMultisetContains
        ((pattern.val.diagram.wires wire).endpoints.map
          (mappedOccurrenceEndpointKey occurrence.nodeMap))
        ((host.val.wires (occurrence.wireMap wire)).endpoints.map
          occurrenceEndpointKey) = true :=
  occurrence.boundary_endpoints_contained

theorem identityIncidence_permuted
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (identity :
      pattern.val.diagram.nodes node = .identity region sig arity) :
    List.Perm
      ((pattern.val.diagram.identityOwners node arity).map
        occurrence.wireMap)
      (host.val.identityOwners (occurrence.nodeMap node) arity) := by
  have incidence := occurrence.identity_incidence node
  rw [identity] at incidence
  exact incidence

/--
Construction-owned renaming of identity storage positions.  It is selected
from the occurrence's exact owner-multiset permutation, so repeated ownership
by one wire is retained positionally.
-/
noncomputable def identityPortEquiv
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (identity :
      pattern.val.diagram.nodes node = .identity region sig arity) :
    Data.Finite.FiniteEquiv (Fin arity) (Fin arity) := by
  let sourceOwners := pattern.val.diagram.identityOwners node arity
  let targetOwners := host.val.identityOwners (occurrence.nodeMap node) arity
  have sourceLength : sourceOwners.length = arity :=
    ConcreteDiagram.identityOwners_length _ pattern.val.diagram
      pattern.property.diagram node region sig arity identity
  have nodeCorresponds := occurrence.node_correspondence node
  have targetNode :
      host.val.nodes (occurrence.nodeMap node) =
        .identity (occurrence.regionMap region) sig arity := by
    simpa [OccurrenceNodeCorresponds, identity] using nodeCorresponds
  have targetLength : targetOwners.length = arity :=
    ConcreteDiagram.identityOwners_length _ host.val host.property
      (occurrence.nodeMap node) (occurrence.regionMap region) sig arity
      targetNode
  let permuted := occurrence.identityIncidence_permuted
    node region sig arity identity
  let positions := Data.Finite.FiniteEquiv.ofListPerm permuted
  exact
    (Data.Finite.FiniteEquiv.finCast
        (by simp [sourceOwners, sourceLength])).trans
      (positions.1.trans
        (Data.Finite.FiniteEquiv.finCast targetLength))

/-- The positional identity renaming transports the exact owning wire. -/
theorem identityPortEquiv_owner
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (identity :
      pattern.val.diagram.nodes node = .identity region sig arity)
    (index : Fin arity)
    (sourceWire : pattern.val.diagram.WireId)
    (sourceOwner :
      pattern.val.diagram.endpointOwner? ⟨node, .identity index.val⟩ =
        some sourceWire) :
    host.val.endpointOwner?
        ⟨occurrence.nodeMap node,
          .identity
            ((occurrence.identityPortEquiv node region sig arity identity)
              index).val⟩ =
      some (occurrence.wireMap sourceWire) := by
  let sourceOwners := pattern.val.diagram.identityOwners node arity
  let targetOwners := host.val.identityOwners (occurrence.nodeMap node) arity
  have sourceLength : sourceOwners.length = arity :=
    ConcreteDiagram.identityOwners_length _ pattern.val.diagram
      pattern.property.diagram node region sig arity identity
  have nodeCorresponds := occurrence.node_correspondence node
  have targetNode :
      host.val.nodes (occurrence.nodeMap node) =
        .identity (occurrence.regionMap region) sig arity := by
    simpa [OccurrenceNodeCorresponds, identity] using nodeCorresponds
  have targetLength : targetOwners.length = arity :=
    ConcreteDiagram.identityOwners_length _ host.val host.property
      (occurrence.nodeMap node) (occurrence.regionMap region) sig arity
      targetNode
  let permuted := occurrence.identityIncidence_permuted
    node region sig arity identity
  let positions := Data.Finite.FiniteEquiv.ofListPerm permuted
  let sourcePosition :
      Fin (sourceOwners.map occurrence.wireMap).length :=
    Data.Finite.FiniteEquiv.finCast
      (by simp [sourceOwners, sourceLength]) index
  let targetPosition : Fin targetOwners.length :=
    positions.1 sourcePosition
  have sourcePositioned :=
    ConcreteDiagram.identityOwners_get_eq_of_owner _
      pattern.val.diagram pattern.property.diagram node region sig arity
      identity index sourceWire sourceOwner
  have positionExact := positions.2 sourcePosition
  have outputPosition :
      Fin.cast targetLength.symm
          ((occurrence.identityPortEquiv node region sig arity identity)
            index) =
        targetPosition := by
    apply Fin.ext
    rfl
  have targetPositioned :
      targetOwners.get
          (Fin.cast targetLength.symm
            ((occurrence.identityPortEquiv node region sig arity identity)
              index)) =
        occurrence.wireMap sourceWire := by
    rw [outputPosition]
    calc
      targetOwners.get targetPosition =
          (sourceOwners.map occurrence.wireMap).get sourcePosition :=
        positionExact
      _ = occurrence.wireMap
          (sourceOwners.get
            (Fin.cast (by simp [sourceOwners]) sourcePosition)) := by
        simp
      _ = occurrence.wireMap sourceWire := by
        exact congrArg occurrence.wireMap
          (by simpa [sourcePosition, sourceOwners] using sourcePositioned)
  have targetOwner :=
    ConcreteDiagram.identityOwner_at_eq_some_get _ host.val
      host.property (occurrence.nodeMap node) (occurrence.regionMap region)
      sig arity targetNode
      ((occurrence.identityPortEquiv node region sig arity identity) index)
  change
    host.val.endpointOwner?
        ⟨occurrence.nodeMap node,
          .identity
            ((occurrence.identityPortEquiv node region sig arity identity)
              index).val⟩ =
      some
        (targetOwners.get
          (Fin.cast targetLength.symm
            ((occurrence.identityPortEquiv node region sig arity identity)
              index))) at targetOwner
  rw [targetPositioned] at targetOwner
  exact targetOwner

/--
The inverse positional identity renaming recovers an owning source wire.  The
source wire is existential because distinct boundary wires may intentionally
share one host wire; its mapped owner is nevertheless exact.
-/
theorem identityPortEquiv_symm_owner
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (identity :
      pattern.val.diagram.nodes node = .identity region sig arity)
    (index : Fin arity)
    (targetWire : host.val.WireId)
    (targetOwner :
      host.val.endpointOwner?
          ⟨occurrence.nodeMap node, .identity index.val⟩ =
        some targetWire) :
    ∃ sourceWire : pattern.val.diagram.WireId,
      pattern.val.diagram.endpointOwner?
          ⟨node,
            .identity
              ((occurrence.identityPortEquiv node region sig arity identity).symm
                index).val⟩ =
          some sourceWire ∧
        occurrence.wireMap sourceWire = targetWire := by
  let sourceIndex :=
    (occurrence.identityPortEquiv node region sig arity identity).symm index
  have sourceRequired :
      CPort.identity sourceIndex.val ∈
        pattern.val.diagram.requiredPorts node := by
    simp [ConcreteDiagram.requiredPorts, identity, sourceIndex.isLt]
  obtain ⟨sourceWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete _ pattern.val.diagram
      pattern.property.diagram node (.identity sourceIndex.val) sourceRequired
  refine ⟨sourceWire, sourceOwner, ?_⟩
  have mappedOwner := occurrence.identityPortEquiv_owner node region sig arity
    identity sourceIndex sourceWire sourceOwner
  have indexExact :
      (occurrence.identityPortEquiv node region sig arity identity)
          sourceIndex = index :=
    (occurrence.identityPortEquiv node region sig arity identity).right_inv index
  rw [indexExact] at mappedOwner
  exact Option.some.inj (mappedOwner.symm.trans targetOwner)

/-- Extend the finite identity-position renaming to every concrete port. -/
noncomputable def identityCPortEquiv
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (identity :
      pattern.val.diagram.nodes node = .identity region sig arity) :
    Data.Finite.FiniteEquiv CPort CPort where
  toFun := fun port =>
    match port with
    | .head => .head
    | .arg index => .arg index
    | .identity index =>
        if bound : index < arity then
          .identity
            ((occurrence.identityPortEquiv node region sig arity identity)
              ⟨index, bound⟩).val
        else
          .identity index
  invFun := fun port =>
    match port with
    | .head => .head
    | .arg index => .arg index
    | .identity index =>
        if bound : index < arity then
          .identity
            ((occurrence.identityPortEquiv node region sig arity identity).symm
              ⟨index, bound⟩).val
        else
          .identity index
  left_inv := by
    intro port
    cases port with
    | head => rfl
    | arg index => rfl
    | identity index =>
        by_cases bound : index < arity
        · simp only [bound, dif_pos]
          have mappedBound :
              ((occurrence.identityPortEquiv node region sig arity identity)
                ⟨index, bound⟩).val < arity :=
            ((occurrence.identityPortEquiv node region sig arity identity)
              ⟨index, bound⟩).isLt
          rw [dif_pos mappedBound]
          exact congrArg CPort.identity
            (congrArg Fin.val
              (Data.Finite.FiniteEquiv.symm_apply_apply
                (occurrence.identityPortEquiv node region sig arity identity)
                ⟨index, bound⟩))
        · simp [bound]
  right_inv := by
    intro port
    cases port with
    | head => rfl
    | arg index => rfl
    | identity index =>
        by_cases bound : index < arity
        · simp only [bound, dif_pos]
          have mappedBound :
              ((occurrence.identityPortEquiv node region sig arity identity).symm
                ⟨index, bound⟩).val < arity :=
            ((occurrence.identityPortEquiv node region sig arity identity).symm
              ⟨index, bound⟩).isLt
          rw [dif_pos mappedBound]
          exact congrArg CPort.identity
            (congrArg Fin.val
              (Data.Finite.FiniteEquiv.apply_symm_apply
                (occurrence.identityPortEquiv node region sig arity identity)
                ⟨index, bound⟩))
        · simp [bound]

/-- Total port renaming selected by the exposed source-node data. -/
noncomputable def portEquivForNode
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId) :
    Data.Finite.FiniteEquiv CPort CPort :=
  match nodeData : pattern.val.diagram.nodes node with
  | .atom _ _ => Data.Finite.FiniteEquiv.refl _
  | .ref _ _ _ => Data.Finite.FiniteEquiv.refl _
  | .identity region sig arity =>
      occurrence.identityCPortEquiv node region sig arity nodeData

theorem portEquivForNode_atom
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (args : List Sig)
    (nodeData : pattern.val.diagram.nodes node = .atom region args) :
    occurrence.portEquivForNode node =
      Data.Finite.FiniteEquiv.refl CPort := by
  unfold portEquivForNode
  split <;> simp_all

theorem portEquivForNode_ref
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (definition : Fin definitions.length)
    (args : List Sig)
    (nodeData :
      pattern.val.diagram.nodes node = .ref region definition args) :
    occurrence.portEquivForNode node =
      Data.Finite.FiniteEquiv.refl CPort := by
  unfold portEquivForNode
  split <;> simp_all

theorem portEquivForNode_identity
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId)
    (region : pattern.val.diagram.RegionId)
    (sig : Sig) (arity : Nat)
    (nodeData :
      pattern.val.diagram.nodes node = .identity region sig arity) :
  occurrence.portEquivForNode node =
      occurrence.identityCPortEquiv node region sig arity nodeData := by
  unfold portEquivForNode
  split
  · simp_all
  · simp_all
  · rename_i positionalData
    cases positionalData.symm.trans nodeData
    have same : positionalData = nodeData := Subsingleton.elim _ _
    cases same
    rfl

/-- Deterministic endpoint transport for an explicitly exposed source node. -/
noncomputable def endpointMapForNode
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount) :
    CEndpoint host.val.nodeCount :=
  ⟨occurrence.nodeMap endpoint.node,
    occurrence.portEquivForNode endpoint.node endpoint.port⟩

theorem properChildren_exact
    (occurrence : Occurrence pattern host) :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.childrenOf region).map occurrence.regionMap)
        (host.val.childrenOf (occurrence.regionMap region)) :=
  occurrence.proper_children_exact

theorem properNodes_exact
    (occurrence : Occurrence pattern host) :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.nodesAt region).map occurrence.nodeMap)
        (host.val.nodesAt (occurrence.regionMap region)) :=
  occurrence.proper_nodes_exact

theorem properWires_exact
    (occurrence : Occurrence pattern host) :
    ∀ region, region ≠ pattern.val.diagram.root →
      List.Perm
        ((pattern.val.diagram.wiresAt region).map occurrence.wireMap)
        (host.val.wiresAt (occurrence.regionMap region)) :=
  occurrence.proper_wires_exact

/-- Ordered host attachments, including every repeated boundary position. -/
def boundaryAttachments
    (occurrence : Occurrence pattern host) :
    List host.val.WireId :=
  pattern.val.boundary.map occurrence.wireMap

@[simp] theorem boundaryAttachments_length
    (occurrence : Occurrence pattern host) :
    occurrence.boundaryAttachments.length =
      pattern.val.boundary.length := by
  simp [boundaryAttachments]

/-- Ordered aliases come only from the authoritative open-pattern boundary. -/
def boundaryAliases (occurrence : Occurrence pattern host)
    (left right : Nat) : Prop :=
  ∃ wire,
    occurrence.boundaryAttachments[left]? = some wire ∧
      occurrence.boundaryAttachments[right]? = some wire

instance (occurrence : Occurrence pattern host)
    (left right : Nat) :
    Decidable (occurrence.boundaryAliases left right) := by
  unfold boundaryAliases
  infer_instance

theorem boundary_attachment_signature
    (occurrence : Occurrence pattern host)
    (position : Fin pattern.val.boundary.length) :
    (host.val.wires
      (occurrence.boundaryAttachments.get
        ⟨position.val, by
          rw [boundaryAttachments_length occurrence]
          exact position.isLt⟩)).sig =
      (pattern.val.diagram.wires
        (pattern.val.boundary.get position)).sig := by
  simp only [boundaryAttachments, List.get_eq_getElem,
    List.getElem_map]
  exact occurrence.wire_signature _

private theorem subtreeRoot_child
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId)
    (member :
      region ∈ occurrenceSubtreeRoots pattern host occurrence.regionMap) :
    host.val.regions region = .cut occurrence.region := by
  rcases List.mem_map.mp member with ⟨source, sourceMember, mapped⟩
  subst region
  have childData :
      ∃ parent,
        pattern.val.diagram.regions source = .cut parent ∧
          parent = pattern.val.diagram.root := by
    simp only [ConcreteDiagram.childrenOf,
      ConcreteDiagram.regionsList, List.mem_filter,
      Data.Finite.mem_allFin, true_and] at sourceMember
    cases data : pattern.val.diagram.regions source with
    | sheet => simp [data] at sourceMember
    | cut parent =>
        have same : parent = pattern.val.diagram.root :=
          eq_of_beq (by simpa [data] using sourceMember)
        exact ⟨parent, rfl, same⟩
  rcases childData with ⟨parent, data, same⟩
  rw [occurrence.parentage source parent data, same, occurrence.root]

private theorem directNode_at_anchor
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId)
    (member :
      node ∈ occurrenceDirectNodes pattern host occurrence.nodeMap) :
    (host.val.nodes node).region = occurrence.region := by
  rcases List.mem_map.mp member with ⟨source, sourceMember, mapped⟩
  subst node
  have sourceRegion :
      (pattern.val.diagram.nodes source).region =
        pattern.val.diagram.root := by
    simpa [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin] using
        (List.mem_filter.mp sourceMember).2
  have corresponds := occurrence.node_corresponds source
  cases sourceData : pattern.val.diagram.nodes source <;>
    simp [OccurrenceNodeCorresponds, sourceData] at corresponds sourceRegion
  all_goals
    subst_vars
    simpa [occurrence.root] using
      congrArg CNode.region corresponds

private theorem explicitWire_at_anchor
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (member :
      wire ∈ occurrenceExplicitWires pattern host occurrence.wireMap) :
    (host.val.wires wire).scope = occurrence.region := by
  rcases List.mem_map.mp member with ⟨source, sourceMember, mapped⟩
  subst wire
  have parts := List.mem_filter.mp sourceMember
  have sourceScope :
      (pattern.val.diagram.wires source).scope =
        pattern.val.diagram.root := by
    simpa [ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin] using parts.1
  have nonboundary : source ∉ pattern.val.boundary :=
    of_decide_eq_true parts.2
  rw [occurrence.internal_wire_scope source nonboundary,
    sourceScope, occurrence.root]

/-- Derive the exact consumable selection represented by this occurrence. -/
def toSelection
    (occurrence : Occurrence pattern host) :
    CheckedSelection host :=
  occurrence.checkedSelection

@[simp] theorem toSelection_region
    (occurrence : Occurrence pattern host) :
    occurrence.toSelection.region = occurrence.region := by
  unfold toSelection CheckedSelection.region
  rw [occurrence.checkedSelection_input]
  rfl

@[simp] theorem toSelection_subtreeRoots
    (occurrence : Occurrence pattern host) :
    occurrence.toSelection.subtreeRoots =
      occurrenceSubtreeRoots pattern host occurrence.regionMap := by
  unfold toSelection CheckedSelection.subtreeRoots
  rw [occurrence.checkedSelection_input]
  rfl

@[simp] theorem toSelection_directNodes
    (occurrence : Occurrence pattern host) :
    occurrence.toSelection.directNodes =
      occurrenceDirectNodes pattern host occurrence.nodeMap := by
  unfold toSelection CheckedSelection.directNodes
  rw [occurrence.checkedSelection_input]
  rfl

@[simp] theorem toSelection_explicitWires
    (occurrence : Occurrence pattern host) :
    occurrence.toSelection.explicitWires =
      occurrenceExplicitWires pattern host occurrence.wireMap := by
  unfold toSelection CheckedSelection.explicitWires
  rw [occurrence.checkedSelection_input]
  rfl

@[simp] theorem mem_toSelection_allRegions
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId) :
    region ∈ occurrence.toSelection.allRegions ↔
      ∃ root,
        root ∈ occurrenceSubtreeRoots pattern host occurrence.regionMap ∧
          host.val.Encloses root region := by
  rw [CheckedSelection.mem_allRegions]
  unfold CheckedSelection.IsSelectedRegion
  rw [toSelection_subtreeRoots]

private theorem mappedRootChildPath
    (occurrence : Occurrence pattern host) :
    ∀ steps (region : pattern.val.diagram.RegionId),
      pattern.val.diagram.climb (steps + 1) region =
          some pattern.val.diagram.root →
        ∃ child,
          child ∈
              pattern.val.diagram.childrenOf pattern.val.diagram.root ∧
            host.val.climb steps (occurrence.regionMap region) =
              some (occurrence.regionMap child) := by
  intro steps
  induction steps with
  | zero =>
      intro region climbed
      cases regionData : pattern.val.diagram.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at climbed
      | cut parent =>
          have parentRoot : parent = pattern.val.diagram.root := by
            simpa [ConcreteDiagram.climb, regionData] using climbed
          subst parent
          refine ⟨region, ?_, rfl⟩
          simp [ConcreteDiagram.childrenOf,
            ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
            regionData]
  | succ steps induction =>
      intro region climbed
      cases regionData : pattern.val.diagram.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at climbed
      | cut parent =>
          have parentClimb :
              pattern.val.diagram.climb (steps + 1) parent =
                some pattern.val.diagram.root := by
            simpa [Nat.succ_add, ConcreteDiagram.climb, regionData] using
              climbed
          obtain ⟨child, childMember, hostClimb⟩ :=
            induction parent parentClimb
          refine ⟨child, childMember, ?_⟩
          rw [ConcreteDiagram.climb,
            occurrence.maps_parentage region parent regionData]
          exact hostClimb

private theorem mappedNonrootRegion_selected
    (occurrence : Occurrence pattern host)
    (region : pattern.val.diagram.RegionId)
    (nonroot : region ≠ pattern.val.diagram.root) :
    occurrence.regionMap region ∈ occurrence.toSelection.allRegions := by
  have reaches :
      pattern.val.diagram.Encloses pattern.val.diagram.root region := by
    have allChecked :=
      (List.all_eq_true.mp
        pattern.property.diagram.all_regions_reach_root)
        region (Data.Finite.mem_allFin region)
    exact of_decide_eq_true allChecked
  unfold ConcreteDiagram.Encloses at reaches
  rw [List.any_eq_true] at reaches
  obtain ⟨⟨steps, bound⟩, _, climbedChecked⟩ := reaches
  have climbed :
      pattern.val.diagram.climb steps region =
        some pattern.val.diagram.root :=
    eq_of_beq climbedChecked
  cases steps with
  | zero =>
      simp only [ConcreteDiagram.climb] at climbed
      exact False.elim (nonroot (Option.some.inj climbed))
  | succ steps =>
      obtain ⟨child, childMember, hostClimb⟩ :=
        mappedRootChildPath occurrence steps region
          (by simpa using climbed)
      rw [mem_toSelection_allRegions]
      refine ⟨occurrence.regionMap child, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨child, childMember, rfl⟩
      · unfold ConcreteDiagram.Encloses
        rw [List.any_eq_true]
        refine ⟨⟨steps, ?_⟩, Data.Finite.mem_allFin _, ?_⟩
        · have countLe :
              pattern.val.diagram.regionCount ≤ host.val.regionCount :=
            Data.Finite.fin_card_le_of_injective occurrence.regionMap
              occurrence.regionMap_injective
          omega
        · exact beq_iff_eq.mpr hostClimb

private theorem selectedDescendant_hasSource
    (occurrence : Occurrence pattern host)
    (source : pattern.val.diagram.RegionId)
    (sourceNonroot : source ≠ pattern.val.diagram.root) :
    ∀ steps (region : host.val.RegionId),
      host.val.climb steps region =
          some (occurrence.regionMap source) →
        ∃ patternRegion,
          patternRegion ≠ pattern.val.diagram.root ∧
            occurrence.regionMap patternRegion = region := by
  intro steps
  induction steps with
  | zero =>
      intro region climbed
      exact ⟨source, sourceNonroot, Option.some.inj climbed.symm⟩
  | succ steps induction =>
      intro region climbed
      cases regionData : host.val.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at climbed
      | cut parent =>
          have parentClimb :
              host.val.climb steps parent =
                some (occurrence.regionMap source) := by
            simpa [ConcreteDiagram.climb, regionData] using climbed
          obtain ⟨patternParent, parentNonroot, parentMapped⟩ :=
            induction parent parentClimb
          have hostChild :
              region ∈ host.val.childrenOf
                (occurrence.regionMap patternParent) := by
            simp [ConcreteDiagram.childrenOf,
              ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
              regionData, parentMapped]
          have mappedChild :
              region ∈
                (pattern.val.diagram.childrenOf patternParent).map
                  occurrence.regionMap :=
            (occurrence.properChildren_exact patternParent
              parentNonroot).mem_iff.mpr hostChild
          obtain ⟨patternChild, childMember, childMapped⟩ :=
            List.mem_map.mp mappedChild
          have childNonroot :
              patternChild ≠ pattern.val.diagram.root := by
            intro same
            subst patternChild
            simp [ConcreteDiagram.childrenOf,
              ConcreteDiagram.regionsList,
              Data.Finite.mem_allFin] at childMember
            rw [pattern.property.diagram.root_is_sheet] at childMember
            contradiction
          exact ⟨patternChild, childNonroot, childMapped⟩

/-- Exact selected-region carrier: precisely mapped nonroot pattern regions. -/
theorem mem_toSelection_allRegions_iff_image
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId) :
    region ∈ occurrence.toSelection.allRegions ↔
      ∃ patternRegion,
        patternRegion ≠ pattern.val.diagram.root ∧
          occurrence.regionMap patternRegion = region := by
  constructor
  · intro selected
    rw [mem_toSelection_allRegions] at selected
    obtain ⟨mappedRoot, mappedRootMember, enclosed⟩ := selected
    obtain ⟨patternRoot, rootMember, rootMapped⟩ :=
      List.mem_map.mp mappedRootMember
    have rootNonroot :
        patternRoot ≠ pattern.val.diagram.root := by
      intro same
      subst patternRoot
      simp [ConcreteDiagram.childrenOf,
        ConcreteDiagram.regionsList,
        Data.Finite.mem_allFin] at rootMember
      rw [pattern.property.diagram.root_is_sheet] at rootMember
      contradiction
    unfold ConcreteDiagram.Encloses at enclosed
    rw [List.any_eq_true] at enclosed
    obtain ⟨steps, _, climbedChecked⟩ := enclosed
    have climbed :
        host.val.climb steps region =
          some (occurrence.regionMap patternRoot) := by
      rw [← rootMapped] at climbedChecked
      exact eq_of_beq climbedChecked
    exact selectedDescendant_hasSource occurrence patternRoot
      rootNonroot steps region climbed
  · rintro ⟨patternRegion, nonroot, rfl⟩
    exact mappedNonrootRegion_selected occurrence patternRegion nonroot

private theorem mappedNode_region
    (occurrence : Occurrence pattern host)
    (node : pattern.val.diagram.NodeId) :
    (host.val.nodes (occurrence.nodeMap node)).region =
      occurrence.regionMap (pattern.val.diagram.nodes node).region := by
  have corresponds := occurrence.node_correspondence node
  cases sourceData : pattern.val.diagram.nodes node <;>
    simp [OccurrenceNodeCorresponds, sourceData] at corresponds
  all_goals
    simpa [sourceData] using congrArg CNode.region corresponds

@[simp] theorem mem_toSelection_allNodes
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId) :
    node ∈ occurrence.toSelection.allNodes ↔
      node ∈ occurrenceDirectNodes pattern host occurrence.nodeMap ∨
        ∃ root,
          root ∈ occurrenceSubtreeRoots pattern host occurrence.regionMap ∧
            host.val.Encloses root (host.val.nodes node).region := by
  rw [CheckedSelection.mem_allNodes]
  unfold CheckedSelection.IsSelectedNode
  rw [toSelection_directNodes, mem_toSelection_allRegions]

/-- Exact selected-node carrier: precisely mapped pattern nodes. -/
theorem mem_toSelection_allNodes_iff_image
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId) :
    node ∈ occurrence.toSelection.allNodes ↔
      ∃ patternNode, occurrence.nodeMap patternNode = node := by
  constructor
  · intro selected
    rw [mem_toSelection_allNodes] at selected
    rcases selected with direct | ⟨mappedRoot, mappedRootMember, enclosed⟩
    · obtain ⟨patternNode, _, mapped⟩ := List.mem_map.mp direct
      exact ⟨patternNode, mapped⟩
    · obtain ⟨patternRoot, rootMember, rootMapped⟩ :=
        List.mem_map.mp mappedRootMember
      have rootNonroot :
          patternRoot ≠ pattern.val.diagram.root := by
        intro same
        subst patternRoot
        simp [ConcreteDiagram.childrenOf,
          ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin] at rootMember
        rw [pattern.property.diagram.root_is_sheet] at rootMember
        contradiction
      have selectedRegion :
          (host.val.nodes node).region ∈
            occurrence.toSelection.allRegions := by
        rw [mem_toSelection_allRegions]
        exact ⟨mappedRoot, mappedRootMember, enclosed⟩
      obtain ⟨patternRegion, patternRegionNonroot, regionMapped⟩ :=
        (mem_toSelection_allRegions_iff_image occurrence
          (host.val.nodes node).region).mp selectedRegion
      have hostMember :
          node ∈ host.val.nodesAt
            (occurrence.regionMap patternRegion) := by
        simp [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList,
          Data.Finite.mem_allFin, regionMapped]
      have mappedMember :
          node ∈
            (pattern.val.diagram.nodesAt patternRegion).map
              occurrence.nodeMap :=
        (occurrence.properNodes_exact patternRegion
          patternRegionNonroot).mem_iff.mpr hostMember
      obtain ⟨patternNode, _, mapped⟩ := List.mem_map.mp mappedMember
      exact ⟨patternNode, mapped⟩
  · rintro ⟨patternNode, rfl⟩
    rw [mem_toSelection_allNodes]
    by_cases atRoot :
        (pattern.val.diagram.nodes patternNode).region =
          pattern.val.diagram.root
    · left
      exact List.mem_map.mpr
        ⟨patternNode, by
          simp [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList,
            Data.Finite.mem_allFin, atRoot], rfl⟩
    · right
      have mappedSelected :=
        mappedNonrootRegion_selected occurrence
          (pattern.val.diagram.nodes patternNode).region atRoot
      rw [mem_toSelection_allRegions] at mappedSelected
      simpa [mappedNode_region occurrence patternNode] using mappedSelected

@[simp] theorem mem_toSelection_internalWires
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId) :
    wire ∈ occurrence.toSelection.internalWires ↔
      (∃ root,
        root ∈ occurrenceSubtreeRoots pattern host occurrence.regionMap ∧
          host.val.Encloses root (host.val.wires wire).scope) ∨
      wire ∈ occurrenceExplicitWires pattern host occurrence.wireMap := by
  rw [CheckedSelection.mem_internalWires]
  unfold CheckedSelection.IsInternal
  rw [mem_toSelection_allRegions, toSelection_explicitWires]

private theorem boundaryWire_scope_eq_root
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    (wire : pattern.val.diagram.WireId)
    (member : wire ∈ pattern.val.boundary) :
    (pattern.val.diagram.wires wire).scope =
      pattern.val.diagram.root := by
  have checked :=
    (List.all_eq_true.mp pattern.property.boundary_root_scoped)
      wire member
  exact of_decide_eq_true checked

/--
Exact selected-wire carrier: precisely mapped nonboundary pattern wires.
Boundary multiplicity is deliberately not collapsed into this carrier theorem.
-/
theorem mem_toSelection_internalWires_iff_image
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId) :
    wire ∈ occurrence.toSelection.internalWires ↔
      ∃ patternWire,
        patternWire ∉ pattern.val.boundary ∧
          occurrence.wireMap patternWire = wire := by
  constructor
  · intro selected
    rw [mem_toSelection_internalWires] at selected
    rcases selected with
      ⟨mappedRoot, mappedRootMember, enclosed⟩ | explicit
    · have selectedScope :
          (host.val.wires wire).scope ∈
            occurrence.toSelection.allRegions := by
        rw [mem_toSelection_allRegions]
        exact ⟨mappedRoot, mappedRootMember, enclosed⟩
      obtain ⟨patternRegion, patternRegionNonroot, regionMapped⟩ :=
        (mem_toSelection_allRegions_iff_image occurrence
          (host.val.wires wire).scope).mp selectedScope
      have hostMember :
          wire ∈ host.val.wiresAt
            (occurrence.regionMap patternRegion) := by
        simp [ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList,
          Data.Finite.mem_allFin, regionMapped]
      have mappedMember :
          wire ∈
            (pattern.val.diagram.wiresAt patternRegion).map
              occurrence.wireMap :=
        (occurrence.properWires_exact patternRegion
          patternRegionNonroot).mem_iff.mpr hostMember
      obtain ⟨patternWire, patternWireMember, mapped⟩ :=
        List.mem_map.mp mappedMember
      have sourceScope :
          (pattern.val.diagram.wires patternWire).scope =
            patternRegion := by
        simpa [ConcreteDiagram.wiresAt,
          ConcreteDiagram.wiresList,
          Data.Finite.mem_allFin] using
            (List.mem_filter.mp patternWireMember).2
      have nonboundary : patternWire ∉ pattern.val.boundary := by
        intro boundary
        have rootScope :=
          boundaryWire_scope_eq_root (pattern := pattern)
            patternWire boundary
        exact patternRegionNonroot (sourceScope.symm.trans rootScope)
      exact ⟨patternWire, nonboundary, mapped⟩
    · obtain ⟨patternWire, patternWireMember, mapped⟩ :=
        List.mem_map.mp explicit
      have parts := List.mem_filter.mp patternWireMember
      exact
        ⟨patternWire, of_decide_eq_true parts.2, mapped⟩
  · rintro ⟨patternWire, nonboundary, rfl⟩
    rw [mem_toSelection_internalWires]
    by_cases atRoot :
        (pattern.val.diagram.wires patternWire).scope =
          pattern.val.diagram.root
    · right
      exact List.mem_map.mpr
        ⟨patternWire, by
          rw [List.mem_filter]
          exact ⟨by
            simp [ConcreteDiagram.wiresAt,
              ConcreteDiagram.wiresList,
              Data.Finite.mem_allFin, atRoot],
            decide_eq_true nonboundary⟩, rfl⟩
    · left
      have mappedSelected :=
        mappedNonrootRegion_selected occurrence
          (pattern.val.diagram.wires patternWire).scope atRoot
      rw [mem_toSelection_allRegions] at mappedSelected
      simpa [occurrence.internalWire_scope patternWire nonboundary] using
        mappedSelected

/--
Touching requires a selected endpoint. In particular, an endpoint-free
boundary attachment is not a touching wire.
-/
@[simp] theorem mem_toSelection_touchingWires
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId) :
    wire ∈ occurrence.toSelection.touchingWires ↔
      wire ∉ occurrence.toSelection.internalWires ∧
        ∃ endpoint ∈ (host.val.wires wire).endpoints,
          endpoint.node ∈ occurrence.toSelection.allNodes := by
  rw [CheckedSelection.mem_touchingWires]
  unfold CheckedSelection.IsTouching
  rw [← CheckedSelection.mem_internalWires]
  rfl

end Occurrence

end VisualProof
