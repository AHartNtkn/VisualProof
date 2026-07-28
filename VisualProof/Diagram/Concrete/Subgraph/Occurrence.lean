import VisualProof.Diagram.Concrete.Subgraph.Selection

namespace VisualProof

namespace ConcreteDiagram

/-- Wire owners of an identity's storage ports; only the resulting multiset matters. -/
def identityOwners (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) (arity : Nat) : List diagram.WireId :=
  (List.range arity).filterMap fun index =>
    diagram.endpointOwner? ⟨node, .identity index⟩

end ConcreteDiagram

/-- Structural preservation of one node under injective occurrence maps. -/
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

/--
A supplied exact occurrence certificate. Besides the forward embeddings it
contains inverse maps on the selected carriers. The ordered boundary enumerates
the finite subtype of actual host crossing incidences exactly once; repeating a
wire therefore requires distinct stored endpoints and cannot be fabricated by
repeating a list entry.
-/
structure Occurrence
    (pattern host : CheckedDiagram definitions) where
  selection : CheckedSelection host
  regionMap : pattern.val.RegionId → host.val.RegionId
  nodeMap : pattern.val.NodeId → host.val.NodeId
  wireMap : pattern.val.WireId → host.val.WireId
  regionInverse :
    (target : host.val.RegionId) →
      target ∈ selection.regions → pattern.val.RegionId
  nodeInverse :
    (target : host.val.NodeId) →
      target ∈ selection.nodes → pattern.val.NodeId
  wireInverse :
    (target : host.val.WireId) →
      target ∈ selection.wires → pattern.val.WireId
  region_injective : Function.Injective regionMap
  node_injective : Function.Injective nodeMap
  wire_injective : Function.Injective wireMap
  root : regionMap pattern.val.root = selection.root
  region_mem : ∀ region, regionMap region ∈ selection.regions
  region_exact :
    ∀ target, target ∈ selection.regions →
      ∃ source, regionMap source = target
  parentage :
    ∀ region parent,
      pattern.val.regions region = .cut parent →
        host.val.regions (regionMap region) = .cut (regionMap parent)
  node_corresponds :
    ∀ node,
      OccurrenceNodeCorresponds pattern.val host.val regionMap node (nodeMap node)
  node_mem : ∀ node, nodeMap node ∈ selection.nodes
  node_exact :
    ∀ target, target ∈ selection.nodes →
      ∃ source, nodeMap source = target
  wire_signature :
    ∀ wire,
      (host.val.wires (wireMap wire)).sig =
        (pattern.val.wires wire).sig
  wire_mem : ∀ wire, wireMap wire ∈ selection.wires
  wire_exact :
    ∀ target, target ∈ selection.wires →
      ∃ source, wireMap source = target
  region_left_inverse :
    ∀ source, regionInverse (regionMap source) (region_mem source) = source
  node_left_inverse :
    ∀ source, nodeInverse (nodeMap source) (node_mem source) = source
  wire_left_inverse :
    ∀ source, wireInverse (wireMap source) (wire_mem source) = source
  region_right_inverse :
    ∀ target (member : target ∈ selection.regions),
      regionMap (regionInverse target member) = target
  node_right_inverse :
    ∀ target (member : target ∈ selection.nodes),
      nodeMap (nodeInverse target member) = target
  wire_right_inverse :
    ∀ target (member : target ∈ selection.wires),
      wireMap (wireInverse target member) = target
  boundary : List (CheckedSelection.BoundaryCrossing selection)
  boundary_nodup : boundary.Nodup
  boundary_complete :
    ∀ crossing : CheckedSelection.BoundaryCrossing selection,
      crossing ∈ boundary
  scope_preserved_internal :
    ∀ wire, (host.val.wires (wireMap wire)).scope ∈ selection.regions →
      (host.val.wires (wireMap wire)).scope =
        regionMap (pattern.val.wires wire).scope
  positional_incidence :
    ∀ node port,
      (match pattern.val.nodes node with
        | .identity _ _ _ => False
        | _ => True) →
      host.val.endpointOwner? ⟨nodeMap node, port⟩ =
        (pattern.val.endpointOwner? ⟨node, port⟩).map wireMap
  identity_incidence :
    ∀ node region sig arity,
      pattern.val.nodes node = CNode.identity region sig arity →
        List.Perm
          ((pattern.val.identityOwners node arity).map wireMap)
          (host.val.identityOwners (nodeMap node) arity)

namespace Occurrence

/-- Ordered host attachments; aliases are projections of distinct crossings. -/
def boundaryAttachments (occurrence : Occurrence pattern host) :
    List host.val.WireId :=
  occurrence.boundary.map
    CheckedSelection.BoundaryCrossing.wire

/-- Ordered extracted source classes, recovered through the occurrence inverse. -/
def boundarySources (occurrence : Occurrence pattern host) :
    List pattern.val.WireId :=
  occurrence.boundary.map fun crossing =>
    occurrence.wireInverse crossing.wire crossing.wire_selected

/-- Two ordered boundary positions alias exactly when their crossings name one wire. -/
def boundaryAliases (occurrence : Occurrence pattern host)
    (left right : Nat) : Prop :=
  ∃ wire,
    occurrence.boundaryAttachments[left]? = some wire ∧
      occurrence.boundaryAttachments[right]? = some wire

instance (occurrence : Occurrence pattern host) (left right : Nat) :
    Decidable (occurrence.boundaryAliases left right) := by
  unfold boundaryAliases
  infer_instance

/-- Out-of-range indices are not boundary positions and therefore cannot alias. -/
theorem not_boundaryAliases_of_left_out_of_bounds
    (occurrence : Occurrence pattern host)
    (left right : Nat)
    (outOfBounds : occurrence.boundaryAttachments.length ≤ left) :
    ¬ occurrence.boundaryAliases left right := by
  rintro ⟨wire, leftAt, _⟩
  have missing : occurrence.boundaryAttachments[left]? = none := by
    exact List.getElem?_eq_none outOfBounds
  rw [missing] at leftAt
  contradiction

/-- The right index is equally required to designate a genuine position. -/
theorem not_boundaryAliases_of_right_out_of_bounds
    (occurrence : Occurrence pattern host)
    (left right : Nat)
    (outOfBounds : occurrence.boundaryAttachments.length ≤ right) :
    ¬ occurrence.boundaryAliases left right := by
  rintro ⟨wire, _, rightAt⟩
  have missing : occurrence.boundaryAttachments[right]? = none := by
    exact List.getElem?_eq_none outOfBounds
  rw [missing] at rightAt
  contradiction

theorem boundary_attachment_signature
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId) :
    (host.val.wires (occurrence.wireMap wire)).sig =
      (pattern.val.wires wire).sig :=
  occurrence.wire_signature wire

end Occurrence

end VisualProof
