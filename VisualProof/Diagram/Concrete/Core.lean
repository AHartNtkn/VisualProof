import VisualProof.Data.Finite
import VisualProof.Theory.Definition

namespace VisualProof

instance : DecidableEq Sig := fun left right =>
  if h : left == right then
    isTrue (eq_of_beq h)
  else
    isFalse fun equality => h (by subst equality; simp)

/-- A concrete region is either the unique sheet or a cut with a stored parent. -/
inductive CRegion (regionCount : Nat)
  | sheet
  | cut (parent : Fin regionCount)
  deriving Repr, DecidableEq

/-- Concrete node ports are derived positions, never an independent table. -/
inductive CPort
  | head
  | arg (index : Nat)
  | identity (index : Nat)
  deriving Repr, DecidableEq

/-- An endpoint names a node and one constructor-derived port. -/
structure CEndpoint (nodeCount : Nat) where
  node : Fin nodeCount
  port : CPort
  deriving Repr, DecidableEq

/-- The three concrete zero-signature node forms. -/
inductive CNode (regionCount definitionCount : Nat)
  | atom (region : Fin regionCount) (args : List Sig)
  | ref (region : Fin regionCount) (definition : Fin definitionCount)
      (args : List Sig)
  | identity (region : Fin regionCount) (sig : Sig) (arity : Nat)
  deriving Repr, DecidableEq

namespace CNode

def region : CNode regionCount definitionCount → Fin regionCount
  | .atom region _ | .ref region _ _ | .identity region _ _ => region

end CNode

/-- A wire owns its signature, lexical scope, and finite endpoint incidence. -/
structure CWire (regionCount nodeCount : Nat) where
  sig : Sig
  scope : Fin regionCount
  endpoints : List (CEndpoint nodeCount)
  deriving Repr, DecidableEq

/-- The normalized concrete graph: separate finite IDs and total ownership tables. -/
structure ConcreteDiagram (definitionCount : Nat) where
  regionCount : Nat
  nodeCount : Nat
  wireCount : Nat
  root : Fin regionCount
  regions : Fin regionCount → CRegion regionCount
  nodes : Fin nodeCount → CNode regionCount definitionCount
  wires : Fin wireCount → CWire regionCount nodeCount

/-- An ordered external boundary may repeat a wire to express aliases. -/
structure OpenConcreteDiagram (definitionCount : Nat) where
  diagram : ConcreteDiagram definitionCount
  boundary : List (Fin diagram.wireCount)

namespace ConcreteDiagram

abbrev RegionId (diagram : ConcreteDiagram definitionCount) :=
  Fin diagram.regionCount

abbrev NodeId (diagram : ConcreteDiagram definitionCount) :=
  Fin diagram.nodeCount

abbrev WireId (diagram : ConcreteDiagram definitionCount) :=
  Fin diagram.wireCount

/-- Follow exactly `steps` stored parent edges, stopping at a sheet. -/
def climb (diagram : ConcreteDiagram definitionCount) :
    Nat → diagram.RegionId → Option diagram.RegionId
  | 0, region => some region
  | steps + 1, region =>
      match diagram.regions region with
      | .sheet => none
      | .cut parent => climb diagram steps parent

/-- Bounded ancestry; the bound prevents cycles from masquerading as trees. -/
def Encloses (diagram : ConcreteDiagram definitionCount)
    (ancestor descendant : diagram.RegionId) : Prop :=
  (Data.Finite.allFin (diagram.regionCount + 1)).any (fun steps =>
    diagram.climb steps descendant == some ancestor) = true

instance (diagram : ConcreteDiagram definitionCount)
    (ancestor descendant : diagram.RegionId) :
    Decidable (diagram.Encloses ancestor descendant) := by
  unfold Encloses
  infer_instance

@[simp] theorem climb_zero (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) :
    diagram.climb 0 region = some region := rfl

theorem encloses_refl (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) :
    diagram.Encloses region region := by
  unfold Encloses
  rw [List.any_eq_true]
  exact ⟨0, Data.Finite.mem_allFin 0, by simp⟩

/-- The complete, deterministic finite support of each identifier sort. -/
def regionsList (diagram : ConcreteDiagram definitionCount) :
    List diagram.RegionId :=
  Data.Finite.allFin diagram.regionCount

def nodesList (diagram : ConcreteDiagram definitionCount) :
    List diagram.NodeId :=
  Data.Finite.allFin diagram.nodeCount

def wiresList (diagram : ConcreteDiagram definitionCount) :
    List diagram.WireId :=
  Data.Finite.allFin diagram.wireCount

def wiresAt (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) : List diagram.WireId :=
  diagram.wiresList.filter fun wire => (diagram.wires wire).scope == region

def nodesAt (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) : List diagram.NodeId :=
  diagram.nodesList.filter fun node => (diagram.nodes node).region == region

def childrenOf (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) : List diagram.RegionId :=
  diagram.regionsList.filter fun child =>
    match diagram.regions child with
    | .sheet => false
    | .cut parent => parent == region

/-- The ports implied by a node constructor, in positional order. -/
def requiredPorts (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) : List CPort :=
  match diagram.nodes node with
  | .atom _ args => .head :: (List.range args.length).map .arg
  | .ref _ _ args => (List.range args.length).map .arg
  | .identity _ _ arity => (List.range arity).map .identity

/-- Every stored incidence in canonical wire order. -/
def endpointOccurrences (diagram : ConcreteDiagram definitionCount) :
    List (diagram.WireId × CEndpoint diagram.nodeCount) :=
  diagram.wiresList.flatMap fun wire =>
    (diagram.wires wire).endpoints.map fun endpoint => (wire, endpoint)

def endpointOwner? (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) : Option diagram.WireId :=
  (diagram.endpointOccurrences.find? fun occurrence =>
    occurrence.2 == endpoint).map Prod.fst

end ConcreteDiagram

/-- Rename a raw concrete region through a finite region equivalence. -/
def CRegion.rename
    (regions : Data.Finite.FiniteEquiv (Fin leftCount) (Fin rightCount)) :
    CRegion leftCount → CRegion rightCount
  | .sheet => .sheet
  | .cut parent => .cut (regions parent)

@[simp] theorem CRegion.rename_sheet
    (regions : Data.Finite.FiniteEquiv (Fin leftCount) (Fin rightCount)) :
    (CRegion.sheet : CRegion leftCount).rename regions = .sheet := rfl

/-- Rename a raw concrete node through a finite region equivalence. -/
def CNode.rename
    (regions : Data.Finite.FiniteEquiv (Fin leftCount) (Fin rightCount)) :
    CNode leftCount definitionCount → CNode rightCount definitionCount
  | .atom region args => .atom (regions region) args
  | .ref region definition args => .ref (regions region) definition args
  | .identity region sig arity => .identity (regions region) sig arity

@[simp] theorem CNode.region_rename
    (regions : Data.Finite.FiniteEquiv (Fin leftCount) (Fin rightCount))
    (node : CNode leftCount definitionCount) :
    (node.rename regions).region = regions node.region := by
  cases node <;> rfl

/--
Port correspondence preserves atom/ref positions exactly. Identity indices are
storage positions and therefore correspond only by identity incidence.
-/
def PortCorresponds
    (left : ConcreteDiagram definitionCount)
    (right : ConcreteDiagram definitionCount)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (endpoint : CEndpoint left.nodeCount)
    (candidate : CEndpoint right.nodeCount) : Prop :=
  candidate.node = nodes endpoint.node ∧
    match left.nodes endpoint.node, right.nodes candidate.node with
    | .identity _ leftSig leftArity, .identity _ rightSig rightArity =>
        leftSig = rightSig ∧ leftArity = rightArity ∧
          (∃ leftIndex rightIndex,
            endpoint.port = .identity leftIndex ∧
              candidate.port = .identity rightIndex)
    | _, _ => candidate.port = endpoint.port

/--
A raw concrete isomorphism is a finite renaming preserving every owned table.
Endpoint order and identity storage indices are intentionally nonsemantic.
-/
structure ConcreteIso {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length) where
  regions : Data.Finite.FiniteEquiv left.RegionId right.RegionId
  nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId
  wires : Data.Finite.FiniteEquiv left.WireId right.WireId
  root : regions left.root = right.root
  region_table :
    ∀ region,
      right.regions (regions region) =
        (left.regions region).rename regions
  node_table :
    ∀ node,
      right.nodes (nodes node) =
        (left.nodes node).rename regions
  wire_signature :
    ∀ wire, (right.wires (wires wire)).sig = (left.wires wire).sig
  wire_scope :
    ∀ wire,
      (right.wires (wires wire)).scope =
        regions (left.wires wire).scope
  endpoint_forward :
    ∀ wire endpoint,
      endpoint ∈ (left.wires wire).endpoints →
        ∃ candidate,
          candidate ∈ (right.wires (wires wire)).endpoints ∧
            PortCorresponds left right nodes endpoint candidate
  endpoint_backward :
    ∀ wire candidate,
      candidate ∈ (right.wires (wires wire)).endpoints →
        ∃ endpoint,
          endpoint ∈ (left.wires wire).endpoints ∧
            PortCorresponds left right nodes endpoint candidate

end VisualProof
