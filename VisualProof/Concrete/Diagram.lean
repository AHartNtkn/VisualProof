namespace VisualProof.Concrete

inductive CRegion (regions : Nat)
  | sheet
  | cut (parent : Fin regions)
  | bubble (parent : Fin regions) (arity : Nat)
  deriving DecidableEq

inductive CPort
  | arg (index : Nat)
  deriving DecidableEq

structure CEndpoint (nodes : Nat) where
  node : Fin nodes
  port : CPort
  deriving DecidableEq

inductive CNode (regions : Nat)
  | atom (region binder : Fin regions)
  | identity (region : Fin regions) (arity : Nat)
structure CWire (regions nodes : Nat) where
  scope : Fin regions
  endpoints : List (CEndpoint nodes)

structure Diagram where
  regionCount : Nat
  nodeCount : Nat
  wireCount : Nat
  root : Fin regionCount
  regions : Fin regionCount -> CRegion regionCount
  nodes : Fin nodeCount -> CNode regionCount
  wires : Fin wireCount -> CWire regionCount nodeCount

structure OpenDiagram where
  diagram : Diagram
  boundary : List (Fin diagram.wireCount)

namespace CRegion

def parent? : CRegion regions -> Option (Fin regions)
  | .sheet => none
  | .cut parent => some parent
  | .bubble parent _ => some parent

end CRegion

namespace CNode

def region : CNode regions -> Fin regions
  | .atom region _ => region
  | .identity region _ => region
end CNode

namespace Diagram

def climb (d : Diagram) :
    Nat -> Fin d.regionCount -> Option (Fin d.regionCount)
  | 0, region => some region
  | steps + 1, region =>
      match (d.regions region).parent? with
      | none => none
      | some parent => d.climb steps parent

@[simp] theorem climb_zero (d : Diagram)
    (region : Fin d.regionCount) :
    d.climb 0 region = some region := rfl

def Encloses (d : Diagram)
    (ancestor descendant : Fin d.regionCount) : Prop :=
  exists steps : Fin (d.regionCount + 1),
    d.climb steps descendant = some ancestor

namespace Encloses

theorem refl (d : Diagram) (region : Fin d.regionCount) :
    d.Encloses region region := by
  exact ⟨0, d.climb_zero region⟩

end Encloses

instance (d : Diagram)
    (ancestor descendant : Fin d.regionCount) :
    Decidable (d.Encloses ancestor descendant) := by
  unfold Encloses
  infer_instance

def ReachesRoot (d : Diagram)
    (region : Fin d.regionCount) : Prop :=
  d.Encloses d.root region

instance (d : Diagram) (region : Fin d.regionCount) :
    Decidable (d.ReachesRoot region) := by
  unfold ReachesRoot
  infer_instance

def binderArity? (d : Diagram)
    (binder : Fin d.regionCount) : Option Nat :=
  match d.regions binder with
  | .bubble _ arity => some arity
  | _ => none

def RequiresPort (d : Diagram)
    (node : Fin d.nodeCount) (port : CPort) : Prop :=
  match d.nodes node with
  | .atom _ binder =>
      match d.regions binder with
      | .bubble _ arity => exists i : Fin arity, port = .arg i
      | _ => False
  | .identity _ arity => exists i : Fin arity, port = .arg i
instance (d : Diagram) (node : Fin d.nodeCount) (port : CPort) :
    Decidable (d.RequiresPort node port) := by
  unfold RequiresPort
  split
  · split <;> infer_instance
  · infer_instance

def EndpointOccurs (d : Diagram) (wire : Fin d.wireCount)
    (endpoint : CEndpoint d.nodeCount) : Prop :=
  endpoint ∈ (d.wires wire).endpoints

instance (d : Diagram) (wire : Fin d.wireCount)
    (endpoint : CEndpoint d.nodeCount) :
    Decidable (d.EndpointOccurs wire endpoint) := by
  unfold EndpointOccurs
  infer_instance

theorem requiresPort_atom_bubble_iff (d : Diagram)
    (node : Fin d.nodeCount) (port : CPort)
    (region binder parent : Fin d.regionCount) (arity : Nat)
    (hnode : d.nodes node = .atom region binder)
    (hbinder : d.regions binder = .bubble parent arity) :
    d.RequiresPort node port <->
      exists i : Fin arity, port = .arg i := by
  simp only [RequiresPort, hnode, hbinder]

theorem requiresPort_identity_iff (d : Diagram)
    (node : Fin d.nodeCount) (port : CPort)
    (region : Fin d.regionCount) (arity : Nat)
    (hnode : d.nodes node = .identity region arity) :
    d.RequiresPort node port <->
      exists i : Fin arity, port = .arg i := by
  simp only [RequiresPort, hnode]

end Diagram

end VisualProof.Concrete
