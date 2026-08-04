import VisualProof.Lambda.Syntax

namespace VisualProof.Diagram

inductive CRegion (regions : Nat)
  | sheet
  | cut (parent : Fin regions)
  | bubble (parent : Fin regions) (arity : Nat)
  deriving DecidableEq

inductive CPort
  | output
  | free (index : Nat)
  | arg (index : Nat)
  deriving DecidableEq

structure CEndpoint (nodes : Nat) where
  node : Fin nodes
  port : CPort
  deriving DecidableEq

inductive CNode (regions : Nat)
  | term (region : Fin regions) (freePorts : Nat)
      (term : Lambda.Term 0 (Fin freePorts))
  | atom (region binder : Fin regions)
  | named (region : Fin regions) (definition arity : Nat)

structure CWire (regions nodes : Nat) where
  scope : Fin regions
  endpoints : List (CEndpoint nodes)

structure ConcreteDiagram where
  regionCount : Nat
  nodeCount : Nat
  wireCount : Nat
  root : Fin regionCount
  regions : Fin regionCount -> CRegion regionCount
  nodes : Fin nodeCount -> CNode regionCount
  wires : Fin wireCount -> CWire regionCount nodeCount

structure OpenConcreteDiagram where
  diagram : ConcreteDiagram
  boundary : List (Fin diagram.wireCount)

namespace CRegion

def parent? : CRegion regions -> Option (Fin regions)
  | .sheet => none
  | .cut parent => some parent
  | .bubble parent _ => some parent

end CRegion

namespace CNode

def region : CNode regions -> Fin regions
  | .term region _ _ => region
  | .atom region _ => region
  | .named region _ _ => region

end CNode

namespace ConcreteDiagram

def climb (d : ConcreteDiagram) :
    Nat -> Fin d.regionCount -> Option (Fin d.regionCount)
  | 0, region => some region
  | steps + 1, region =>
      match (d.regions region).parent? with
      | none => none
      | some parent => d.climb steps parent

@[simp] theorem climb_zero (d : ConcreteDiagram)
    (region : Fin d.regionCount) :
    d.climb 0 region = some region := rfl

def Encloses (d : ConcreteDiagram)
    (ancestor descendant : Fin d.regionCount) : Prop :=
  exists steps : Fin (d.regionCount + 1),
    d.climb steps descendant = some ancestor

namespace Encloses

theorem refl (d : ConcreteDiagram) (region : Fin d.regionCount) :
    d.Encloses region region := by
  exact ⟨0, d.climb_zero region⟩

end Encloses

instance (d : ConcreteDiagram)
    (ancestor descendant : Fin d.regionCount) :
    Decidable (d.Encloses ancestor descendant) := by
  unfold Encloses
  infer_instance

def ReachesRoot (d : ConcreteDiagram)
    (region : Fin d.regionCount) : Prop :=
  d.Encloses d.root region

instance (d : ConcreteDiagram) (region : Fin d.regionCount) :
    Decidable (d.ReachesRoot region) := by
  unfold ReachesRoot
  infer_instance

def binderArity? (d : ConcreteDiagram)
    (binder : Fin d.regionCount) : Option Nat :=
  match d.regions binder with
  | .bubble _ arity => some arity
  | _ => none

def RequiresPort (d : ConcreteDiagram)
    (node : Fin d.nodeCount) (port : CPort) : Prop :=
  match d.nodes node with
  | .term _ freePorts _ =>
      port = .output \/ exists i : Fin freePorts, port = .free i
  | .atom _ binder =>
      match d.regions binder with
      | .bubble _ arity => exists i : Fin arity, port = .arg i
      | _ => False
  | .named _ _ arity => exists i : Fin arity, port = .arg i

instance (d : ConcreteDiagram) (node : Fin d.nodeCount) (port : CPort) :
    Decidable (d.RequiresPort node port) := by
  unfold RequiresPort
  split
  · infer_instance
  · split <;> infer_instance
  · infer_instance

def EndpointOccurs (d : ConcreteDiagram) (wire : Fin d.wireCount)
    (endpoint : CEndpoint d.nodeCount) : Prop :=
  endpoint ∈ (d.wires wire).endpoints

instance (d : ConcreteDiagram) (wire : Fin d.wireCount)
    (endpoint : CEndpoint d.nodeCount) :
    Decidable (d.EndpointOccurs wire endpoint) := by
  unfold EndpointOccurs
  infer_instance

theorem requiresPort_term_iff (d : ConcreteDiagram)
    (node : Fin d.nodeCount) (port : CPort)
    (region : Fin d.regionCount) (freePorts : Nat)
    (term : Lambda.Term 0 (Fin freePorts))
    (hnode : d.nodes node = .term region freePorts term) :
    d.RequiresPort node port <->
      port = .output \/ exists i : Fin freePorts, port = .free i := by
  simp only [RequiresPort, hnode]

theorem requiresPort_atom_bubble_iff (d : ConcreteDiagram)
    (node : Fin d.nodeCount) (port : CPort)
    (region binder parent : Fin d.regionCount) (arity : Nat)
    (hnode : d.nodes node = .atom region binder)
    (hbinder : d.regions binder = .bubble parent arity) :
    d.RequiresPort node port <->
      exists i : Fin arity, port = .arg i := by
  simp only [RequiresPort, hnode, hbinder]

theorem requiresPort_named_iff (d : ConcreteDiagram)
    (node : Fin d.nodeCount) (port : CPort)
    (region : Fin d.regionCount) (definition arity : Nat)
    (hnode : d.nodes node = .named region definition arity) :
    d.RequiresPort node port <->
      exists i : Fin arity, port = .arg i := by
  simp only [RequiresPort, hnode]

end ConcreteDiagram

end VisualProof.Diagram
