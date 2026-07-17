import VisualProof.Diagram.BetaEtaIsomorphism
import VisualProof.Diagram.Concrete.OpenIsomorphism
import VisualProof.Lambda.Certificate

namespace VisualProof.Diagram

open VisualProof

namespace CNode

/-- Proof-relevant node correspondence. A term pair is accepted only through
its stored, kernel-checked certificate between positional closures. -/
inductive CertifiedCorresponds
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions)) :
    CNode sourceRegions → CNode targetRegions → Type
  | term (sourceRegion : Fin sourceRegions)
      (targetRegion : Fin targetRegions) (ports : Nat)
      (sourceTerm targetTerm : Lambda.Term 0 (Fin ports))
      (region_eq : regions sourceRegion = targetRegion)
      (certificate : Lambda.CheckedCertificate
        sourceTerm.closeOverPorts targetTerm.closeOverPorts) :
      CertifiedCorresponds regions
        (.term sourceRegion ports sourceTerm)
        (.term targetRegion ports targetTerm)
  | atom (sourceRegion sourceBinder : Fin sourceRegions)
      (targetRegion targetBinder : Fin targetRegions)
      (region_eq : regions sourceRegion = targetRegion)
      (binder_eq : regions sourceBinder = targetBinder) :
      CertifiedCorresponds regions
        (.atom sourceRegion sourceBinder)
        (.atom targetRegion targetBinder)
  | named (sourceRegion : Fin sourceRegions)
      (targetRegion : Fin targetRegions) (definition arity : Nat)
      (region_eq : regions sourceRegion = targetRegion) :
      CertifiedCorresponds regions
        (.named sourceRegion definition arity)
        (.named targetRegion definition arity)

theorem CertifiedCorresponds.region_eq
    {source : CNode sourceRegions} {target : CNode targetRegions}
    (corresponds : CertifiedCorresponds regions source target) :
    regions source.region = target.region := by
  cases corresponds <;> assumption

def CertifiedCorresponds.ofRenameEq
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions))
    {source : CNode sourceRegions} {target : CNode targetRegions}
    (equality : source.rename regions = target) :
    CertifiedCorresponds regions source target := by
  subst target
  cases source with
  | term region ports term =>
      exact .term region (regions region) ports term term rfl
        (Lambda.CheckedCertificate.refl term.closeOverPorts)
  | atom region binder =>
      exact .atom region binder (regions region) (regions binder) rfl rfl
  | named region definition arity =>
      exact .named region (regions region) definition arity rfl

end CNode

/-- Concrete occurrence equivalence preserves the complete graph and ordered
ports, but replaces exact term equality with checked positional certificates. -/
structure ConcreteOccurrenceEquiv (source target : ConcreteDiagram) where
  regionCount_eq : source.regionCount = target.regionCount
  nodeCount_eq : source.nodeCount = target.nodeCount
  wireCount_eq : source.wireCount = target.wireCount
  regions : FiniteEquiv (Fin source.regionCount) (Fin target.regionCount)
  nodes : FiniteEquiv (Fin source.nodeCount) (Fin target.nodeCount)
  wires : FiniteEquiv (Fin source.wireCount) (Fin target.wireCount)
  root_eq : regions source.root = target.root
  regions_eq : ∀ region,
    (source.regions region).rename regions = target.regions (regions region)
  nodes_correspond : ∀ node,
    CNode.CertifiedCorresponds regions
      (source.nodes node) (target.nodes (nodes node))
  wire_scope_eq : ∀ wire,
    regions (source.wires wire).scope = (target.wires (wires wire)).scope
  wire_endpoints_perm : ∀ wire,
    ((source.wires wire).endpoints.map (CEndpoint.rename nodes)).Perm
      (target.wires (wires wire)).endpoints

namespace ConcreteOccurrenceEquiv

def ofConcreteIso {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) : ConcreteOccurrenceEquiv source target where
  regionCount_eq := iso.regionCount_eq
  nodeCount_eq := iso.nodeCount_eq
  wireCount_eq := iso.wireCount_eq
  regions := iso.regions
  nodes := iso.nodes
  wires := iso.wires
  root_eq := iso.root_eq
  regions_eq := iso.regions_eq
  nodes_correspond := fun node =>
    CNode.CertifiedCorresponds.ofRenameEq iso.regions (iso.nodes_eq node)
  wire_scope_eq := iso.wire_scope_eq
  wire_endpoints_perm := iso.wire_endpoints_perm

theorem node_region_eq {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (node : Fin source.nodeCount) :
    equiv.regions (source.nodes node).region =
      (target.nodes (equiv.nodes node)).region :=
  (equiv.nodes_correspond node).region_eq

theorem endpointOccurs_transport {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    {wire : Fin source.wireCount} {endpoint : CEndpoint source.nodeCount}
    (occurs : source.EndpointOccurs wire endpoint) :
    target.EndpointOccurs (equiv.wires wire) (endpoint.rename equiv.nodes) := by
  exact (equiv.wire_endpoints_perm wire).mem_iff.mp
    (List.mem_map.mpr ⟨endpoint, occurs, rfl⟩)

end ConcreteOccurrenceEquiv

/-- Ordered-open occurrence equivalence. Repeated boundary positions and their
order remain part of the certified interface. -/
structure OpenOccurrenceEquiv
    (source target : OpenConcreteDiagram) where
  diagram : ConcreteOccurrenceEquiv source.diagram target.diagram
  boundary : source.boundary.map diagram.wires = target.boundary

namespace OpenOccurrenceEquiv

def ofOpenConcreteIso {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) : OpenOccurrenceEquiv source target where
  diagram := ConcreteOccurrenceEquiv.ofConcreteIso iso.diagram
  boundary := iso.boundary

theorem boundary_length_eq {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target) :
    source.boundary.length = target.boundary.length := by
  simpa using congrArg List.length equiv.boundary

theorem mem_exposedWires_iff {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (wire : Fin source.diagram.wireCount) :
    equiv.diagram.wires wire ∈ target.exposedWires ↔
      wire ∈ source.exposedWires := by
  rw [OpenConcreteDiagram.mem_exposedWires,
    OpenConcreteDiagram.mem_exposedWires]
  constructor
  · intro htarget
    rw [← equiv.boundary] at htarget
    obtain ⟨sourceWire, hsource, heq⟩ := List.mem_map.mp htarget
    have : sourceWire = wire := equiv.diagram.wires.injective heq
    simpa [this] using hsource
  · intro hsource
    rw [← equiv.boundary]
    exact List.mem_map_of_mem hsource

def exposedWiresEquiv {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target) :
    FiniteEquiv (Fin source.exposedWires.length)
      (Fin target.exposedWires.length) :=
  FiniteEquiv.restrictLists equiv.diagram.wires
    source.exposedWires target.exposedWires
    source.exposedWires_nodup target.exposedWires_nodup
    equiv.mem_exposedWires_iff

theorem exposedWiresEquiv_spec {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (index : Fin source.exposedWires.length) :
    target.exposedWires.get (equiv.exposedWiresEquiv index) =
      equiv.diagram.wires (source.exposedWires.get index) :=
  FiniteEquiv.restrictLists_spec equiv.diagram.wires _ _ _ _
    equiv.mem_exposedWires_iff index

theorem mem_hiddenWires_iff {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (wire : Fin source.diagram.wireCount) :
    equiv.diagram.wires wire ∈ target.hiddenWires ↔
      wire ∈ source.hiddenWires := by
  rw [OpenConcreteDiagram.mem_hiddenWires,
    OpenConcreteDiagram.mem_hiddenWires]
  have hscope :
      (target.diagram.wires (equiv.diagram.wires wire)).scope =
          target.diagram.root ↔
        (source.diagram.wires wire).scope = source.diagram.root := by
    constructor
    · intro htarget
      apply equiv.diagram.regions.injective
      calc
        equiv.diagram.regions (source.diagram.wires wire).scope =
            (target.diagram.wires (equiv.diagram.wires wire)).scope :=
          equiv.diagram.wire_scope_eq wire
        _ = target.diagram.root := htarget
        _ = equiv.diagram.regions source.diagram.root :=
          equiv.diagram.root_eq.symm
    · intro hsource
      calc
        (target.diagram.wires (equiv.diagram.wires wire)).scope =
            equiv.diagram.regions (source.diagram.wires wire).scope :=
          (equiv.diagram.wire_scope_eq wire).symm
        _ = equiv.diagram.regions source.diagram.root := by rw [hsource]
        _ = target.diagram.root := equiv.diagram.root_eq
  rw [hscope, not_congr (equiv.mem_exposedWires_iff wire)]

def hiddenWiresEquiv {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target) :
    FiniteEquiv (Fin source.hiddenWires.length)
      (Fin target.hiddenWires.length) :=
  FiniteEquiv.restrictLists equiv.diagram.wires
    source.hiddenWires target.hiddenWires
    source.hiddenWires_nodup target.hiddenWires_nodup
    equiv.mem_hiddenWires_iff

theorem hiddenWiresEquiv_spec {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (index : Fin source.hiddenWires.length) :
    target.hiddenWires.get (equiv.hiddenWiresEquiv index) =
      equiv.diagram.wires (source.hiddenWires.get index) :=
  FiniteEquiv.restrictLists_spec equiv.diagram.wires _ _ _ _
    equiv.mem_hiddenWires_iff index

theorem boundary_get_transport {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (position : Fin source.boundary.length) :
    target.boundary.get (Fin.cast equiv.boundary_length_eq position) =
      equiv.diagram.wires (source.boundary.get position) := by
  have htarget : position.val < target.boundary.length := by
    simpa [equiv.boundary_length_eq] using position.isLt
  have hpoint := congrArg (fun values => values[position.val]?) equiv.boundary
  simp [List.getElem?_eq_getElem htarget] at hpoint
  exact hpoint.symm

theorem boundaryClass_commute {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (position : Fin source.boundary.length) :
    equiv.exposedWiresEquiv (source.boundaryClass position) =
      target.boundaryClass (Fin.cast equiv.boundary_length_eq position) := by
  exact OpenConcreteDiagram.boundaryClass_complete target
    (Fin.cast equiv.boundary_length_eq position)
    (equiv.exposedWiresEquiv (source.boundaryClass position)) (by
      rw [equiv.exposedWiresEquiv_spec,
        OpenConcreteDiagram.boundaryClass_sound,
        equiv.boundary_get_transport])

end OpenOccurrenceEquiv

end VisualProof.Diagram
