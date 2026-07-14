import VisualProof.Diagram.Concrete.Isomorphism
import VisualProof.Diagram.Concrete.Open

namespace VisualProof.Diagram

/--
An isomorphism of open concrete diagrams preserves the total concrete graph and
the ordered boundary list. In particular, order and repeated positions are part
of the interface, while endpoint order remains nonsemantic through `ConcreteIso`.
-/
structure OpenConcreteIso
    (source target : OpenConcreteDiagram) where
  diagram : ConcreteIso source.diagram target.diagram
  boundary : source.boundary.map diagram.wires = target.boundary

namespace OpenConcreteIso

def refl (diagram : OpenConcreteDiagram) :
    OpenConcreteIso diagram diagram where
  diagram := ConcreteIso.refl diagram.diagram
  boundary := by
    induction diagram.boundary with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons]
        congr

def symm {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) : OpenConcreteIso target source where
  diagram := iso.diagram.symm
  boundary := by
    rw [← iso.boundary]
    induction source.boundary with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons]
        congr 1
        · exact iso.diagram.wires.left_inv head

def trans {source middle target : OpenConcreteDiagram}
    (first : OpenConcreteIso source middle)
    (second : OpenConcreteIso middle target) :
    OpenConcreteIso source target where
  diagram := first.diagram.trans second.diagram
  boundary := by
    rw [← second.boundary, ← first.boundary, List.map_map]
    rfl

/-- Ordered-interface isomorphism forces the two boundary arities to agree. -/
theorem boundary_length_eq {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) :
    source.boundary.length = target.boundary.length := by
  simpa using congrArg List.length iso.boundary

/-- The wire isomorphism carries precisely the exposed boundary-wire fiber. -/
theorem mem_exposedWires_iff {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (wire : Fin source.diagram.wireCount) :
    iso.diagram.wires wire ∈ target.exposedWires ↔
      wire ∈ source.exposedWires := by
  rw [OpenConcreteDiagram.mem_exposedWires,
    OpenConcreteDiagram.mem_exposedWires]
  constructor
  · intro htarget
    rw [← iso.boundary] at htarget
    obtain ⟨sourceWire, hsource, heq⟩ := List.mem_map.mp htarget
    have : sourceWire = wire := by
      apply iso.diagram.wires.injective
      exact heq
    simpa [this] using hsource
  · intro hsource
    rw [← iso.boundary]
    exact List.mem_map_of_mem hsource

/-- Dense equivalence between exposed wire classes. -/
def exposedWiresEquiv {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) :
    FiniteEquiv (Fin source.exposedWires.length)
      (Fin target.exposedWires.length) :=
  FiniteEquiv.restrictLists iso.diagram.wires
    source.exposedWires target.exposedWires
    source.exposedWires_nodup target.exposedWires_nodup
    (iso.mem_exposedWires_iff)

theorem exposedWiresEquiv_spec {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (index : Fin source.exposedWires.length) :
    target.exposedWires.get (iso.exposedWiresEquiv index) =
      iso.diagram.wires (source.exposedWires.get index) :=
  FiniteEquiv.restrictLists_spec iso.diagram.wires _ _ _ _
    iso.mem_exposedWires_iff index

/-- The wire isomorphism carries precisely the hidden root-wire fiber. -/
theorem mem_hiddenWires_iff {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (wire : Fin source.diagram.wireCount) :
    iso.diagram.wires wire ∈ target.hiddenWires ↔
      wire ∈ source.hiddenWires := by
  rw [OpenConcreteDiagram.mem_hiddenWires,
    OpenConcreteDiagram.mem_hiddenWires]
  have hscope :
      (target.diagram.wires (iso.diagram.wires wire)).scope =
          target.diagram.root ↔
        (source.diagram.wires wire).scope = source.diagram.root := by
    constructor
    · intro htarget
      apply iso.diagram.regions.injective
      calc
        iso.diagram.regions (source.diagram.wires wire).scope =
            (target.diagram.wires (iso.diagram.wires wire)).scope :=
          iso.diagram.wire_scope_eq wire
        _ = target.diagram.root := htarget
        _ = iso.diagram.regions source.diagram.root := iso.diagram.root_eq.symm
    · intro hsource
      calc
        (target.diagram.wires (iso.diagram.wires wire)).scope =
            iso.diagram.regions (source.diagram.wires wire).scope :=
          (iso.diagram.wire_scope_eq wire).symm
        _ = iso.diagram.regions source.diagram.root := by rw [hsource]
        _ = target.diagram.root := iso.diagram.root_eq
  rw [hscope, not_congr (iso.mem_exposedWires_iff wire)]

/-- Dense equivalence between hidden root-local wires. -/
def hiddenWiresEquiv {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) :
    FiniteEquiv (Fin source.hiddenWires.length)
      (Fin target.hiddenWires.length) :=
  FiniteEquiv.restrictLists iso.diagram.wires
    source.hiddenWires target.hiddenWires
    source.hiddenWires_nodup target.hiddenWires_nodup
    (iso.mem_hiddenWires_iff)

theorem hiddenWiresEquiv_spec {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (index : Fin source.hiddenWires.length) :
    target.hiddenWires.get (iso.hiddenWiresEquiv index) =
      iso.diagram.wires (source.hiddenWires.get index) :=
  FiniteEquiv.restrictLists_spec iso.diagram.wires _ _ _ _
    iso.mem_hiddenWires_iff index

/-- Ordered boundary lookup commutes with the underlying wire isomorphism. -/
theorem boundary_get_transport {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (position : Fin source.boundary.length) :
    target.boundary.get (Fin.cast iso.boundary_length_eq position) =
      iso.diagram.wires (source.boundary.get position) := by
  have htarget : position.val < target.boundary.length := by
    simpa [iso.boundary_length_eq] using position.isLt
  have hpoint := congrArg (fun values => values[position.val]?) iso.boundary
  simp [List.getElem?_eq_getElem htarget] at hpoint
  exact hpoint.symm

/-- Ordered boundary positions retain their exposed class under isomorphism. -/
theorem boundaryClass_commute {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (position : Fin source.boundary.length) :
    iso.exposedWiresEquiv (source.boundaryClass position) =
      target.boundaryClass (Fin.cast iso.boundary_length_eq position) := by
  exact OpenConcreteDiagram.boundaryClass_complete target
    (Fin.cast iso.boundary_length_eq position)
    (iso.exposedWiresEquiv (source.boundaryClass position)) (by
      rw [iso.exposedWiresEquiv_spec,
        OpenConcreteDiagram.boundaryClass_sound,
        iso.boundary_get_transport])

/-- Open well-formedness is invariant under ordered-interface isomorphism. -/
def wellFormed_transport {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) {signature : List Nat}
    (h : source.WellFormed signature) : target.WellFormed signature where
  diagram_well_formed := iso.diagram.wellFormed_transport
    h.diagram_well_formed
  boundary_is_root_scoped := by
    intro targetWire htarget
    rw [← iso.boundary] at htarget
    obtain ⟨sourceWire, hsource, hwire⟩ := List.mem_map.mp htarget
    calc
      (target.diagram.wires targetWire).scope =
          (target.diagram.wires (iso.diagram.wires sourceWire)).scope := by
            rw [hwire]
      _ = iso.diagram.regions (source.diagram.wires sourceWire).scope :=
        (iso.diagram.wire_scope_eq sourceWire).symm
      _ = iso.diagram.regions source.diagram.root := by
        rw [h.boundary_is_root_scoped sourceWire hsource]
      _ = target.diagram.root := iso.diagram.root_eq

/-- Transport a checked open diagram along an isomorphism from its value. -/
def checked_transport {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target) {signature : List Nat}
    (checked : CheckedOpenDiagram signature) (hsource : checked.val = source) :
    CheckedOpenDiagram signature := by
  subst source
  exact ⟨target, iso.wellFormed_transport checked.property⟩

end OpenConcreteIso

end VisualProof.Diagram
