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
