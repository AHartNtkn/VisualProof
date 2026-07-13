import VisualProof.Diagram.Concrete.Elaboration.Traversal

namespace VisualProof.Diagram

open VisualProof.Data.Finite
open ConcreteElaboration

/-- An open concrete diagram paired with its single well-formedness certificate. -/
abbrev CheckedOpenDiagram (signature : List Nat) :=
  { d : OpenConcreteDiagram // d.WellFormed signature }

namespace OpenConcreteDiagram

private theorem eraseDups_nodup [BEq alpha] [LawfulBEq alpha]
    (values : List alpha) : values.eraseDups.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (tail.filter fun value => !value == head)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

/--
The external wire classes in stable first-occurrence order. Boundary positions
remain in `boundary`; repeated positions share one class here.
-/
def exposedWires (d : OpenConcreteDiagram) :
    List (Fin d.diagram.wireCount) :=
  d.boundary.eraseDups

@[simp] theorem mem_exposedWires (d : OpenConcreteDiagram)
    (wire : Fin d.diagram.wireCount) :
    wire ∈ d.exposedWires ↔ wire ∈ d.boundary := by
  simp [exposedWires]

theorem exposedWires_nodup (d : OpenConcreteDiagram) :
    d.exposedWires.Nodup :=
  eraseDups_nodup d.boundary

@[simp] theorem boundary_get_mem_exposedWires (d : OpenConcreteDiagram)
    (position : Fin d.boundary.length) :
    d.boundary.get position ∈ d.exposedWires := by
  rw [mem_exposedWires]
  exact d.boundary.get_mem position

/--
The external class of an ordered boundary position. The result is computed only
from the raw boundary list; the membership proof passed to `Option.get` cannot
affect it.
-/
def boundaryClass (d : OpenConcreteDiagram)
    (position : Fin d.boundary.length) : Fin d.exposedWires.length :=
  (indexOf? d.exposedWires (d.boundary.get position)).get (by
    rw [indexOf?_isSome_iff]
    exact boundary_get_mem_exposedWires d position)

theorem boundaryClass_lookup (d : OpenConcreteDiagram)
    (position : Fin d.boundary.length) :
    indexOf? d.exposedWires (d.boundary.get position) =
      some (d.boundaryClass position) := by
  unfold boundaryClass
  let hsome :
      (indexOf? d.exposedWires (d.boundary.get position)).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact boundary_get_mem_exposedWires d position
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    indexOf? d.exposedWires (d.boundary.get position) = some found := hfound
    _ = some ((indexOf? d.exposedWires
        (d.boundary.get position)).get hsome) :=
      congrArg some (Option.get_of_eq_some hsome hfound).symm
    _ = some (d.boundaryClass position) := by rfl

/-- Looking up a computed boundary class returns its original boundary wire. -/
theorem boundaryClass_sound (d : OpenConcreteDiagram)
    (position : Fin d.boundary.length) :
    d.exposedWires.get (d.boundaryClass position) =
      d.boundary.get position := by
  exact indexOf?_sound (boundaryClass_lookup d position)

/-- The computed class is the unique exposed class containing that wire. -/
theorem boundaryClass_complete (d : OpenConcreteDiagram)
    (position : Fin d.boundary.length)
    (external : Fin d.exposedWires.length)
    (hwire : d.exposedWires.get external = d.boundary.get position) :
    external = d.boundaryClass position := by
  exact indexOf?_unique_of_nodup d.exposedWires_nodup
    (boundaryClass_lookup d position) hwire

theorem boundaryClass_eq_iff (d : OpenConcreteDiagram)
    (left right : Fin d.boundary.length) :
    d.boundaryClass left = d.boundaryClass right ↔
      d.boundary.get left = d.boundary.get right := by
  constructor
  · intro hclasses
    rw [← boundaryClass_sound d left, ← boundaryClass_sound d right,
      hclasses]
  · intro hwires
    apply Fin.ext
    have hleft := boundaryClass_complete d left (d.boundaryClass right) (by
      rw [boundaryClass_sound d right, hwires])
    exact congrArg Fin.val hleft.symm

theorem boundaryClass_surjective (d : OpenConcreteDiagram) :
    Function.Surjective d.boundaryClass := by
  intro external
  have hexposed : d.exposedWires.get external ∈ d.exposedWires :=
    d.exposedWires.get_mem external
  have hboundary : d.exposedWires.get external ∈ d.boundary :=
    (mem_exposedWires d _).mp hexposed
  obtain ⟨position, hposition⟩ := List.mem_iff_get.mp hboundary
  exact ⟨position, (boundaryClass_complete d position external
    hposition.symm).symm⟩

/-- Root-local wires that are not exposed by any boundary position. -/
def hiddenWires (d : OpenConcreteDiagram) :
    List (Fin d.diagram.wireCount) :=
  (exactScopeWires d.diagram d.diagram.root).filter fun wire =>
    decide (wire ∉ d.exposedWires)

@[simp] theorem mem_hiddenWires (d : OpenConcreteDiagram)
    (wire : Fin d.diagram.wireCount) :
    wire ∈ d.hiddenWires ↔
      (d.diagram.wires wire).scope = d.diagram.root ∧
        wire ∉ d.exposedWires := by
  simp [hiddenWires]

theorem hiddenWires_nodup (d : OpenConcreteDiagram) :
    d.hiddenWires.Nodup :=
  (exactScopeWires_nodup d.diagram d.diagram.root).filter _

theorem exposedWires_hiddenWires_disjoint (d : OpenConcreteDiagram) :
    ∀ exposed, exposed ∈ d.exposedWires →
      ∀ hidden, hidden ∈ d.hiddenWires → exposed ≠ hidden := by
  intro exposed hexposed hidden hhidden heq
  subst hidden
  exact (mem_hiddenWires d exposed).mp hhidden |>.2 hexposed

/-- The stable root-wire partition: external classes first, then hidden locals. -/
def rootWires (d : OpenConcreteDiagram) :
    List (Fin d.diagram.wireCount) :=
  d.exposedWires ++ d.hiddenWires

theorem WellFormed.exposed_root_scoped
    {d : OpenConcreteDiagram} (hwf : d.WellFormed signature)
    {wire : Fin d.diagram.wireCount} (hexposed : wire ∈ d.exposedWires) :
    (d.diagram.wires wire).scope = d.diagram.root :=
  hwf.boundary_is_root_scoped wire ((mem_exposedWires d wire).mp hexposed)

@[simp] theorem mem_rootWires_iff
    (d : OpenConcreteDiagram) (hwf : d.WellFormed signature)
    (wire : Fin d.diagram.wireCount) :
    wire ∈ d.rootWires ↔
      (d.diagram.wires wire).scope = d.diagram.root := by
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hexposed | hhidden
    · exact hwf.exposed_root_scoped hexposed
    · exact (mem_hiddenWires d wire).mp hhidden |>.1
  · intro hroot
    by_cases hexposed : wire ∈ d.exposedWires
    · exact List.mem_append_left _ hexposed
    · exact List.mem_append_right _ ((mem_hiddenWires d wire).mpr
        ⟨hroot, hexposed⟩)

theorem rootWires_nodup (d : OpenConcreteDiagram) :
    d.rootWires.Nodup := by
  rw [rootWires, List.nodup_append]
  exact ⟨d.exposedWires_nodup, d.hiddenWires_nodup,
    d.exposedWires_hiddenWires_disjoint⟩

end OpenConcreteDiagram

end VisualProof.Diagram
