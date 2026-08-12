import VisualProof.Concrete.Elaboration
import VisualProof.Concrete.Step.Core

namespace VisualProof.Concrete

private structure BoundaryValidation
    (diagram : Concrete.Diagram)
    (boundary : List (Fin diagram.wireCount)) : Type where
  root_scoped : ∀ wire, wire ∈ boundary →
    (diagram.wires wire).scope = diagram.root

private def checkBoundaryRoot
    (diagram : Concrete.Diagram) :
    (boundary : List (Fin diagram.wireCount)) →
    (position : Nat) →
    Except Concrete.Error
      (BoundaryValidation diagram boundary)
  | [], _ => .ok ⟨by simp⟩
  | wire :: tail, position =>
      if rootScoped : (diagram.wires wire).scope = diagram.root then
        match checkBoundaryRoot diagram tail (position + 1) with
        | .error error => .error error
        | .ok tailValidation => .ok ⟨by
            intro candidate member
            rcases List.mem_cons.mp member with rfl | member
            · exact rootScoped
            · exact tailValidation.root_scoped candidate member⟩
      else
        .error (.invalidBoundaryPosition position)

private theorem checkBoundaryRoot_complete
    {diagram : Concrete.Diagram}
    {boundary : List (Fin diagram.wireCount)}
    (rootScoped : ∀ wire, wire ∈ boundary →
      (diagram.wires wire).scope = diagram.root)
    (position : Nat) :
    checkBoundaryRoot diagram boundary position =
      .ok (⟨rootScoped⟩ : BoundaryValidation diagram boundary) := by
  induction boundary generalizing position with
  | nil => rfl
  | cons wire tail ih =>
      have headRootScoped := rootScoped wire (by simp)
      have tailRootScoped : ∀ candidate, candidate ∈ tail →
          (diagram.wires candidate).scope = diagram.root := by
        intro candidate member
        exact rootScoped candidate (by simp [member])
      simp only [checkBoundaryRoot, dif_pos headRootScoped]
      rw [ih tailRootScoped (position + 1)]

/-- A successful validation carries the proof for the exact raw input. -/
structure OpenValidation (concrete : Concrete.OpenDiagram) : Type where
  valid : concrete.WellFormed

def OpenValidation.checked
    (validation : Concrete.OpenValidation concrete) :
    Concrete.CheckedOpen :=
  ⟨concrete, validation.valid⟩

/-- Validate a raw open diagram without changing its concrete identity. -/
def checkOpen (concrete : Concrete.OpenDiagram) :
    Except Concrete.Error (Concrete.OpenValidation concrete) :=
  match hdiagram : Concrete.checkWellFormed concrete.diagram with
  | .error error => .error (.invalidOpenDiagram error)
  | .ok checked =>
      match checkBoundaryRoot concrete.diagram concrete.boundary 0 with
      | .error error => .error error
      | .ok boundaryValidation => .ok ⟨{
          diagram_well_formed := by
            rw [← Concrete.checkWellFormed_preserves_input hdiagram]
            exact checked.property
          boundary_is_root_scoped := boundaryValidation.root_scoped
        }⟩

theorem checkOpen_complete
    (valid : concrete.WellFormed) :
    Concrete.checkOpen concrete = .ok ⟨valid⟩ := by
  unfold Concrete.checkOpen
  split
  · rename_i error hcheck
    rw [Concrete.checkWellFormed_complete valid.diagram_well_formed] at hcheck
    contradiction
  · rename_i checked hcheck
    rw [checkBoundaryRoot_complete valid.boundary_is_root_scoped 0]

/-- The sole raw concrete-to-recursive translation: validate, then elaborate. -/
noncomputable def translate (concrete : Concrete.OpenDiagram) :
    Except Concrete.Error
      (VisualProof.Diagram.OpenDiagram concrete.boundary.length) :=
  match Concrete.checkOpen concrete with
  | .error error => .error error
  | .ok validation => .ok validation.checked.elaborate

theorem translate_checked (checked : Concrete.CheckedOpen) :
    Concrete.translate checked.val = .ok checked.elaborate := by
  unfold Concrete.translate
  rw [Concrete.checkOpen_complete checked.property]
  congr

end VisualProof.Concrete
