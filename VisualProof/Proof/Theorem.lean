import VisualProof.Proof.Schema
import VisualProof.Proof.Replay

namespace VisualProof.Proof

open VisualProof.Concrete

open VisualProof
open Diagram
open Rule

/-- The replay state determined by a checked open theorem side. -/
def theoremSideState (side : Concrete.CheckedOpen) : OperationState where
  diagram := ⟨side.val.diagram, side.property.diagram_well_formed⟩
  boundary := side.val.boundary
  boundary_root_scoped := side.property.boundary_is_root_scoped

@[simp] theorem theoremSideState_asCheckedOpen
    (side : Concrete.CheckedOpen) :
    (theoremSideState side).asCheckedOpen = side := by
  rfl

@[simp] theorem theoremSideState_denote
    (side : Concrete.CheckedOpen)
    (model : Model)
    (args : Fin side.val.boundary.length → model.Carrier) :
    (theoremSideState side).denote model args =
      side.denote model args := by
  rfl

/-- A theorem certified by dual replay of primitive programs. The forward
program starts at the stated left side, the backward program starts at the
stated right side, and their boundary-pinned endpoints meet up to ordered
concrete isomorphism. -/
structure CheckedTheorem where
  schema : TheoremSchema
  forwardFinish : OperationState
  backwardFinish : OperationState
  forwardProgram : Program .forward (theoremSideState schema.left)
  backwardProgram : Program .backward (theoremSideState schema.right)
  forwardReplay : replay .forward (theoremSideState schema.left)
      forwardProgram = .ok forwardFinish
  backwardReplay : replay .backward (theoremSideState schema.right)
      backwardProgram = .ok backwardFinish
  meet : Concrete.OpenIso forwardFinish.asCheckedOpen.val
    backwardFinish.asCheckedOpen.val

/-- The semantic theorem certified by primitive replay and ordered endpoint
isomorphism. -/
theorem checkedTheorem_sound
    (checked : CheckedTheorem) : checked.schema.Valid model := by
  intro args leftDenotes
  have forwardSound := replay_sound (model := model) checked.forwardProgram
    checked.forwardReplay
  have backwardSound := replay_sound (model := model) checked.backwardProgram
    checked.backwardReplay
  have forwardDenotes : checked.forwardFinish.denote model
      (transportArgs forwardSound.boundaryLength args) :=
    forwardSound.sound args leftDenotes
  have meetDenotes : checked.backwardFinish.denote model
      (transportArgs checked.meet.boundary_length_eq.symm
        (transportArgs forwardSound.boundaryLength args)) := by
    exact (checked.meet.denote_iff
      checked.forwardFinish.asCheckedOpen.property
      checked.backwardFinish.asCheckedOpen.property model
      (transportArgs forwardSound.boundaryLength args)).mp forwardDenotes
  let rightArgs : Fin checked.schema.right.val.boundary.length →
      model.Carrier :=
    transportArgs checked.schema.sameBoundaryArity.symm args
  have hbackwardArgs :
      transportArgs backwardSound.boundaryLength rightArgs =
        transportArgs checked.meet.boundary_length_eq.symm
          (transportArgs forwardSound.boundaryLength args) := by
    funext index
    apply congrArg args
    apply Fin.ext
    rfl
  have backwardInput : checked.backwardFinish.denote model
      (transportArgs backwardSound.boundaryLength rightArgs) := by
    exact hbackwardArgs.symm ▸ meetDenotes
  exact backwardSound.sound rightArgs backwardInput

end VisualProof.Proof
