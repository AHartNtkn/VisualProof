import VisualProof.Proof.Replay
import VisualProof.Diagram.Concrete.Semantics

namespace VisualProof.Proof

open VisualProof
open Diagram
open Rule

/-- The replay state determined by a checked open theorem side. -/
def theoremSideState (side : CheckedOpenDiagram ) :
    OpenProofState  where
  diagram := ⟨side.val.diagram, side.property.diagram_well_formed⟩
  boundary := side.val.boundary
  boundary_root_scoped := side.property.boundary_is_root_scoped

@[simp] theorem theoremSideState_asCheckedOpen
    (side : CheckedOpenDiagram ) :
    (theoremSideState side).asCheckedOpen = side := by
  rfl

@[simp] theorem theoremSideState_denote
    (side : CheckedOpenDiagram )
    (model : Model)
    (args : Fin side.val.boundary.length → model.Carrier) :
    (theoremSideState side).denote model  args =
      side.denote model  args := by
  rfl

/-- A theorem checked by dual replay.  The forward half starts at the stated
left side, the backward half starts at the stated right side, and their
boundary-pinned endpoints meet up to ordered concrete isomorphism. -/
structure CheckedTheorem (context : ProofContext ) where
  schema : TheoremSchema
  forwardFinish : OpenProofState
  backwardFinish : OpenProofState
  forwardProgram : Program context .forward (theoremSideState schema.left)
  backwardProgram : Program context .backward (theoremSideState schema.right)
  forwardReplay : replay context .forward (theoremSideState schema.left)
      forwardProgram = .ok forwardFinish
  backwardReplay : replay context .backward (theoremSideState schema.right)
      backwardProgram = .ok backwardFinish
  meet : OpenConcreteIso forwardFinish.asCheckedOpen.val
    backwardFinish.asCheckedOpen.val

/-- The semantic theorem certified by dual replay and the ordered endpoint
isomorphism.  Every replay step reaches this proof through
`Rule.applyStep_sound`; there is no theorem-checker soundness parameter. -/
theorem checkedTheorem_sound
    (checked : CheckedTheorem context)
    (valid : context.Valid model) :
    checked.schema.Valid model := by
  intro args leftDenotes
  have forwardSound := replay_sound checked.forwardProgram
    checked.forwardReplay valid
  have backwardSound := replay_sound checked.backwardProgram
    checked.backwardReplay valid
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

/-- Register a checked theorem at the end of its validating context.  Later
theorems may cite it, while its own proof could cite only the earlier prefix. -/
def CheckedTheorem.register {context : ProofContext } (checked : CheckedTheorem context) :
    ProofContext  where
  theorems := context.theorems ++ [checked.schema]

theorem CheckedTheorem.register_valid
    {context : ProofContext }
    (checked : CheckedTheorem context)
    (valid : context.Valid model) : checked.register.Valid model := by
  refine ⟨?_⟩
  change ∀ index : Fin (context.theorems ++ [checked.schema]).length,
    ((context.theorems ++ [checked.schema]).get index).Valid
      model
  intro index
  by_cases hprior : index.val < context.theorems.length
  · let prior : Fin context.theorems.length := ⟨index.val, hprior⟩
    have hget : (context.theorems ++ [checked.schema]).get index =
        context.theorems.get prior := by
      simp [List.get_eq_getElem, List.getElem_append_left hprior, prior]
    rw [hget]
    exact valid.theorems prior
  · have hlast : index.val = context.theorems.length := by
      have hin := index.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at hin
      omega
    have hget : (context.theorems ++ [checked.schema]).get index =
        checked.schema := by
      simp [List.get_eq_getElem, hlast]
    rw [hget]
    exact checkedTheorem_sound checked valid

/-- A citation is semantically authorized precisely by lookup in a valid
ordered context. -/
theorem citation_sound
    {context : ProofContext }
    (valid : context.Valid model)
    (index : Fin context.theorems.length) :
    (context.theorems.get index).Valid
      model :=
  valid.theorems index

end VisualProof.Proof
