import VisualProof.Proof.Replay
import VisualProof.Diagram.Concrete.Semantics

namespace VisualProof.Proof

open VisualProof
open Diagram
open Rule

/-- The replay state determined by a checked open theorem side. -/
def theoremSideState (side : CheckedOpenDiagram signature) :
    OpenProofState signature where
  diagram := ⟨side.val.diagram, side.property.diagram_well_formed⟩
  boundary := side.val.boundary
  boundary_root_scoped := side.property.boundary_is_root_scoped

@[simp] theorem theoremSideState_asCheckedOpen
    (side : CheckedOpenDiagram signature) :
    (theoremSideState side).asCheckedOpen = side := by
  rfl

@[simp] theorem theoremSideState_denote
    (side : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin side.val.boundary.length → model.Carrier) :
    (theoremSideState side).denote model named args =
      side.denote model named args := by
  rfl

/-- A theorem checked by dual replay.  The forward half starts at the stated
left side, the backward half starts at the stated right side, and their
boundary-pinned endpoints meet up to ordered concrete isomorphism. -/
structure CheckedTheorem (context : ProofContext signature) where
  schema : TheoremSchema signature
  forwardFinish : OpenProofState signature
  backwardFinish : OpenProofState signature
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
    (valid : context.Valid) :
    checked.schema.Valid
      (Theory.interpretDefinitions context.definitions) := by
  intro args leftDenotes
  let named := Theory.interpretDefinitions context.definitions
  have forwardSound := replay_sound checked.forwardProgram
    checked.forwardReplay valid
  have backwardSound := replay_sound checked.backwardProgram
    checked.backwardReplay valid
  have forwardDenotes : checked.forwardFinish.denote Lambda.canonicalModel named
      (transportArgs forwardSound.boundaryLength args) :=
    forwardSound.sound args leftDenotes
  have meetDenotes : checked.backwardFinish.denote Lambda.canonicalModel named
      (transportArgs checked.meet.boundary_length_eq.symm
        (transportArgs forwardSound.boundaryLength args)) := by
    exact (checked.meet.denote_iff
      checked.forwardFinish.asCheckedOpen.property
      checked.backwardFinish.asCheckedOpen.property Lambda.canonicalModel named
      (transportArgs forwardSound.boundaryLength args)).mp forwardDenotes
  let rightArgs : Fin checked.schema.right.val.boundary.length →
      Lambda.Individual :=
    transportArgs checked.schema.sameBoundaryArity.symm args
  have hbackwardArgs :
      transportArgs backwardSound.boundaryLength rightArgs =
        transportArgs checked.meet.boundary_length_eq.symm
          (transportArgs forwardSound.boundaryLength args) := by
    funext index
    apply congrArg args
    apply Fin.ext
    rfl
  have backwardInput : checked.backwardFinish.denote Lambda.canonicalModel named
      (transportArgs backwardSound.boundaryLength rightArgs) := by
    exact hbackwardArgs.symm ▸ meetDenotes
  exact backwardSound.sound rightArgs backwardInput

/-- Register a checked theorem at the end of its validating context.  Later
theorems may cite it, while its own proof could cite only the earlier prefix. -/
def CheckedTheorem.register {signature : List Nat}
    {context : ProofContext signature} (checked : CheckedTheorem context) :
    ProofContext signature where
  definitions := context.definitions
  theorems := context.theorems ++ [checked.schema]

theorem CheckedTheorem.register_definitions
    {signature : List Nat} {context : ProofContext signature}
    (checked : CheckedTheorem context) :
    checked.register.definitions = context.definitions := rfl

theorem CheckedTheorem.register_valid
    {signature : List Nat} {context : ProofContext signature}
    (checked : CheckedTheorem context)
    (valid : context.Valid) : checked.register.Valid := by
  refine ⟨?_⟩
  change ∀ index : Fin (context.theorems ++ [checked.schema]).length,
    ((context.theorems ++ [checked.schema]).get index).Valid
      (Theory.interpretDefinitions context.definitions)
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
    simpa only [CheckedTheorem.register_definitions] using
      checkedTheorem_sound checked valid

/-- A citation is semantically authorized precisely by lookup in a valid
ordered context. -/
theorem citation_sound
    {signature : List Nat} {context : ProofContext signature}
    (valid : context.Valid)
    (index : Fin context.theorems.length) :
    (context.theorems.get index).Valid
      (Theory.interpretDefinitions context.definitions) :=
  valid.theorems index

end VisualProof.Proof
