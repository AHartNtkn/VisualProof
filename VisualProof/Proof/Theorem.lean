import VisualProof.Proof.Schema
import VisualProof.Proof.Replay
import VisualProof.Refinement.Step
import VisualProof.Rule.Soundness

namespace VisualProof.Proof

open VisualProof.Concrete

/-- The arity-indexed execution state determined by a checked theorem side. -/
def theoremSideState (side : Concrete.CheckedOpen) :
    State side.val.boundary.length where
  checked := side
  boundary_length := rfl

@[simp] theorem theoremSideState_checked (side : Concrete.CheckedOpen) :
    (theoremSideState side).checked = side := by
  rfl

/-- A theorem-shaped certificate consisting of dual programs replayed by the
sole concrete executor, with endpoints meeting up to ordered open isomorphism.
Its semantic interpretation is established in the proof layer by composing
execution refinement with aggregate rule soundness. -/
structure CheckedTheorem where
  schema : TheoremSchema
  forwardFinish : State schema.left.val.boundary.length
  backwardFinish : State schema.right.val.boundary.length
  forwardProgram : Program .forward (theoremSideState schema.left)
  backwardProgram : Program .backward (theoremSideState schema.right)
  forwardReplay : replay .forward (theoremSideState schema.left)
      forwardProgram = .ok forwardFinish
  backwardReplay : replay .backward (theoremSideState schema.right)
      backwardProgram = .ok backwardFinish
  meet : Concrete.OpenIso forwardFinish.checked.val
    backwardFinish.checked.val

end VisualProof.Proof
