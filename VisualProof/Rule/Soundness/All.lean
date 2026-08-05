import VisualProof.Rule.Soundness.Structural
import VisualProof.Rule.Soundness.HighLevel

namespace VisualProof.Rule

open VisualProof
open Diagram

/-- Every successful branch of the sole checked dispatcher preserves
denotation at every transported ordered boundary.  The proof is exhaustive:
each constructor is discharged by its  rule-family obligation. -/
theorem applyStep_sound
    {context : ProofContext } {orientation : Orientation}
    {input : Diagram.CheckedDiagram } {step : Step context input}
    {receipt : StepReceipt input}
    (happly : applyStep context orientation input step = .ok receipt) :
    SuccessfulReceiptSound context orientation input step receipt := by
  cases step with
  | boundRelationSpawn region binder arity =>
      exact applyBoundRelationSpawn_sound context orientation input region binder
        arity receipt happly
  | wireJoin first second =>
      exact applyWireJoin_sound context orientation input first second receipt
        happly
  | erasure selection =>
      exact applyErasure_sound context orientation input selection receipt happly
  | wireSever wire keep =>
      exact applyWireSever_sound context orientation input wire keep receipt
        happly
  | iteration selection target =>
      exact applyIteration_sound context orientation input selection target
        receipt happly
  | deiteration selection witness =>
      exact applyDeiteration_sound context orientation input selection witness
        receipt happly
  | doubleCutIntro selection =>
      exact applyDoubleCutIntro_sound context orientation input selection receipt
        happly
  | doubleCutElim region =>
      exact applyDoubleCutElim_sound context orientation input region receipt
        happly
  | comprehensionInstantiate bubble comprehension attachments binders payload =>
      exact applyComprehensionInstantiate_sound context orientation input bubble
        comprehension attachments binders payload receipt happly
  | comprehensionAbstract wrap comprehension occurrences payload =>
      exact applyComprehensionAbstract_sound context orientation input wrap
        comprehension occurrences payload receipt happly
  | «theorem» theoremIndex selection args direction payload registered =>
      exact applyTheorem_sound context orientation input theoremIndex selection
        args direction payload registered receipt happly
  | vacuousIntro selection arity =>
      exact applyVacuousIntro_sound context orientation input selection arity
        receipt happly
  | vacuousElim region =>
      exact applyVacuousElim_sound context orientation input region receipt happly
end VisualProof.Rule
