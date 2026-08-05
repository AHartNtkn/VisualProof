import VisualProof.Rule.Soundness.Structural
import VisualProof.Rule.Soundness.HighLevel

namespace VisualProof.Rule

open VisualProof
open Diagram

/-- Every successful branch of the sole checked dispatcher preserves
denotation at every transported ordered boundary.  The proof is exhaustive:
each constructor is discharged by its  rule-family obligation. -/
theorem applyStep_sound
    {orientation : Orientation}
    {input : Diagram.CheckedDiagram } {step : Step input}
    {receipt : StepReceipt input}
    (happly : applyStep orientation input step = .ok receipt) :
    SuccessfulReceiptSound orientation input step receipt := by
  cases step with
  | boundRelationSpawn region binder arity =>
      exact applyBoundRelationSpawn_sound orientation input region binder
        arity receipt happly
  | wireJoin first second =>
      exact applyWireJoin_sound orientation input first second receipt
        happly
  | erasure selection =>
      exact applyErasure_sound orientation input selection receipt happly
  | wireSever wire keep =>
      exact applyWireSever_sound orientation input wire keep receipt
        happly
  | iteration selection target =>
      exact applyIteration_sound orientation input selection target
        receipt happly
  | deiteration selection witness =>
      exact applyDeiteration_sound orientation input selection witness
        receipt happly
  | doubleCutIntro selection =>
      exact applyDoubleCutIntro_sound orientation input selection receipt
        happly
  | doubleCutElim region =>
      exact applyDoubleCutElim_sound orientation input region receipt
        happly
  | comprehensionInstantiate bubble comprehension attachments binders payload =>
      exact applyComprehensionInstantiate_sound orientation input bubble
        comprehension attachments binders payload receipt happly
  | comprehensionAbstract wrap comprehension occurrences payload =>
      exact applyComprehensionAbstract_sound orientation input wrap
        comprehension occurrences payload receipt happly
  | vacuousIntro selection arity =>
      exact applyVacuousIntro_sound orientation input selection arity
        receipt happly
  | vacuousElim region =>
      exact applyVacuousElim_sound orientation input region receipt happly
end VisualProof.Rule
