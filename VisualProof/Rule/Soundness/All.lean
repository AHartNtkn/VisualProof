import VisualProof.Rule.Soundness.Structural
import VisualProof.Rule.Soundness.Equational
import VisualProof.Rule.Soundness.HighLevel

namespace VisualProof.Rule

open VisualProof
open Diagram

/-- Every successful branch of the sole checked dispatcher preserves
denotation at every transported ordered boundary.  The proof is exhaustive:
each constructor is discharged by its named rule-family obligation. -/
theorem applyStep_sound
    {context : ProofContext signature} {orientation : Orientation}
    {input : Diagram.CheckedDiagram signature} {step : Step context input}
    {receipt : StepReceipt input}
    (happly : applyStep context orientation input step = .ok receipt) :
    SuccessfulReceiptSound context orientation input step receipt := by
  cases step with
  | openTermSpawn region freePorts term =>
      exact applyOpenTermSpawn_sound context orientation input region freePorts
        term receipt happly
  | relationSpawn region definition arity =>
      exact applyRelationSpawn_sound context orientation input region definition
        arity receipt happly
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
  | inconsistentCutElim region first second payload =>
      exact applyInconsistentCutElim_sound context orientation input region first
        second payload receipt happly
  | conversion node payload =>
      exact applyConversion_sound context orientation input node payload receipt
        happly
  | congruenceJoin first second payload =>
      exact applyCongruenceJoin_sound context orientation input first second
        payload receipt happly
  | anchoredWireSplit wire witness endpoints target =>
      exact applyAnchoredWireSplit_sound context orientation input wire witness
        endpoints target receipt happly
  | anchoredWireContract redundant survivor certificate =>
      exact applyAnchoredWireContract_sound context orientation input redundant
        survivor certificate receipt happly
  | headStrip first second payload =>
      exact applyHeadStrip_sound context orientation input first second payload
        receipt happly
  | closedTermIntro region term =>
      exact applyClosedTermIntro_sound context orientation input region term
        receipt happly
  | fusion wire =>
      exact applyFusion_sound context orientation input wire receipt happly
  | fission node path =>
      exact applyFission_sound context orientation input node path receipt happly
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
  | relUnfold node definition payload body_eq =>
      exact applyRelUnfold_sound context orientation input node definition
        payload body_eq receipt happly
  | relFold selection definition args payload body_eq =>
      exact applyRelFold_sound context orientation input selection definition
        args payload body_eq receipt happly

end VisualProof.Rule
