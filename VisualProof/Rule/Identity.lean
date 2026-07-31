import VisualProof.Rule.Structural
import VisualProof.Rule.WirePrimitive.Partition
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics

namespace VisualProof

universe u

open StructuralCore WirePrimitive.Partition

/--
Identity substitution is the derived composition of ordinary iteration,
signature-indexed scoped sever, and eager one-point normalization.  The sever
orientation supplies the only directed step; iteration and normalization are
equivalences.
-/
theorem identity_substitution_derived_sound
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    {iterationInput : OrdinaryIterationInput selection occurrence}
    (iteration : CheckedOrdinaryIteration iterationInput)
    (severInput : WireSeverInput iteration.target)
    (sever : AppliedWireSever iteration.target severInput)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed severInput.orientation
      (denoteChecked pre definitionEnv iteration.source)
      (denoteChecked pre definitionEnv
        (ConcreteDiagram.normalizeIdentities sever.target).target) := by
  have copied := iteration.equivalence pre definitionEnv
  have severed :=
    wire_sever_sound severInput sever pre definitionEnv
  have normalized :=
    ConcreteDiagram.normalizeIdentities_sound sever.target pre definitionEnv
  cases orientation : severInput.orientation with
  | forward =>
      have severedForward :
          denoteChecked pre definitionEnv iteration.target →
            denoteChecked pre definitionEnv sever.target := by
        simpa [Directed, orientation] using severed
      intro sourceHolds
      exact normalized.mpr
        (severedForward (copied.mp sourceHolds))
  | backward =>
      have severedBackward :
          denoteChecked pre definitionEnv sever.target →
            denoteChecked pre definitionEnv iteration.target := by
        simpa [Directed, orientation] using severed
      intro targetHolds
      exact copied.mpr
        (severedBackward (normalized.mp targetHolds))

end VisualProof
