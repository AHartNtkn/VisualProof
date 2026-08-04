import VisualProof.Rule.Soundness.All

namespace VisualProof.Proof

open VisualProof
open Diagram
open Rule

/-- Execute one rule on an open proof state. A successful concrete rewrite is
rejected when it deletes any pinned boundary identity. -/
def applyOpenStep (context : ProofContext signature)
    (orientation : Orientation) (input : OpenProofState signature)
    (action : Step context input.diagram) :
    Except StepError (OpenProofState signature) :=
  match applyStep context orientation input.diagram action with
  | .error error => .error error
  | .ok receipt =>
      match receipt.transportOpen input.boundary input.boundary_root_scoped with
      | none => .error .boundaryMismatch
      | some result => .ok result

/-- A typed executable proof program indexed by the complete open state. The
continuation is indexed by the actual boundary-transported result of the sole
dispatcher, so neither a diagram nor its boundary can be substituted. -/
inductive Program (context : ProofContext signature) (orientation : Orientation) :
    OpenProofState signature → Type
  | done (input) : Program context orientation input
  | step {input : OpenProofState signature}
      (action : Step context input.diagram)
      (next : ∀ result,
        applyOpenStep context orientation input action = .ok result →
          Program context orientation result) :
      Program context orientation input

def replay (context : ProofContext signature) (orientation : Orientation) :
    (input : OpenProofState signature) → Program context orientation input →
      Except StepError (OpenProofState signature)
  | input, .done _ => .ok input
  | input, .step action next =>
      match happly : applyOpenStep context orientation input action with
      | .error error => .error error
      | .ok result => replay context orientation result (next result happly)

/-- Closed replay is the empty-boundary specialization of open replay. -/
def replayClosed (context : ProofContext signature)
    (orientation : Orientation) (input : CheckedDiagram signature)
    (program : Program context orientation (OpenProofState.closed input)) :
    Except StepError (OpenProofState signature) :=
  replay context orientation (OpenProofState.closed input) program

/-- Transport an ordered boundary assignment along the positional arity
equality established by successful replay.  Aliased boundary positions remain
aliased because this changes only the finite index type, never the values. -/
def transportArgs {sourceLength targetLength : Nat}
    (length_eq : targetLength = sourceLength)
    (args : Fin sourceLength → D) : Fin targetLength → D :=
  args ∘ Fin.cast length_eq

@[simp] theorem transportArgs_rfl (args : Fin length → D) :
    transportArgs rfl args = args := by
  rfl

theorem transportArgs_trans
    (first : middleLength = sourceLength)
    (second : targetLength = middleLength)
    (args : Fin sourceLength → D) :
    transportArgs second (transportArgs first args) =
      transportArgs (second.trans first) args := by
  subst middleLength
  subst targetLength
  rfl

/-- Boundary-parametric semantic composition between two checked open states.
The equality records that the same ordered boundary positions survive, while
`sound` records the implication in the selected proof orientation. -/
structure ReplayEntailment (orientation : Orientation)
    (source target : OpenProofState signature)
    (named : NamedEnv Lambda.Individual signature) : Prop where
  boundaryLength : target.boundary.length = source.boundary.length
  sound : ∀ args : Fin source.boundary.length → Lambda.Individual,
    DirectedImplication orientation
      (source.denote Lambda.canonicalModel named args)
      (target.denote Lambda.canonicalModel named
        (transportArgs boundaryLength args))

namespace ReplayEntailment

theorem refl (orientation : Orientation) (state : OpenProofState signature)
    (named : NamedEnv Lambda.Individual signature) :
    ReplayEntailment orientation state state named := by
  refine ⟨rfl, ?_⟩
  intro args
  cases orientation <;> exact id

theorem trans
    (first : ReplayEntailment orientation source middle named)
    (second : ReplayEntailment orientation middle target named) :
    ReplayEntailment orientation source target named := by
  refine ⟨second.boundaryLength.trans first.boundaryLength, ?_⟩
  intro args
  have htransport := transportArgs_trans first.boundaryLength
    second.boundaryLength args
  cases orientation with
  | forward =>
      intro sourceDenotes
      have middleDenotes := first.sound args sourceDenotes
      have targetDenotes := second.sound
        (transportArgs first.boundaryLength args) middleDenotes
      simpa only [htransport] using targetDenotes
  | backward =>
      intro targetDenotes
      have targetDenotes' : target.denote Lambda.canonicalModel named
          (transportArgs second.boundaryLength
            (transportArgs first.boundaryLength args)) := by
        simpa only [htransport] using targetDenotes
      have middleDenotes := second.sound
        (transportArgs first.boundaryLength args) targetDenotes'
      exact first.sound args middleDenotes

end ReplayEntailment

private theorem directedEntailment_implication
    (sound : DirectedEntailment tag orientation before after) :
    DirectedImplication orientation before after := by
  unfold DirectedEntailment at sound
  cases hmode : tag.semanticMode <;> simp only [hmode] at sound
  · exact sound
  · cases orientation with
    | forward => exact sound.mp
    | backward => exact sound.mpr

/-- One successful open step is semantically sound directly from the checked
dispatcher theorem; replay has no separately supplied soundness authority. -/
theorem applyOpenStep_sound
    (happly : applyOpenStep context orientation input action = .ok result)
    (valid : context.Valid) :
    ReplayEntailment orientation input result
      (Theory.interpretDefinitions context.definitions) := by
  unfold applyOpenStep at happly
  split at happly
  · contradiction
  · rename_i receipt hstep
    split at happly
    · contradiction
    · rename_i transported htransport
      obtain ⟨mapped, hboundary, rfl⟩ :=
        receipt.transportOpen_result input.boundary
          input.boundary_root_scoped transported htransport
      cases happly
      have stepSound := Rule.applyStep_sound hstep input.boundary
        input.boundary_root_scoped mapped hboundary valid
      refine ⟨receipt.interface.transportBoundary_length hboundary, ?_⟩
      intro args
      exact directedEntailment_implication (stepSound args)

/-- Sound replay in either orientation.  Forward replay composes source-to-
target implications; backward replay composes target-to-source implications. -/
theorem replay_sound
    (program : Program context orientation input)
    (hreplay : replay context orientation input program = .ok finish)
    (valid : context.Valid) :
    ReplayEntailment orientation input finish
      (Theory.interpretDefinitions context.definitions) := by
  induction program with
  | done input =>
      simp [replay] at hreplay
      cases hreplay
      exact ReplayEntailment.refl orientation finish
        (Theory.interpretDefinitions context.definitions)
  | @step input action next ih =>
      simp only [replay] at hreplay
      split at hreplay
      · contradiction
      · rename_i result happly
        exact ReplayEntailment.trans
          (applyOpenStep_sound happly valid)
          (ih result happly hreplay)

/-- Forward replay preserves denotation for every ordered boundary assignment. -/
theorem forward_replay_sound
    (program : Program context .forward input)
    (hreplay : replay context .forward input program = .ok finish)
    (valid : context.Valid) :
    ∃ length_eq : finish.boundary.length = input.boundary.length,
      ∀ args : Fin input.boundary.length → Lambda.Individual,
        input.denote Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions) args →
          finish.denote Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (transportArgs length_eq args) := by
  let sound := replay_sound program hreplay valid
  exact ⟨sound.boundaryLength, sound.sound⟩

/-- Backward replay is goal reduction: denotation of the reduced endpoint for
the transported assignment entails denotation of the original goal. -/
theorem backward_replay_sound
    (program : Program context .backward goal)
    (hreplay : replay context .backward goal program = .ok reduced)
    (valid : context.Valid) :
    ∃ length_eq : reduced.boundary.length = goal.boundary.length,
      ∀ args : Fin goal.boundary.length → Lambda.Individual,
        reduced.denote Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (transportArgs length_eq args) →
          goal.denote Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions) args := by
  let sound := replay_sound program hreplay valid
  exact ⟨sound.boundaryLength, sound.sound⟩

end VisualProof.Proof
