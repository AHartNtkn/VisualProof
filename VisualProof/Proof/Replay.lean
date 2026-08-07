import VisualProof.Rule.Soundness.All

namespace VisualProof.Proof

open VisualProof.Concrete

open VisualProof
open Diagram
open Rule

/-- Execute one rule on an open proof state. A successful concrete rewrite is
rejected when it deletes any pinned boundary identity. -/
def applyOpenStep (orientation : Orientation) (input : OperationState )
    (action : OperationStep input.diagram) :
    Except Error (OperationState ) :=
  match applyRawOperation orientation input.diagram action with
  | .error error => .error error
  | .ok receipt =>
      match receipt.transportOpen input.boundary input.boundary_root_scoped with
      | none => .error .boundaryMismatch
      | some result => .ok result

/-- A typed executable proof program indexed by the complete open state. The
continuation is indexed by the actual boundary-transported raw proof-tower
result, so neither a diagram nor its boundary can be substituted. -/
inductive Program (orientation : Orientation) :
    OperationState  → Type
  | done (input) : Program orientation input
  | step {input : OperationState }
      (action : OperationStep input.diagram)
      (next : ∀ result,
        applyOpenStep orientation input action = .ok result →
          Program orientation result) :
      Program orientation input

def replay (orientation : Orientation) :
    (input : OperationState ) → Program orientation input →
      Except Error (OperationState )
  | input, .done _ => .ok input
  | input, .step action next =>
      match happly : applyOpenStep orientation input action with
      | .error error => .error error
      | .ok result => replay orientation result (next result happly)

/-- Closed replay is the empty-boundary specialization of open replay. -/
def replayClosed (orientation : Orientation) (input : Concrete.Checked )
    (program : Program orientation (OperationState.closed input)) :
    Except Error (OperationState ) :=
  replay orientation (OperationState.closed input) program

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
    (source target : OperationState )
    (model : Model) : Prop where
  boundaryLength : target.boundary.length = source.boundary.length
  sound : ∀ args : Fin source.boundary.length → model.Carrier,
    OperationImplication orientation
      (source.denote model  args)
      (target.denote model
        (transportArgs boundaryLength args))

namespace ReplayEntailment

theorem refl (orientation : Orientation) (state : OperationState )
    (model : Model) :
    ReplayEntailment orientation state state model  := by
  refine ⟨rfl, ?_⟩
  intro args
  cases orientation <;> exact id

theorem trans
    (first : ReplayEntailment orientation source middle model )
    (second : ReplayEntailment orientation middle target model ) :
    ReplayEntailment orientation source target model  := by
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
      have targetDenotes' : target.denote model
          (transportArgs second.boundaryLength
            (transportArgs first.boundaryLength args)) := by
        simpa only [htransport] using targetDenotes
      have middleDenotes := second.sound
        (transportArgs first.boundaryLength args) targetDenotes'
      exact first.sound args middleDenotes

end ReplayEntailment

private theorem directedEntailment_implication
    (sound : OperationEntailment tag orientation before after) :
    OperationImplication orientation before after := by
  unfold OperationEntailment at sound
  cases hmode : tag.operationMode <;> simp only [hmode] at sound
  · exact sound
  · cases orientation with
    | forward => exact sound.mp
    | backward => exact sound.mpr

/-- One successful open step is semantically sound from the raw operation
proof tower; replay has no separately supplied soundness assumption. -/
theorem applyOpenStep_sound
    (happly : applyOpenStep orientation input action = .ok result) :
    ReplayEntailment orientation input result model := by
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
      have stepSound := Rule.applyOperation_sound hstep model input.boundary
        input.boundary_root_scoped mapped hboundary
      refine ⟨receipt.interface.transportBoundary_length hboundary, ?_⟩
      intro args
      exact directedEntailment_implication (stepSound args)

/-- Sound replay in either orientation.  Forward replay composes source-to-
target implications; backward replay composes target-to-source implications. -/
theorem replay_sound
    (program : Program orientation input)
    (hreplay : replay orientation input program = .ok finish) :
    ReplayEntailment orientation input finish model := by
  induction program with
  | done input =>
      simp [replay] at hreplay
      cases hreplay
      exact ReplayEntailment.refl orientation finish
        model
  | @step input action next ih =>
      simp only [replay] at hreplay
      split at hreplay
      · contradiction
      · rename_i result happly
        exact ReplayEntailment.trans
          (applyOpenStep_sound happly)
          (ih result happly hreplay)

/-- Forward replay preserves denotation for every ordered boundary assignment. -/
theorem forward_replay_sound
    (program : Program .forward input)
    (hreplay : replay .forward input program = .ok finish) :
    ∃ length_eq : finish.boundary.length = input.boundary.length,
      ∀ args : Fin input.boundary.length → model.Carrier,
        input.denote model args →
          finish.denote model
            (transportArgs length_eq args) := by
  let sound := replay_sound (model := model) program hreplay
  exact ⟨sound.boundaryLength, sound.sound⟩

/-- Backward replay is goal reduction: denotation of the reduced endpoint for
the transported assignment entails denotation of the original goal. -/
theorem backward_replay_sound
    (program : Program .backward goal)
    (hreplay : replay .backward goal program = .ok reduced) :
    ∃ length_eq : reduced.boundary.length = goal.boundary.length,
      ∀ args : Fin goal.boundary.length → model.Carrier,
        reduced.denote model
            (transportArgs length_eq args) →
          goal.denote model args := by
  let sound := replay_sound (model := model) program hreplay
  exact ⟨sound.boundaryLength, sound.sound⟩

end VisualProof.Proof
