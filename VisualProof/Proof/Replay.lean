import VisualProof.Concrete.Step

namespace VisualProof.Proof

open VisualProof.Concrete

/-- A typed executable proof program indexed by the complete concrete state.
Each continuation is indexed by the exact receipt returned by the sole public
executor. -/
inductive Program (orientation : Orientation) {arity : Nat} :
    State arity → Type
  | done (input) : Program orientation input
  | step {input : State arity}
      (action : Step input)
      (next : ∀ receipt,
        execute orientation input action = .ok receipt →
          Program orientation receipt.target) :
      Program orientation input

/-- Execute a certified program exclusively through `Concrete.execute`. -/
def replay (orientation : Orientation) {arity : Nat} :
    (input : State arity) → Program orientation input →
      Except Error (State arity)
  | input, .done _ => .ok input
  | input, .step action next =>
      match happly : execute orientation input action with
      | .error error => .error error
      | .ok receipt =>
          replay orientation receipt.target (next receipt happly)

/-- Closed replay is the arity-zero specialization of concrete replay. -/
def replayClosed (orientation : Orientation) (input : Concrete.Checked)
    (program : Program orientation (State.closed input)) :
    Except Error (State 0) :=
  replay orientation (State.closed input) program

end VisualProof.Proof
