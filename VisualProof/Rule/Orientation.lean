namespace VisualProof

/-- Replay direction is explicit data checked by every directional rule. -/
inductive Orientation
  | forward
  | backward
  deriving Repr, DecidableEq

/-- The proposition-level direction selected by a replay orientation. -/
def Directed (orientation : Orientation) (source target : Prop) : Prop :=
  match orientation with
  | .forward => source → target
  | .backward => target → source

end VisualProof
