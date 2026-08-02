import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame

namespace VisualProof

/-! Executable equality for compiler-produced intrinsic regions. -/

namespace IntrinsicEquality

private def DefVar.decEq :
    (left right : DefVar defs args) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private instance : DecidableEq (DefVar defs args) :=
  DefVar.decEq

private def Vars.decEq :
    (left right : Vars ctx args) → Decidable (left = right)
  | .nil, .nil => isTrue rfl
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      match Var.decEq leftHead rightHead, decEq leftTail rightTail with
      | isTrue headEqual, isTrue tailEqual =>
          isTrue (by cases headEqual; cases tailEqual; rfl)
      | isFalse different, _ =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)
      | _, isFalse different =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)

private instance : DecidableEq (Vars ctx args) :=
  Vars.decEq

deriving instance DecidableEq for Region
deriving instance DecidableEq for Item
deriving instance DecidableEq for ItemSeq

end IntrinsicEquality

open IntrinsicEquality in
def intrinsicRegionsEqual
    (left right : Region definitions ctx) : Bool :=
  decide (left = right)

open IntrinsicEquality in
theorem intrinsicRegionsEqual_sound
    {left right : Region definitions ctx}
    (accepted : intrinsicRegionsEqual left right = true) :
    left = right := by
  simpa [intrinsicRegionsEqual] using of_decide_eq_true accepted

end VisualProof
