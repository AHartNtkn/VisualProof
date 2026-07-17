import VisualProof.Lambda.Reduction

namespace VisualProof.Lambda

/-- A beta-eta normal form has no outgoing one-step contraction. -/
def Normal (term : Term n α) : Prop :=
  ∀ next, ¬ OneStep term next

/-- A reduction starting at a normal form cannot move. -/
theorem Reduces.eq_of_normal {start finish : Term n α}
    (normal : Normal start) (reduces : Reduces start finish) :
    finish = start := by
  induction reduces with
  | refl => rfl
  | @tail middle finish reduces step ih =>
      have hmiddle : middle = start := ih
      subst middle
      exact False.elim (normal finish step)

/-- Distinct certified normal forms cannot be beta-eta equivalent. -/
theorem not_betaEta_of_normal_ne {left right : Term n α}
    (leftNormal : Normal left) (rightNormal : Normal right)
    (different : left ≠ right) :
    ¬ BetaEta left right := by
  intro equivalent
  obtain ⟨common, leftReduces, rightReduces⟩ := churchRosser equivalent
  have hleft : common = left := leftReduces.eq_of_normal leftNormal
  have hright : common = right := rightReduces.eq_of_normal rightNormal
  exact different (hleft.symm.trans hright)

end VisualProof.Lambda
