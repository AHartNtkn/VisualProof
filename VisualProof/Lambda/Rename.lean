import VisualProof.Lambda.Syntax

namespace VisualProof.Lambda

private def liftRenaming (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def Term.renameBound (ρ : Fin n → Fin m) : Term n α → Term m α
  | .bvar i => .bvar (ρ i)
  | .port x => .port x
  | .lam body => .lam (body.renameBound (liftRenaming ρ))
  | .app fn arg => .app (fn.renameBound ρ) (arg.renameBound ρ)

def Term.lift : Term n α → Term (n + 1) α :=
  Term.renameBound Fin.succ

theorem Term.renameBound_id (t : Term n α) :
    t.renameBound id = t := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [renameBound]
      rw [show liftRenaming id = id by
        funext i
        refine Fin.cases ?_ (fun _ => ?_) i <;> rfl]
      exact congrArg Term.lam ih
  | app _ _ ihFn ihArg => simp only [renameBound, ihFn, ihArg]

theorem Term.renameBound_comp
    (t : Term n α) (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (t.renameBound ρ).renameBound τ = t.renameBound (τ ∘ ρ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [renameBound]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun r => Term.renameBound r body)
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | app _ _ ihFn ihArg => simp only [renameBound, ihFn, ihArg]

theorem Term.lift_renameBound
    (t : Term n α) (ρ : Fin n → Fin m) :
    (t.renameBound ρ).lift =
      t.lift.renameBound (Fin.cases 0 (fun i => Fin.succ (ρ i))) := by
  simp only [lift, renameBound_comp]
  apply congrArg (fun r => t.renameBound r)
  funext i
  rfl

end VisualProof.Lambda
