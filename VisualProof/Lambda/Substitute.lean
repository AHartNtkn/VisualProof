import VisualProof.Lambda.Rename

namespace VisualProof.Lambda

private def liftSubstitution (σ : Fin n → Term m α) :
    Fin (n + 1) → Term (m + 1) α :=
  Fin.cases (Term.bvar 0) (fun i => (σ i).lift)

def Term.substBound (σ : Fin n → Term m α) : Term n α → Term m α
  | .bvar i => σ i
  | .port x => .port x
  | .lam body => .lam (body.substBound (liftSubstitution σ))
  | .app fn arg => .app (fn.substBound σ) (arg.substBound σ)

def Term.bindFree (σ : α → Term n β) : Term n α → Term n β
  | .bvar i => .bvar i
  | .port x => σ x
  | .lam body => .lam (body.bindFree (fun x => (σ x).lift))
  | .app fn arg => .app (fn.bindFree σ) (arg.bindFree σ)

private theorem Term.renameBound_comp
    (t : Term n α) (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (t.renameBound ρ).renameBound τ = t.renameBound (τ ∘ ρ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [renameBound]
      apply congrArg TermCore.lam
      rw [ih]
      apply congrArg (fun r => Term.renameBound r body)
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | app _ _ ihFn ihArg => simp only [renameBound, ihFn, ihArg]

private theorem Term.renameBound_bindFree
    (t : Term n α) (f : α → Term n β) (ρ : Fin n → Fin m) :
    (t.bindFree f).renameBound ρ =
      (t.renameBound ρ).bindFree (fun x => (f x).renameBound ρ) := by
  induction t generalizing m with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [bindFree, renameBound]
      apply congrArg TermCore.lam
      rw [ih]
      apply congrArg (fun h =>
        Term.bindFree h
          (Term.renameBound (fun i => Fin.cases 0 (fun j => Fin.succ (ρ j)) i) body))
      funext x
      simp only [lift]
      rw [renameBound_comp, renameBound_comp]
      apply congrArg (fun r => (f x).renameBound r)
      funext i
      rfl
  | app _ _ ihFn ihArg => simp only [bindFree, renameBound, ihFn, ihArg]

theorem Term.substBound_id (t : Term n α) :
    t.substBound Term.bvar = t := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [substBound]
      rw [show liftSubstitution Term.bvar = Term.bvar by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl]
      exact congrArg Term.lam ih
  | app _ _ ihFn ihArg => simp only [substBound, ihFn, ihArg]

theorem Term.bindFree_id (t : Term n α) :
    t.bindFree Term.port = t := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [bindFree]
      rw [show (fun x => (Term.port x).lift) = Term.port by rfl]
      exact congrArg Term.lam ih
  | app _ _ ihFn ihArg => simp only [bindFree, ihFn, ihArg]

theorem Term.bindFree_assoc
    (t : Term n α) (f : α → Term n β) (g : β → Term n γ) :
    (t.bindFree f).bindFree g = t.bindFree (fun x => (f x).bindFree g) := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [bindFree]
      rw [ih]
      congr
      funext x
      exact (renameBound_bindFree (f x) g Fin.succ).symm
  | app _ _ ihFn ihArg => simp only [bindFree, ihFn, ihArg]

end VisualProof.Lambda
