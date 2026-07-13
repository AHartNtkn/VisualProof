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

theorem Term.renameBound_bindFree
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

theorem Term.renameBound_substBound
    (t : Term n α) (σ : Fin n → Term m α) (ρ : Fin m → Fin k) :
    (t.substBound σ).renameBound ρ =
      t.substBound (fun i => (σ i).renameBound ρ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [substBound, renameBound]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (lift_renameBound (σ j) ρ).symm
  | app _ _ ihFn ihArg => simp only [substBound, renameBound, ihFn, ihArg]

theorem Term.substBound_renameBound
    (t : Term n α) (ρ : Fin n → Fin m) (σ : Fin m → Term k α) :
    (t.renameBound ρ).substBound σ = t.substBound (σ ∘ ρ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [renameBound, substBound]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | app _ _ ihFn ihArg => simp only [renameBound, substBound, ihFn, ihArg]

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

theorem Term.lift_substBound
    (t : Term n α) (σ : Fin n → Term m α) :
    (t.substBound σ).lift =
      t.lift.substBound
        (Fin.cases (Term.bvar 0) (fun i => (σ i).lift)) := by
  simp only [lift, renameBound_substBound, substBound_renameBound]
  apply congrArg (fun s => t.substBound s)
  funext i
  rfl

theorem Term.substBound_comp
    (t : Term n α) (σ : Fin n → Term m α) (τ : Fin m → Term k α) :
    (t.substBound σ).substBound τ =
      t.substBound (fun i => (σ i).substBound τ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [substBound]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (lift_substBound (σ j) τ).symm
  | app _ _ ihFn ihArg => simp only [substBound, ihFn, ihArg]

private theorem Term.bindFree_substBound_of_compatible
    (t : Term n α)
    (σ : Fin n → Term m α)
    (f : α → Term n β)
    (g : α → Term m β)
    (τ : Fin n → Term m β)
    (hbound : ∀ i, (σ i).bindFree g = τ i)
    (hfree : ∀ x, g x = (f x).substBound τ) :
    (t.substBound σ).bindFree g = (t.bindFree f).substBound τ := by
  induction t generalizing m with
  | bvar i => exact hbound i
  | port x => exact hfree x
  | lam body ih =>
      simp only [substBound, bindFree]
      apply congrArg Term.lam
      apply ih
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · calc
            ((σ j).lift).bindFree (fun x => (g x).lift) =
                ((σ j).bindFree g).lift :=
              (renameBound_bindFree (σ j) g Fin.succ).symm
            _ = (τ j).lift := congrArg Term.lift (hbound j)
      · intro x
        calc
          (g x).lift = ((f x).substBound τ).lift :=
            congrArg Term.lift (hfree x)
          _ = (f x).lift.substBound
                (Fin.cases (Term.bvar 0) (fun i => (τ i).lift)) :=
            lift_substBound (f x) τ
  | app _ _ ihFn ihArg =>
      simp only [substBound, bindFree]
      rw [ihFn _ _ _ _ hbound hfree, ihArg _ _ _ _ hbound hfree]

theorem Term.bindFree_substBound
    (body : Term (n + 1) α) (arg : Term n α) (f : α → Term n β) :
    (body.substBound (Fin.cases arg Term.bvar)).bindFree f =
      (body.bindFree (fun x => (f x).lift)).substBound
        (Fin.cases (arg.bindFree f) Term.bvar) := by
  apply bindFree_substBound_of_compatible
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · intro x
    simp only [lift, substBound_renameBound]
    rw [show (Fin.cases (arg.bindFree f) Term.bvar) ∘ Fin.succ = Term.bvar by
      funext i
      rfl]
    exact (substBound_id (f x)).symm

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
