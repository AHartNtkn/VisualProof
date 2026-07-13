import VisualProof.Lambda.Rename

namespace VisualProof.Lambda

def Term.traverseBound [Applicative F]
    (σ : Fin n → F (Term m α)) : Term n α → F (Term m α)
  | .bvar i => σ i
  | .port x => pure (.port x)
  | .lam body =>
      Term.lam <$> body.traverseBound
        (Fin.cases (pure (Term.bvar 0)) (fun i => Term.lift <$> σ i))
  | .app fn arg => Term.app <$> fn.traverseBound σ <*> arg.traverseBound σ

def Term.substBound (σ : Fin n → Term m α) (t : Term n α) : Term m α :=
  Id.run (t.traverseBound (F := Id) σ)

def Term.substBoundOption
    (σ : Fin n → Option (Term m α)) (t : Term n α) : Option (Term m α) :=
  t.traverseBound σ

@[simp] theorem Term.substBound_bvar
    (σ : Fin n → Term m α) (i : Fin n) :
    (Term.bvar i).substBound σ = σ i := rfl

@[simp] theorem Term.substBound_port
    (σ : Fin n → Term m α) (x : α) :
    (Term.port x).substBound σ = Term.port x := rfl

@[simp] theorem Term.substBound_lam
    (σ : Fin n → Term m α) (body : Term (n + 1) α) :
    (Term.lam body).substBound σ =
      Term.lam (body.substBound
        (Fin.cases (Term.bvar 0) (fun i => (σ i).lift))) := rfl

@[simp] theorem Term.substBound_app
    (σ : Fin n → Term m α) (fn arg : Term n α) :
    (Term.app fn arg).substBound σ =
      Term.app (fn.substBound σ) (arg.substBound σ) := rfl

@[simp] theorem Term.substBoundOption_bvar
    (σ : Fin n → Option (Term m α)) (i : Fin n) :
    (Term.bvar i).substBoundOption σ = σ i := rfl

@[simp] theorem Term.substBoundOption_port
    (σ : Fin n → Option (Term m α)) (x : α) :
    (Term.port x).substBoundOption σ = some (Term.port x) := rfl

@[simp] theorem Term.substBoundOption_lam
    (σ : Fin n → Option (Term m α)) (body : Term (n + 1) α) :
    (Term.lam body).substBoundOption σ =
      (body.substBoundOption
        (Fin.cases (some (Term.bvar 0))
          (fun i => (σ i).map Term.lift))).map Term.lam := rfl

@[simp] theorem Term.substBoundOption_app
    (σ : Fin n → Option (Term m α)) (fn arg : Term n α) :
    (Term.app fn arg).substBoundOption σ =
      Term.app <$> fn.substBoundOption σ <*> arg.substBoundOption σ := rfl

theorem Term.substBoundOption_rename_leftInverse
    (t : Term n α) (ρ : Fin n → Fin m)
    (σ : Fin m → Option (Term n α))
    (hσ : ∀ i, σ (ρ i) = some (Term.bvar i)) :
    (t.renameBound ρ).substBoundOption σ = some t := by
  induction t generalizing m with
  | bvar i => exact hσ i
  | port _ => rfl
  | lam body ih =>
      simp only [Term.renameBound, Term.substBoundOption_lam,
        Option.map_eq_some_iff]
      refine ⟨body, ?_, rfl⟩
      apply ih
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change Option.map Term.lift (σ (ρ j)) = some (Term.bvar j.succ)
        rw [hσ]
        rfl
  | app fn arg ihFn ihArg =>
      simp only [Term.renameBound, Term.substBoundOption_app]
      rw [ihFn ρ σ hσ, ihArg ρ σ hσ]
      rfl

theorem Term.renameBound_of_substBoundOption
    (t : Term n α) (σ : Fin n → Option (Term m α))
    (ρ : Fin m → Fin n) {u : Term m α}
    (hσ : ∀ i v, σ i = some v → v.renameBound ρ = Term.bvar i)
    (h : t.substBoundOption σ = some u) :
    u.renameBound ρ = t := by
  induction t generalizing m with
  | bvar i => exact hσ i u h
  | port _ => cases h; rfl
  | lam body ih =>
      simp only [Term.substBoundOption_lam, Option.map_eq_some_iff] at h
      obtain ⟨body', hbody, rfl⟩ := h
      apply congrArg Term.lam
      apply ih
        (σ := Fin.cases (some (Term.bvar 0))
          (fun i => (σ i).map Term.lift))
        (ρ := Fin.cases 0 (fun i => Fin.succ (ρ i))) (u := body') ?_ hbody
      exact fun i => Fin.cases
        (fun v hv => by
          change some (Term.bvar 0) = some v at hv
          cases hv
          rfl)
        (fun j v hv => by
          change Option.map Term.lift (σ j) = some v at hv
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
          rw [← Term.lift_renameBound, hσ j w hw]
          rfl)
        i
  | app fn arg ihFn ihArg =>
      simp only [Term.substBoundOption_app] at h
      generalize hfn : Term.substBoundOption σ fn = ofn at h
      generalize harg : Term.substBoundOption σ arg = oarg at h
      cases ofn with
      | none => cases oarg <;> contradiction
      | some fn' =>
          cases oarg with
          | none => contradiction
          | some arg' =>
              cases h
              simp only [Term.renameBound]
              congr
              · exact ihFn (σ := σ) (ρ := ρ) (u := fn') hσ hfn
              · exact ihArg (σ := σ) (ρ := ρ) (u := arg') hσ harg

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
      simp only [substBound_lam, renameBound]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (lift_renameBound (σ j) ρ).symm
  | app _ _ ihFn ihArg =>
      simp only [substBound_app, renameBound, ihFn, ihArg]

theorem Term.substBound_renameBound
    (t : Term n α) (ρ : Fin n → Fin m) (σ : Fin m → Term k α) :
    (t.renameBound ρ).substBound σ = t.substBound (σ ∘ ρ) := by
  induction t generalizing m k with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [renameBound, substBound_lam]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  | app _ _ ihFn ihArg =>
      simp only [renameBound, substBound_app, ihFn, ihArg]

theorem Term.substBound_id (t : Term n α) :
    t.substBound Term.bvar = t := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam body ih =>
      simp only [substBound_lam]
      rw [show Fin.cases (Term.bvar 0) (fun i => (Term.bvar i).lift) =
          Term.bvar by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cases_zero]
        · simp only [lift, renameBound, Fin.cases_succ]]
      exact congrArg Term.lam ih
  | app _ _ ihFn ihArg => simp only [substBound_app, ihFn, ihArg]

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
      simp only [substBound_lam]
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (fun s => Term.substBound s body)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (lift_substBound (σ j) τ).symm
  | app _ _ ihFn ihArg => simp only [substBound_app, ihFn, ihArg]

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
      simp only [substBound_lam, bindFree]
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
      simp only [substBound_app, bindFree]
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
