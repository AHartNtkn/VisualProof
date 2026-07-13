import VisualProof.Lambda.Substitute

namespace VisualProof.Lambda

private def liftOptionSubstitution (σ : Fin n → Option (Term m α)) :
    Fin (n + 1) → Option (Term (m + 1) α) :=
  Fin.cases (some (Term.bvar 0)) (fun i => (σ i).map Term.lift)

private def Term.substBoundOption (σ : Fin n → Option (Term m α)) :
    Term n α → Option (Term m α)
  | .bvar i => σ i
  | .port x => some (.port x)
  | .lam body => (body.substBoundOption (liftOptionSubstitution σ)).map Term.lam
  | .app fn arg =>
      match fn.substBoundOption σ, arg.substBoundOption σ with
      | some fn', some arg' => some (.app fn' arg')
      | _, _ => none

private def dropZero : Fin (n + 1) → Option (Term n α) :=
  Fin.cases none (fun i => some (Term.bvar i))

def Term.unlift (t : Term (n + 1) α) : Option (Term n α) :=
  t.substBoundOption dropZero

private theorem Term.substBoundOption_rename_leftInverse
    (t : Term n α) (ρ : Fin n → Fin m)
    (σ : Fin m → Option (Term n α))
    (hσ : ∀ i, σ (ρ i) = some (Term.bvar i)) :
    (t.renameBound ρ).substBoundOption σ = some t := by
  induction t generalizing m with
  | bvar i => exact hσ i
  | port _ => rfl
  | lam body ih =>
      simp only [Term.renameBound, Term.substBoundOption, Option.map_eq_some_iff]
      refine ⟨body, ?_, rfl⟩
      apply ih
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change Option.map Term.lift (σ (ρ j)) = some (Term.bvar j.succ)
        rw [hσ]
        rfl
  | app fn arg ihFn ihArg =>
      simp only [Term.renameBound, Term.substBoundOption]
      rw [ihFn ρ σ hσ, ihArg ρ σ hσ]

theorem Term.unlift_lift (t : Term n α) : t.lift.unlift = some t := by
  apply Term.substBoundOption_rename_leftInverse
  intro i
  rfl

private theorem Term.renameBound_of_substBoundOption
    (t : Term n α) (σ : Fin n → Option (Term m α))
    (ρ : Fin m → Fin n) {u : Term m α}
    (hσ : ∀ i v, σ i = some v → v.renameBound ρ = Term.bvar i)
    (h : t.substBoundOption σ = some u) :
    u.renameBound ρ = t := by
  induction t generalizing m with
  | bvar i => exact hσ i u h
  | port _ => cases h; rfl
  | lam body ih =>
      simp only [Term.substBoundOption, Option.map_eq_some_iff] at h
      obtain ⟨body', hbody, rfl⟩ := h
      apply congrArg Term.lam
      apply ih (σ := liftOptionSubstitution σ)
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
      simp only [Term.substBoundOption] at h
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

theorem Term.unlift_sound {t : Term (n + 1) α} {u : Term n α}
    (h : t.unlift = some u) : t = u.lift := by
  symm
  apply Term.renameBound_of_substBoundOption t dropZero Fin.succ (u := u) ?_ h
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> intro v hv
  · change none = some v at hv
    contradiction
  · change some (Term.bvar j) = some v at hv
    cases hv
    rfl

def etaContract (body : Term (n + 1) α) : Option (Term n α) :=
  match body with
  | .app fn (.bvar i) => if i = 0 then fn.unlift else none
  | _ => none

theorem etaContract_sound {body : Term (n + 1) α} {fn : Term n α}
    (h : etaContract body = some fn) :
    body = Term.app fn.lift (Term.bvar 0) := by
  cases body with
  | app f x =>
      cases x with
      | bvar i =>
          simp only [etaContract] at h
          split at h
          next hi => subst i; rw [Term.unlift_sound h]
          next => contradiction
      | port _ => simp only [etaContract] at h; contradiction
      | lam _ => simp only [etaContract] at h; contradiction
      | app _ _ => simp only [etaContract] at h; contradiction
  | bvar _ => simp only [etaContract] at h; contradiction
  | port _ => simp only [etaContract] at h; contradiction
  | lam _ => simp only [etaContract] at h; contradiction

theorem etaContract_complete (fn : Term n α) :
    etaContract (Term.app fn.lift (Term.bvar 0)) = some fn := by
  simp only [etaContract, Term.unlift_lift]
  rfl

inductive OneStep : Term n α → Term n α → Prop
  | beta : body.substBound (Fin.cases arg Term.bvar) = out →
      OneStep (Term.app (Term.lam body) arg) out
  | eta : etaContract body = some fn → OneStep (Term.lam body) fn
  | lam : OneStep a b → OneStep (Term.lam a) (Term.lam b)
  | appFn : OneStep a b → OneStep (Term.app a x) (Term.app b x)
  | appArg : OneStep a b → OneStep (Term.app x a) (Term.app x b)

inductive BetaEta : Term n α → Term n α → Prop
  | refl : BetaEta a a
  | step : OneStep a b → BetaEta a b
  | symm : BetaEta a b → BetaEta b a
  | trans : BetaEta a b → BetaEta b c → BetaEta a c

theorem betaEta_equivalence : Equivalence (@BetaEta n α) := by
  exact ⟨fun _ => .refl, .symm, .trans⟩

theorem BetaEta.lam {a b : Term (n + 1) α} (h : BetaEta a b) :
    BetaEta (Term.lam a) (Term.lam b) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (.lam h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BetaEta.appFn {a b : Term n α} (h : BetaEta a b) (x : Term n α) :
    BetaEta (Term.app a x) (Term.app b x) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (.appFn h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BetaEta.appArg {a b : Term n α} (h : BetaEta a b) (x : Term n α) :
    BetaEta (Term.app x a) (Term.app x b) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (.appArg h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BetaEta.app {fn fn' arg arg' : Term n α}
    (hfn : BetaEta fn fn') (harg : BetaEta arg arg') :
    BetaEta (Term.app fn arg) (Term.app fn' arg') :=
  (hfn.appFn arg).trans (harg.appArg fn')

-- Required transport and confluence statements are declared before proof work.
private theorem OneStep.renameBound {a b : Term n α} (h : OneStep a b)
    (ρ : Fin n → Fin m) : OneStep (a.renameBound ρ) (b.renameBound ρ) := by
  induction h generalizing m with
  | beta hred =>
      rename_i k γ out body arg
      let θ : Fin (k + 1) → Term k γ := Fin.cases arg Term.bvar
      simp only [Term.renameBound]
      apply OneStep.beta
      calc
        _ = _ := Term.substBound_renameBound _ _ _
        _ = Term.substBound
              (fun i => Term.renameBound ρ (θ i)) body := by
            apply congrArg (fun s => Term.substBound s body)
            funext i
            refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
        _ = Term.renameBound ρ (Term.substBound θ body) :=
              (Term.renameBound_substBound _ _ _).symm
        _ = Term.renameBound ρ out := by
              apply congrArg (Term.renameBound ρ)
              exact hred
  | eta heta =>
      rename_i k γ body fn
      simp only [Term.renameBound]
      apply OneStep.eta
      rw [etaContract_sound heta]
      change etaContract (Term.app
        (fn.lift.renameBound (Fin.cases 0 (fun i => Fin.succ (ρ i))))
        (Term.bvar 0)) = some (fn.renameBound ρ)
      rw [← Term.lift_renameBound]
      exact etaContract_complete _
  | lam _ ih => exact OneStep.lam (ih _)
  | appFn _ ih => exact OneStep.appFn (ih _)
  | appArg _ ih => exact OneStep.appArg (ih _)

theorem BetaEta.renameBound {a b : Term n α} (h : BetaEta a b)
    (ρ : Fin n → Fin m) : BetaEta (a.renameBound ρ) (b.renameBound ρ) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (h.renameBound ρ)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem OneStep.substBound {a b : Term n α} (h : OneStep a b)
    (σ : Fin n → Term m α) : OneStep (a.substBound σ) (b.substBound σ) := by
  induction h generalizing m with
  | beta hred =>
      rename_i k γ out body arg
      let lifted : Fin (k + 1) → Term (m + 1) γ :=
        Fin.cases (Term.bvar 0) (fun j => (σ j).lift)
      let contract : Fin (m + 1) → Term m γ :=
        Fin.cases (Term.substBound σ arg) Term.bvar
      let original : Fin (k + 1) → Term k γ := Fin.cases arg Term.bvar
      simp only [Term.substBound]
      apply OneStep.beta
      change (Term.substBound lifted body).substBound contract =
        Term.substBound σ out
      calc
        _ = Term.substBound (fun i =>
              Term.substBound contract (lifted i)) body :=
              Term.substBound_comp _ _ _
        _ = Term.substBound (fun i =>
              Term.substBound σ (original i)) body := by
            apply congrArg (fun s => Term.substBound s body)
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · calc
                (σ j).lift.substBound contract =
                    (σ j).substBound (contract ∘ Fin.succ) :=
                  Term.substBound_renameBound _ _ _
                _ = (σ j).substBound Term.bvar := by
                  apply congrArg (fun s => (σ j).substBound s)
                  funext q
                  rfl
                _ = σ j := Term.substBound_id _
        _ = Term.substBound σ (Term.substBound original body) :=
              (Term.substBound_comp _ _ _).symm
        _ = Term.substBound σ out := by
              apply congrArg (Term.substBound σ)
              exact hred
  | eta heta =>
      rename_i k γ body fn
      simp only [Term.substBound]
      apply OneStep.eta
      rw [etaContract_sound heta]
      change etaContract (Term.app
        (fn.lift.substBound
          (Fin.cases (Term.bvar 0) (fun i => (σ i).lift)))
        (Term.bvar 0)) = some (fn.substBound σ)
      rw [← Term.lift_substBound]
      exact etaContract_complete _
  | lam _ ih => exact OneStep.lam (ih _)
  | appFn _ ih => exact OneStep.appFn (ih _)
  | appArg _ ih => exact OneStep.appArg (ih _)

theorem BetaEta.substBound {a b : Term n α} (h : BetaEta a b)
    (σ : Fin n → Term m α) : BetaEta (a.substBound σ) (b.substBound σ) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (h.substBound σ)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem OneStep.bindFree {a b : Term n α} (h : OneStep a b)
    (σ : α → Term n β) : OneStep (a.bindFree σ) (b.bindFree σ) := by
  induction h with
  | beta hred =>
      rename_i k γ out body arg
      simp only [Term.bindFree]
      apply OneStep.beta
      calc
        _ = Term.bindFree σ (Term.substBound (Fin.cases arg Term.bvar) body) :=
              (Term.bindFree_substBound body arg σ).symm
        _ = Term.bindFree σ out := congrArg (Term.bindFree σ) hred
  | eta heta =>
      rename_i k γ body fn
      simp only [Term.bindFree]
      apply OneStep.eta
      rw [etaContract_sound heta]
      change etaContract (Term.app
        (fn.lift.bindFree (fun x => (σ x).lift)) (Term.bvar 0)) =
          some (fn.bindFree σ)
      rw [show fn.lift.bindFree (fun x => (σ x).lift) =
          (fn.bindFree σ).lift by
        exact (Term.renameBound_bindFree fn σ Fin.succ).symm]
      exact etaContract_complete _
  | lam _ ih => exact OneStep.lam (ih (fun x => (σ x).lift))
  | appFn _ ih => exact OneStep.appFn (ih σ)
  | appArg _ ih => exact OneStep.appArg (ih σ)

theorem BetaEta.bindFree {a b : Term n α} (h : BetaEta a b)
    (σ : α → Term n β) : BetaEta (a.bindFree σ) (b.bindFree σ) := by
  induction h with
  | refl => exact .refl
  | step h => exact .step (h.bindFree σ)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

inductive Reduces : Term n α → Term n α → Prop
  | refl : Reduces a a
  | tail : Reduces a b → OneStep b c → Reduces a c

inductive Parallel : Term n α → Term n α → Prop
  | bvar : Parallel (Term.bvar i) (Term.bvar i)
  | port : Parallel (Term.port x) (Term.port x)
  | lam : Parallel a b → Parallel (Term.lam a) (Term.lam b)
  | app : Parallel fn fn' → Parallel arg arg' →
      Parallel (Term.app fn arg) (Term.app fn' arg')
  | beta : Parallel body body' → Parallel arg arg' →
      Parallel (Term.app (Term.lam body) arg)
        (body'.substBound (Fin.cases arg' Term.bvar))
  | eta : Parallel fn fn' →
      Parallel (Term.lam (Term.app fn.lift (Term.bvar 0))) fn'

theorem Parallel.refl (t : Term n α) : Parallel t t := by
  induction t with
  | bvar _ => exact .bvar
  | port _ => exact .port
  | lam _ ih => exact .lam ih
  | app _ _ ihFn ihArg => exact .app ihFn ihArg

private theorem Parallel.renameBound {a b : Term n α} (h : Parallel a b)
    (ρ : Fin n → Fin m) : Parallel (a.renameBound ρ) (b.renameBound ρ) := by
  induction h generalizing m with
  | bvar => exact .bvar
  | port => exact .port
  | lam _ ih => exact .lam (ih _)
  | app _ _ ihFn ihArg => exact .app (ihFn _) (ihArg _)
  | @beta q γ body body' arg arg' hBody hArg ihBody ihArg =>
      let original : Fin (q + 1) → Term q γ := Fin.cases arg' Term.bvar
      have ht : (body'.substBound original).renameBound ρ =
          (body'.renameBound (Fin.cases 0 (fun i => Fin.succ (ρ i)))).substBound
            (Fin.cases (arg'.renameBound ρ) Term.bvar) := by
        calc
          _ = body'.substBound (fun i =>
              (original i).renameBound ρ) :=
            Term.renameBound_substBound _ _ _
          _ = _ := by
            rw [Term.substBound_renameBound]
            apply congrArg (fun s => body'.substBound s)
            funext i
            refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
      simp only [Term.renameBound]
      rw [ht]
      exact Parallel.beta (ihBody _) (ihArg _)
  | @eta q γ fn fn' hfn ih =>
      simp only [Term.renameBound]
      change Parallel (Term.lam (Term.app
        (fn.lift.renameBound (Fin.cases 0 (fun i => Fin.succ (ρ i))))
        (Term.bvar 0))) (fn'.renameBound ρ)
      rw [← Term.lift_renameBound]
      exact .eta (ih _)

private theorem Parallel.substBound_env {a b : Term n α} (h : Parallel a b)
    {σ τ : Fin n → Term m α}
    (hστ : ∀ i, Parallel (σ i) (τ i)) :
    Parallel (a.substBound σ) (b.substBound τ) := by
  induction h generalizing m with
  | bvar => exact hστ _
  | port => exact .port
  | lam _ ih =>
      apply Parallel.lam
      apply ih
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .bvar
      · exact (hστ j).renameBound Fin.succ
  | app _ _ ihFn ihArg => exact .app (ihFn hστ) (ihArg hστ)
  | @beta q γ body body' arg arg' hBody hArg ihBody ihArg =>
      let liftσ : Fin (q + 1) → Term (m + 1) γ :=
        Fin.cases (Term.bvar 0) (fun i => (σ i).lift)
      let liftτ : Fin (q + 1) → Term (m + 1) γ :=
        Fin.cases (Term.bvar 0) (fun i => (τ i).lift)
      have hlift : ∀ i, Parallel (liftσ i) (liftτ i) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact .bvar
        · exact (hστ j).renameBound Fin.succ
      have hbody := ihBody hlift
      have harg := ihArg hστ
      have hβ := Parallel.beta hbody harg
      let original : Fin (q + 1) → Term q γ := Fin.cases arg' Term.bvar
      let contract : Fin (m + 1) → Term m γ :=
        Fin.cases (arg'.substBound τ) Term.bvar
      have ht : (body'.substBound original).substBound τ =
          (body'.substBound liftτ).substBound
            contract := by
        calc
          _ = body'.substBound (fun i =>
              (original i).substBound τ) :=
            Term.substBound_comp _ _ _
          _ = body'.substBound (fun i =>
              (liftτ i).substBound contract) := by
            apply congrArg (fun s => body'.substBound s)
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · symm
              calc
                (τ j).lift.substBound contract =
                    (τ j).substBound (contract ∘ Fin.succ) :=
                  Term.substBound_renameBound _ _ _
                _ = (τ j).substBound Term.bvar := by
                  apply congrArg (fun s => (τ j).substBound s)
                  funext r
                  rfl
                _ = τ j := Term.substBound_id _
          _ = _ := (Term.substBound_comp _ _ _).symm
      change Parallel
        (Term.app (Term.lam (body.substBound liftσ)) (arg.substBound σ))
        ((body'.substBound original).substBound τ)
      rw [ht]
      exact hβ
  | @eta q γ fn fn' hfn ih =>
      have hfn := ih hστ
      simp only [Term.substBound]
      change Parallel (Term.lam (Term.app
        (fn.lift.substBound
          (Fin.cases (Term.bvar 0) (fun i => (σ i).lift))) (Term.bvar 0)))
        (fn'.substBound τ)
      rw [← Term.lift_substBound]
      exact .eta hfn

theorem Parallel.betaSubst
    (hbody : Parallel body body') (harg : Parallel arg arg') :
    Parallel (body.substBound (Fin.cases arg Term.bvar))
      (body'.substBound (Fin.cases arg' Term.bvar)) := by
  apply hbody.substBound_env
  intro i
  refine Fin.cases harg (fun _ => Parallel.bvar) i

end VisualProof.Lambda
