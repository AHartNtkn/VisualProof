import VisualProof.Lambda.Substitute

namespace VisualProof.Lambda

private def dropZero : Fin (n + 1) → Option (Term n α) :=
  Fin.cases none (fun i => some (Term.bvar i))

def Term.unlift (t : Term (n + 1) α) : Option (Term n α) :=
  t.substBoundOption dropZero

theorem Term.unlift_lift (t : Term n α) : t.lift.unlift = some t := by
  apply Term.substBoundOption_rename_leftInverse
  intro i
  rfl

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

theorem Term.unlift_renameBound (t : Term (n + 1) α)
    (ρ : Fin n → Fin m) :
    (t.renameBound (Fin.cases 0 (fun i => Fin.succ (ρ i)))).unlift =
      t.unlift.map (Term.renameBound ρ) := by
  simp only [Term.unlift, Term.substBoundOption_renameBound,
    Term.renameBound_substBoundOption]
  apply congrArg (fun s => Term.substBoundOption s t)
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

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

-- Reduction owns transport through term operations; substitution algebra stays in its defining modules.
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

/-- Lambda congruence reflects beta-eta equivalence. Applying both renamed
abstractions to the same fresh bound variable beta-reduces to their bodies. -/
theorem BetaEta.lam_cancel {a b : Term (n + 1) α}
    (h : BetaEta (Term.lam a) (Term.lam b)) : BetaEta a b := by
  have congruent := (h.renameBound Fin.succ).appFn (Term.bvar 0)
  have left : BetaEta
      (Term.app ((Term.lam a).renameBound Fin.succ) (Term.bvar 0)) a := by
    apply BetaEta.step
    apply OneStep.beta
    rw [Term.substBound_renameBound]
    calc
      _ = a.substBound Term.bvar := by
        apply congrArg (fun substitution => a.substBound substitution)
        funext index
        refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
      _ = a := Term.substBound_id a
  have right : BetaEta
      (Term.app ((Term.lam b).renameBound Fin.succ) (Term.bvar 0)) b := by
    apply BetaEta.step
    apply OneStep.beta
    rw [Term.substBound_renameBound]
    calc
      _ = b.substBound Term.bvar := by
        apply congrArg (fun substitution => b.substBound substitution)
        funext index
        refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
      _ = b := Term.substBound_id b
  exact left.symm.trans (congruent.trans right)

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

theorem BetaEta.mapFree {a b : Term n α} (h : BetaEta a b)
    (rename : α → β) : BetaEta (a.mapFree rename) (b.mapFree rename) := by
  rw [Term.mapFree_eq_bindFree_ports, Term.mapFree_eq_bindFree_ports]
  exact h.bindFree (fun value => Term.port (rename value))

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

private theorem liftRenaming_injective (ρ : Fin n → Fin m)
    (hρ : Function.Injective ρ) :
    Function.Injective (Fin.cases 0 (fun i => Fin.succ (ρ i))) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i <;> intro j
  · refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · rfl
    · exfalso
      have hv : 0 = (ρ j).val + 1 := congrArg Fin.val hij
      omega
  · refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · exfalso
      have hv : (ρ i).val + 1 = 0 := congrArg Fin.val hij
      omega
    · have hv : (ρ i).val + 1 = (ρ j).val + 1 :=
        congrArg Fin.val hij
      apply congrArg Fin.succ
      apply hρ
      apply Fin.ext
      exact Nat.succ.inj hv

private theorem finSucc_injective : Function.Injective (@Fin.succ n) := by
  intro i j hij
  apply Fin.ext
  exact Nat.succ.inj (congrArg Fin.val hij)

private theorem Parallel.renameBound_reflect
    {a : Term n α} {b : Term m α} (ρ : Fin n → Fin m)
    (hρ : Function.Injective ρ) (h : Parallel (a.renameBound ρ) b) :
    ∃ b₀, b = b₀.renameBound ρ ∧ Parallel a b₀ := by
  generalize hs : a.renameBound ρ = source at h
  induction h generalizing n with
  | bvar =>
      cases a with
      | bvar i =>
          simp only [Term.renameBound] at hs
          cases hs
          exact ⟨Term.bvar i, rfl, .bvar⟩
      | port _ => cases hs
      | lam _ => cases hs
      | app _ _ => cases hs
  | port =>
      cases a with
      | bvar _ => cases hs
      | port x =>
          simp only [Term.renameBound] at hs
          cases hs
          exact ⟨Term.port _, rfl, .port⟩
      | lam _ => cases hs
      | app _ _ => cases hs
  | lam hbody ih =>
      cases a with
      | bvar _ => cases hs
      | port _ => cases hs
      | lam body =>
          simp only [Term.renameBound] at hs
          cases hs
          obtain ⟨body₀, hbody₀, hparallel⟩ :=
            ih (Fin.cases 0 (fun i => Fin.succ (ρ i)))
              (liftRenaming_injective ρ hρ) rfl
          exact ⟨Term.lam body₀, congrArg Term.lam hbody₀, .lam hparallel⟩
      | app _ _ => cases hs
  | app hfn harg ihFn ihArg =>
      cases a with
      | bvar _ => cases hs
      | port _ => cases hs
      | lam _ => cases hs
      | app fn arg =>
          simp only [Term.renameBound] at hs
          cases hs
          obtain ⟨fn₀, hfn₀, hpfn⟩ := ihFn ρ hρ rfl
          obtain ⟨arg₀, harg₀, hparg⟩ := ihArg ρ hρ rfl
          refine ⟨Term.app fn₀ arg₀, ?_, .app hpfn hparg⟩
          rw [hfn₀, harg₀]
          rfl
  | beta hbody harg ihBody ihArg =>
      cases a with
      | bvar _ => cases hs
      | port _ => cases hs
      | lam _ => cases hs
      | app fn arg =>
          cases fn with
          | bvar _ => cases hs
          | port _ => cases hs
          | app _ _ => cases hs
          | lam body =>
              simp only [Term.renameBound] at hs
              cases hs
              obtain ⟨body₀, hbody₀, hpbody⟩ :=
                ihBody (Fin.cases 0 (fun i => Fin.succ (ρ i)))
                  (liftRenaming_injective ρ hρ) rfl
              obtain ⟨arg₀, harg₀, hparg⟩ := ihArg ρ hρ rfl
              let original : Fin (n + 1) → Term n _ :=
                Fin.cases arg₀ Term.bvar
              let contract : Fin (_ + 1) → Term _ _ :=
                Fin.cases (arg₀.renameBound ρ) Term.bvar
              refine ⟨body₀.substBound original, ?_,
                Parallel.beta hpbody hparg⟩
              rw [hbody₀, harg₀]
              calc
                _ = body₀.substBound (contract ∘
                      Fin.cases 0 (fun i => Fin.succ (ρ i))) :=
                    Term.substBound_renameBound _ _ _
                _ = body₀.substBound
                      (fun i => (original i).renameBound ρ) := by
                    apply congrArg (fun s => body₀.substBound s)
                    funext i
                    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
                _ = _ := (Term.renameBound_substBound _ _ _).symm
  | @eta q γ fn fn' hfn ih =>
      cases a with
      | bvar _ => cases hs
      | port _ => cases hs
      | app _ _ => cases hs
      | lam body =>
          cases body with
          | bvar _ => cases hs
          | port _ => cases hs
          | lam _ => cases hs
          | app candidate arg =>
              simp only [Term.renameBound] at hs
              injection hs with _ hsBody
              injection hsBody with _ hsCandidate hsArg
              cases arg with
              | port _ => cases hsArg
              | lam _ => cases hsArg
              | app _ _ => cases hsArg
              | bvar i =>
                  injection hsArg with _ hsIndex
                  have hi : i = 0 :=
                    (liftRenaming_injective ρ hρ) hsIndex
                  subst i
                  have hu := congrArg Term.unlift hsCandidate
                  change (Term.renameBound
                    (Fin.cases 0 (fun i => Fin.succ (ρ i))) candidate).unlift =
                      fn.lift.unlift at hu
                  rw [Term.unlift_renameBound, Term.unlift_lift] at hu
                  obtain ⟨core, hcore, hrenamed⟩ :=
                    Option.map_eq_some_iff.mp hu
                  rw [Term.unlift_sound hcore]
                  obtain ⟨fn₀, hfn₀, hpfn⟩ := ih ρ hρ hrenamed
                  exact ⟨fn₀, hfn₀, Parallel.eta hpfn⟩

theorem Parallel.lift_reflect {a : Term n α} {b : Term (n + 1) α}
    (h : Parallel a.lift b) :
    ∃ b₀, b = b₀.lift ∧ Parallel a b₀ := by
  apply Parallel.renameBound_reflect Fin.succ
  · intro i j hij
    apply Fin.ext
    exact Nat.succ.inj (congrArg Fin.val hij)
  · exact h

def Term.nodeCount : Term n α → Nat
  | .bvar _ => 1
  | .port _ => 1
  | .lam body => body.nodeCount + 1
  | .app fn arg => fn.nodeCount + arg.nodeCount + 1

private theorem Term.nodeCount_renameBound (t : Term n α)
    (ρ : Fin n → Fin m) : (t.renameBound ρ).nodeCount = t.nodeCount := by
  induction t generalizing m with
  | bvar _ => rfl
  | port _ => rfl
  | lam _ ih => simp only [Term.renameBound, Term.nodeCount, ih]
  | app _ _ ihFn ihArg =>
      simp only [Term.renameBound, Term.nodeCount, ihFn, ihArg]

private theorem etaContract_nodeCount_lt {body : Term (n + 1) α}
    {fn : Term n α} (h : etaContract body = some fn) :
    fn.nodeCount < (Term.lam body).nodeCount := by
  rw [etaContract_sound h]
  simp only [Term.nodeCount, Term.nodeCount_renameBound, Term.lift]
  omega

set_option linter.unusedVariables false in
def Term.completeDevelopment (t : Term n α) : Term n α :=
  match t with
  | .bvar i => .bvar i
  | .port x => .port x
  | .app (.lam body) arg =>
      (completeDevelopment body).substBound
        (Fin.cases (completeDevelopment arg) Term.bvar)
  | .app fn arg => .app (completeDevelopment fn) (completeDevelopment arg)
  | .lam body =>
      match h : etaContract body with
      | some fn => completeDevelopment fn
      | none => .lam (completeDevelopment body)
termination_by t.nodeCount
decreasing_by
  all_goals simp_all [Term.nodeCount]
  all_goals try omega
  all_goals exact etaContract_nodeCount_lt h

theorem parallel_app_beta_peak
    (completeBody : ∀ {body'}, Parallel body body' →
      Parallel body' body.completeDevelopment)
    (completeArg : ∀ {arg'}, Parallel arg arg' →
      Parallel arg' arg.completeDevelopment)
    (hfn : Parallel (Term.lam body) fn')
    (harg : Parallel arg arg') :
    Parallel (Term.app fn' arg')
      (body.completeDevelopment.substBound
        (Fin.cases arg.completeDevelopment Term.bvar)) := by
  cases hfn with
  | lam hbody => exact Parallel.beta (completeBody hbody) (completeArg harg)
  | eta hcore =>
      have hcanonical := Parallel.app
        (hcore.renameBound Fin.succ) (Parallel.bvar (i := 0))
      have hbody := completeBody hcanonical
      have hresult := Parallel.betaSubst hbody (completeArg harg)
      simp only [Term.substBound_app, Term.substBound_bvar,
        Term.substBound_renameBound, Term.lift] at hresult
      rw [show (fun i => Fin.cases arg' Term.bvar i) ∘ Fin.succ =
          Term.bvar by
        funext i
        rfl, Term.substBound_id] at hresult
      exact hresult

theorem parallel_lam_eta_peak {n : Nat} {α : Type u}
    {fn : Term n α} {body' : Term (n + 1) α}
    (completeFn : ∀ {fn'}, Parallel fn fn' →
      Parallel fn' fn.completeDevelopment)
    (hbody : Parallel (Term.app fn.lift (Term.bvar 0)) body') :
    Parallel (Term.lam body') fn.completeDevelopment := by
  generalize hs : Term.app fn.lift (Term.bvar 0) = source at hbody
  cases hbody with
  | bvar => cases hs
  | port => cases hs
  | lam _ => cases hs
  | eta _ => cases hs
  | app hfn harg =>
      injection hs with _ hsFn hsArg
      cases hsFn
      cases hsArg
      cases harg
      obtain ⟨fn₀, rfl, hpfn⟩ := hfn.lift_reflect
      exact Parallel.eta (completeFn hpfn)
  | beta hbody harg =>
      cases fn with
      | bvar _ => cases hs
      | port _ => cases hs
      | app _ _ => cases hs
      | lam core =>
          simp only [Term.lift, Term.renameBound] at hs
          injection hs with _ hsFn hsArg
          injection hsFn with _ hsBody
          cases hsArg
          cases harg
          let insert : Fin (n + 1) → Fin (n + 2) :=
            Fin.cases 0 (fun i => Fin.succ (Fin.succ i))
          change Term.renameBound insert core = _ at hsBody
          rw [← hsBody] at hbody
          have hinsert : Function.Injective insert :=
            liftRenaming_injective (Fin.succ : Fin n → Fin (n + 1))
              finSucc_injective
          obtain ⟨core', hcore', hparallel⟩ :=
            hbody.renameBound_reflect insert hinsert
          rw [hcore']
          have hcancel :
              (Term.renameBound insert core').substBound
                (Fin.cases (Term.bvar 0) Term.bvar) = core' := by
            rw [Term.substBound_renameBound]
            calc
              _ = core'.substBound Term.bvar := by
                apply congrArg (fun s => core'.substBound s)
                funext i
                refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
              _ = core' := Term.substBound_id _
          rw [hcancel]
          exact completeFn (Parallel.lam hparallel)

theorem Parallel.to_completeDevelopment {a b : Term n α}
    (h : Parallel a b) : Parallel b a.completeDevelopment := by
  apply Term.completeDevelopment.induct
    (motive := fun _ a => ∀ {b}, Parallel a b →
      Parallel b a.completeDevelopment)
  · intro _ _ _ hb
    cases hb
    simpa only [Term.completeDevelopment] using (Parallel.bvar (i := _))
  · intro _ _ _ hb
    cases hb
    simpa only [Term.completeDevelopment] using (Parallel.port (x := _))
  · intro _ body arg completeArg completeBody _ hb
    cases hb with
    | app hfn harg =>
        simpa only [Term.completeDevelopment] using
          parallel_app_beta_peak completeBody completeArg hfn harg
    | beta hbody harg =>
        simpa only [Term.completeDevelopment] using
          Parallel.betaSubst (completeBody hbody) (completeArg harg)
  · intro _ fn arg hnotLam completeFn completeArg _ hb
    cases hb with
    | app hfn harg =>
        simpa only [Term.completeDevelopment] using
          Parallel.app (completeFn hfn) (completeArg harg)
    | beta _ _ => exact (hnotLam _ rfl).elim
  · intro _ body fn heta completeFn _ hb
    have hdevelopment :
        (Term.lam body).completeDevelopment = fn.completeDevelopment := by
      rw [Term.completeDevelopment, heta]
    rw [hdevelopment]
    cases hb with
    | lam hbody =>
        rw [etaContract_sound heta] at hbody
        exact parallel_lam_eta_peak completeFn hbody
    | eta hfn =>
        rw [etaContract_complete] at heta
        cases heta
        exact completeFn hfn
  · intro _ body heta completeBody _ hb
    have hdevelopment :
        (Term.lam body).completeDevelopment =
          Term.lam body.completeDevelopment := by
      rw [Term.completeDevelopment, heta]
    rw [hdevelopment]
    cases hb with
    | lam hbody =>
        exact Parallel.lam (completeBody hbody)
    | eta _ =>
        rw [etaContract_complete] at heta
        contradiction
  · exact h

theorem parallel_diamond {a b c : Term n α}
    (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d :=
  ⟨a.completeDevelopment, hab.to_completeDevelopment,
    hac.to_completeDevelopment⟩

theorem OneStep.toParallel {a b : Term n α} (h : OneStep a b) :
    Parallel a b := by
  induction h with
  | beta hred =>
      rw [← hred]
      exact Parallel.beta (Parallel.refl _) (Parallel.refl _)
  | eta heta =>
      rw [etaContract_sound heta]
      exact Parallel.eta (Parallel.refl _)
  | lam _ ih => exact Parallel.lam ih
  | appFn _ ih => exact Parallel.app ih (Parallel.refl _)
  | appArg _ ih => exact Parallel.app (Parallel.refl _) ih

theorem Reduces.trans {a b c : Term n α}
    (hab : Reduces a b) (hbc : Reduces b c) : Reduces a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

theorem Reduces.lam {a b : Term (n + 1) α} (h : Reduces a b) :
    Reduces (Term.lam a) (Term.lam b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (.lam hstep)

theorem Reduces.appFn {a b x : Term n α} (h : Reduces a b) :
    Reduces (Term.app a x) (Term.app b x) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (.appFn hstep)

theorem Reduces.appArg {a b x : Term n α} (h : Reduces a b) :
    Reduces (Term.app x a) (Term.app x b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (.appArg hstep)

theorem Reduces.app {fn fn' arg arg' : Term n α}
    (hfn : Reduces fn fn') (harg : Reduces arg arg') :
    Reduces (Term.app fn arg) (Term.app fn' arg') :=
  (hfn.appFn).trans harg.appArg

private theorem Reduces.renameBound {a b : Term n α} (h : Reduces a b)
    (ρ : Fin n → Fin m) :
    Reduces (a.renameBound ρ) (b.renameBound ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (hstep.renameBound ρ)

theorem Parallel.toReduces {a b : Term n α} (h : Parallel a b) :
    Reduces a b := by
  induction h with
  | bvar => exact .refl
  | port => exact .refl
  | lam _ ih => exact ih.lam
  | app _ _ ihFn ihArg => exact ihFn.app ihArg
  | beta _ _ ihBody ihArg =>
      exact (ihBody.lam.app ihArg).tail (.beta rfl)
  | eta _ ih =>
      have hbody := (ih.renameBound Fin.succ).app (Reduces.refl (a := Term.bvar 0))
      exact hbody.lam.tail (.eta (etaContract_complete _))

theorem reduces_parallel_strip {a b c : Term n α}
    (hab : Reduces a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Reduces c d := by
  induction hab generalizing c with
  | refl => exact ⟨c, hac, .refl⟩
  | tail hab hstep ih =>
      obtain ⟨x, hbx, hcx⟩ := ih hac
      obtain ⟨d, hxd, hbd⟩ := parallel_diamond hbx hstep.toParallel
      exact ⟨d, hbd, hcx.trans hxd.toReduces⟩

theorem reduces_confluent {a b c : Term n α}
    (hab : Reduces a b) (hac : Reduces a c) :
    ∃ d, Reduces b d ∧ Reduces c d := by
  induction hac with
  | refl => exact ⟨b, .refl, hab⟩
  | tail hac hstep ih =>
      obtain ⟨x, hbx, hcx⟩ := ih
      obtain ⟨d, hxd, hcd⟩ := reduces_parallel_strip hcx hstep.toParallel
      exact ⟨d, hbx.trans hxd.toReduces, hcd⟩

theorem churchRosser {a b : Term n α} (h : BetaEta a b) :
    ∃ c, Reduces a c ∧ Reduces b c := by
  induction h with
  | refl => exact ⟨_, .refl, .refl⟩
  | step hstep => exact ⟨_, .tail .refl hstep, .refl⟩
  | symm _ ih =>
      obtain ⟨c, hac, hbc⟩ := ih
      exact ⟨c, hbc, hac⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨x, hax, hbx⟩ := ih₁
      obtain ⟨y, hby, hcy⟩ := ih₂
      obtain ⟨z, hxz, hyz⟩ := reduces_confluent hbx hby
      exact ⟨z, hax.trans hxz, hcy.trans hyz⟩

inductive Head (n binders : Nat) (α : Type u) where
  | bound : Fin binders → Head n binders α
  | outer : Fin n → Head n binders α
  | port : α → Head n binders α

inductive Head.Corresponds : Head n k α → Head n l α → Prop
  | bound (i : Nat) (hi : i < k) (hj : i < l) :
      Corresponds (.bound ⟨i, hi⟩) (.bound ⟨i, hj⟩)
  | outer (i : Fin n) : Corresponds (.outer i) (.outer i)
  | port (x : α) : Corresponds (.port x) (.port x)

private def extendScope (n : Nat) : Nat → Nat
  | 0 => n
  | binders + 1 => extendScope (n + 1) binders

private theorem extendScope_eq (n binders : Nat) :
    extendScope n binders = n + binders := by
  induction binders generalizing n with
  | zero => rfl
  | succ binders ih => simp only [extendScope, ih]; omega

structure HeadSpine (n : Nat) (α : Type u) where
  binders : Nat
  head : Head n binders α
  args : List (Term (extendScope n binders) α)

def Head.mapFree (rename : α → β) : Head n binders α → Head n binders β
  | Head.bound index => Head.bound index
  | Head.outer index => Head.outer index
  | Head.port value => Head.port (rename value)

def HeadSpine.mapFree (rename : α → β)
    (spine : HeadSpine n α) : HeadSpine n β where
  binders := spine.binders
  head := spine.head.mapFree rename
  args := spine.args.map (Term.mapFree rename)

private structure PrefixBody (n : Nat) (α : Type u) where
  binders : Nat
  body : Term (extendScope n binders) α

private def peelPrefix : (t : Term n α) → PrefixBody n α
  | .lam body =>
      let peeled := peelPrefix body
      { binders := peeled.binders + 1
        body := peeled.body }
  | t => { binders := 0, body := t }

private inductive RawHead (n : Nat) (α : Type u) where
  | bvar : Fin n → RawHead n α
  | port : α → RawHead n α

private structure RawSpine (n : Nat) (α : Type u) where
  head : RawHead n α
  args : List (Term n α)

private def rawSpine : Term n α → Option (RawSpine n α)
  | .bvar i => some { head := .bvar i, args := [] }
  | .port x => some { head := .port x, args := [] }
  | .lam _ => none
  | .app fn arg =>
      (rawSpine fn).map fun spine =>
        { spine with args := spine.args ++ [arg] }

private def classifyHead (binders : Nat) :
    RawHead (extendScope n binders) α → Head n binders α
  | .port x => .port x
  | .bvar i =>
      if h : i.val < binders then
        .bound ⟨binders - 1 - i.val, by omega⟩
      else
        .outer ⟨i.val - binders, by
          have hi : i.val < n + binders := by
            simpa only [extendScope_eq] using i.isLt
          omega⟩

def headSpine (t : Term n α) : Option (HeadSpine n α) :=
  let peeled := peelPrefix t
  (rawSpine peeled.body).map fun spine =>
    { binders := peeled.binders
      head := classifyHead peeled.binders spine.head
      args := spine.args }

def prefixClose : (binders : Nat) → Term (extendScope n binders) α → Term n α
  | 0, t => t
  | binders + 1, t =>
      Term.lam (prefixClose binders t)

private def Head.toTerm : Head n binders α → Term (extendScope n binders) α
  | .bound i => .bvar ⟨binders - 1 - i.val, by
      rw [extendScope_eq]
      omega⟩
  | .outer i => .bvar ⟨binders + i.val, by
      rw [extendScope_eq]
      omega⟩
  | .port x => .port x

private def RawHead.toTerm : RawHead n α → Term n α
  | .bvar i => .bvar i
  | .port x => .port x

private def Head.toRaw : Head n binders α →
    RawHead (extendScope n binders) α
  | .bound i => .bvar ⟨binders - 1 - i.val, by
      rw [extendScope_eq]
      omega⟩
  | .outer i => .bvar ⟨binders + i.val, by
      rw [extendScope_eq]
      omega⟩
  | .port x => .port x

private theorem Head.toRaw_toTerm (head : Head n binders α) :
    head.toRaw.toTerm = head.toTerm := by
  cases head <;> rfl

private theorem classifyHead_toRaw (head : Head n binders α) :
    classifyHead binders head.toRaw = head := by
  cases head with
  | port x => rfl
  | bound i =>
      have hi := i.isLt
      simp only [Head.toRaw, classifyHead]
      split
      next h =>
        apply congrArg Head.bound
        apply Fin.ext
        change binders - 1 - (binders - 1 - i.val) = i.val
        omega
      next h => omega
  | outer i =>
      have hi := i.isLt
      simp only [Head.toRaw, classifyHead]
      split
      next h => omega
      next h =>
        apply congrArg Head.outer
        apply Fin.ext
        change binders + i.val - binders = i.val
        omega

private def applyArgs (fn : Term n α) : List (Term n α) → Term n α
  | [] => fn
  | arg :: args => applyArgs (Term.app fn arg) args

private def HeadSpine.toTerm (spine : HeadSpine n α) : Term n α :=
  prefixClose spine.binders (applyArgs spine.head.toTerm spine.args)

private theorem applyArgs_append (fn : Term n α)
    (xs ys : List (Term n α)) :
    applyArgs fn (xs ++ ys) = applyArgs (applyArgs fn xs) ys := by
  induction xs generalizing fn with
  | nil => rfl
  | cons x xs ih => exact ih (Term.app fn x)

private theorem BetaEta.applyArgs {fn fn' : Term n α}
    (h : BetaEta fn fn') (args : List (Term n α)) :
    BetaEta (applyArgs fn args) (applyArgs fn' args) := by
  induction args generalizing fn fn' with
  | nil => exact h
  | cons argument arguments ih =>
      exact ih (h.appFn argument)

private theorem lift_substBound_closed (term argument : Term 0 α) :
    term.lift.substBound (Fin.cases argument Term.bvar) = term := by
  calc
    _ = term.substBound ((Fin.cases argument Term.bvar) ∘ Fin.succ) :=
      Term.substBound_renameBound term Fin.succ _
    _ = term.substBound Term.bvar := by
      apply congrArg (fun environment => term.substBound environment)
      funext index
      exact Fin.elim0 index
    _ = term := Term.substBound_id term

private def reverseArgument (arguments : Fin ports → Term 0 α)
    (index : Fin ports) : Term 0 α :=
  arguments ⟨ports - 1 - index.val, by
    have hindex := index.isLt
    omega⟩

/-- Applying an abstracted positional body to its arguments beta-reduces to
simultaneous reverse-index substitution into the body. -/
private theorem abstractPorts_applyArgs
    (body : Term ports Empty) (arguments : Fin ports → Term 0 α) :
    BetaEta
      (applyArgs ((Term.abstractPorts ports body).mapFree Empty.elim)
        (List.ofFn arguments))
      ((body.mapFree Empty.elim).substBound (reverseArgument arguments)) := by
  induction ports with
  | zero =>
      simp only [Term.abstractPorts, List.ofFn_zero, applyArgs]
      rw [show reverseArgument arguments = Term.bvar by
        funext index
        exact Fin.elim0 index]
      rw [Term.substBound_id]
      exact .refl
  | succ ports ih =>
      rw [List.ofFn_succ_last, applyArgs_append]
      have hprefix := ih (Term.lam body)
        (fun index => arguments index.castSucc)
      have happ := hprefix.appFn (arguments (Fin.last ports))
      refine happ.trans ?_
      simp only [Term.mapFree, Term.substBound_lam]
      apply BetaEta.step
      apply OneStep.beta
      rw [Term.substBound_comp]
      apply congrArg (fun substitution =>
        Term.substBound substitution (body.mapFree Empty.elim))
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · simp only [Fin.cases_zero, reverseArgument, Term.substBound_bvar]
        apply congrArg arguments
        apply Fin.ext
        simp
      · simp only [Fin.cases_succ, reverseArgument]
        rw [lift_substBound_closed]
        apply congrArg arguments
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega

private def reopenClosedPort (bound ports : Nat) :
    Fin (ports + bound) → Term bound (Fin ports) := fun index =>
  if hbound : index.val < bound then
    Term.bvar ⟨index.val, hbound⟩
  else
    Term.port ⟨ports - 1 - (index.val - bound), by
      have hindex := index.isLt
      omega⟩

private theorem reopenClosedPort_succ (bound ports : Nat) :
    Fin.cases (Term.bvar 0)
        (fun index => (reopenClosedPort bound ports index).lift) =
      reopenClosedPort (bound + 1) ports := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · simp only [Fin.cases_zero, reopenClosedPort]
    split
    next _ => rfl
    next h => exact False.elim (h (Nat.zero_lt_succ bound))
  · simp only [Fin.cases_succ, reopenClosedPort]
    by_cases hbound : prior.val < bound
    · simp only [hbound, ↓reduceDIte, Term.lift, Term.renameBound]
      split
      next _ => apply congrArg Term.bvar; apply Fin.ext; rfl
      next h => exact False.elim (h (Nat.succ_lt_succ hbound))
    · simp only [hbound, ↓reduceDIte, Term.lift, Term.renameBound]
      split
      next h => exact False.elim (hbound (Nat.lt_of_succ_lt_succ h))
      next _ =>
        apply congrArg Term.port
        apply Fin.ext
        simp only [Fin.val_succ]
        omega

private theorem closeOverPortsBody_reopen
    (term : Term bound (Fin ports)) :
    (term.closeOverPortsBody.mapFree Empty.elim).substBound
      (reopenClosedPort bound ports) = term := by
  induction term with
  | bvar index =>
      simp only [Term.closeOverPortsBody, Term.mapFree, Term.substBound_bvar,
        reopenClosedPort]
      split
      next h => exact congrArg Term.bvar (Fin.ext rfl)
      next h => exact False.elim (h index.isLt)
  | port port =>
      simp only [Term.closeOverPortsBody, Term.mapFree, Term.substBound_bvar,
        reopenClosedPort]
      split
      next h => omega
      next h =>
        apply congrArg Term.port
        apply Fin.ext
        simp only
        omega
  | lam body ih =>
      rename_i currentBound
      simp only [Term.closeOverPortsBody, Term.mapFree, Term.substBound_lam]
      apply congrArg Term.lam
      have henvironment :
          (fun index => Fin.cases (Term.bvar 0)
            (fun prior => (reopenClosedPort currentBound ports prior).lift)
            index) = reopenClosedPort (currentBound + 1) ports := by
        funext index
        exact congrFun (reopenClosedPort_succ currentBound ports) index
      exact (congrArg (fun environment =>
        (Term.mapFree Empty.elim (Term.closeOverPortsBody body)).substBound
          environment)
        henvironment).trans ih
  | app fn argument ihFn ihArgument =>
      simp only [Term.closeOverPortsBody, Term.mapFree, Term.substBound_app,
        ihFn, ihArgument]

theorem closeOverPorts_applyPorts (term : Term 0 (Fin ports)) :
    BetaEta
      (applyArgs (term.closeOverPorts.mapFree Empty.elim)
        (List.ofFn fun port => Term.port port))
      term := by
  unfold Term.closeOverPorts
  have happ := abstractPorts_applyArgs
    (body := term.closeOverPortsBody)
    (arguments := fun port => Term.port port)
  refine happ.trans ?_
  rw [show reverseArgument (fun port => Term.port port) =
      reopenClosedPort 0 ports by
    funext index
    simp only [reverseArgument, reopenClosedPort]
    split
    next h => omega
    next _ => rfl]
  rw [closeOverPortsBody_reopen]
  exact .refl

/-- Closing positional ports reflects beta-eta equivalence. The proof maps the
closed relation to the positional free type, applies both sides to the same
ordered fresh ports, and cancels each closure by beta reduction. -/
theorem closeOverPorts_betaEta_cancel {left right : Term 0 (Fin ports)}
    (equivalent : BetaEta left.closeOverPorts right.closeOverPorts) :
    BetaEta left right := by
  have mapped := equivalent.mapFree (Empty.elim : Empty → Fin ports)
  let arguments : List (Term 0 (Fin ports)) :=
    List.ofFn fun port => Term.port port
  have applied := mapped.applyArgs arguments
  exact (closeOverPorts_applyPorts left).symm.trans
    (applied.trans (closeOverPorts_applyPorts right))

private theorem rawSpine_applyArgs_of
    {fn : Term n α} {spine : RawSpine n α}
    (hfn : rawSpine fn = some spine) (args : List (Term n α)) :
    rawSpine (applyArgs fn args) =
      some { head := spine.head, args := spine.args ++ args } := by
  induction args generalizing fn spine with
  | nil => simpa [applyArgs] using hfn
  | cons arg args ih =>
      have happ : rawSpine (Term.app fn arg) =
          some { head := spine.head, args := spine.args ++ [arg] } := by
        simp only [rawSpine, Option.map_eq_some_iff]
        exact ⟨spine, hfn, by simp⟩
      simpa only [applyArgs, List.append_assoc] using ih happ

private theorem rawSpine_applyArgs (head : RawHead n α)
    (args : List (Term n α)) :
    rawSpine (applyArgs head.toTerm args) =
      some { head := head, args := args } := by
  have := rawSpine_applyArgs_of
    (show rawSpine head.toTerm = some { head := head, args := [] } by
      cases head <;> rfl) args
  simpa using this

private theorem rawSpine_sound {t : Term n α} {spine : RawSpine n α}
    (h : rawSpine t = some spine) :
    t = applyArgs spine.head.toTerm spine.args := by
  induction t with
  | bvar i =>
      simp only [rawSpine, Option.some.injEq] at h
      subst spine
      rfl
  | port x =>
      simp only [rawSpine, Option.some.injEq] at h
      subst spine
      rfl
  | lam body => simp only [rawSpine] at h; contradiction
  | app fn arg ihFn _ =>
      simp only [rawSpine, Option.map_eq_some_iff] at h
      obtain ⟨fnSpine, hfn, rfl⟩ := h
      rw [ihFn hfn, applyArgs_append]
      rfl

private theorem classifyHead_toTerm (binders : Nat)
    (head : RawHead (extendScope n binders) α) :
    (classifyHead binders head).toTerm = head.toTerm := by
  cases head with
  | port x => rfl
  | bvar i =>
      simp only [classifyHead]
      split
      next h =>
        simp only [Head.toTerm, RawHead.toTerm]
        apply congrArg Term.bvar
        apply Fin.ext
        change binders - 1 - (binders - 1 - i.val) = i.val
        omega
      next h =>
        simp only [Head.toTerm, RawHead.toTerm]
        apply congrArg Term.bvar
        apply Fin.ext
        change binders + (i.val - binders) = i.val
        omega

private def Head.wrap : Head (n + 1) binders α → Head n (binders + 1) α
  | .bound i => .bound ⟨i.val + 1, by omega⟩
  | .outer i => Fin.cases (.bound ⟨0, by omega⟩) (fun j => .outer j) i
  | .port x => .port x

private def HeadSpine.wrap (spine : HeadSpine (n + 1) α) :
    HeadSpine n α where
  binders := spine.binders + 1
  head := spine.head.wrap
  args := spine.args

private theorem classifyHead_wrap (binders : Nat)
    (head : RawHead (extendScope (n + 1) binders) α) :
    classifyHead (n := n) (binders + 1) head =
      (classifyHead (n := n + 1) binders head).wrap := by
  cases head with
  | port x => rfl
  | bvar i =>
      simp only [classifyHead]
      split
      next hOuter =>
        split
        next hInner =>
          simp only [Head.wrap]
          apply congrArg Head.bound
          apply Fin.ext
          change binders + 1 - 1 - i.val = binders - 1 - i.val + 1
          omega
        next hInner =>
          have hi : i.val = binders := by omega
          have hj : (⟨i.val - binders, by omega⟩ : Fin (n + 1)) = 0 := by
            apply Fin.ext
            change i.val - binders = 0
            omega
          simp only [Head.wrap]
          rw [hj]
          apply congrArg Head.bound
          apply Fin.ext
          change binders + 1 - 1 - i.val = 0
          omega
      next hOuter =>
        split
        next hInner => omega
        next hInner =>
          have hiTotal : i.val < n + 1 + binders := by
            simpa only [extendScope_eq, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using i.isLt
          let j : Fin n := ⟨i.val - binders - 1, by omega⟩
          have hj : (⟨i.val - binders, by omega⟩ : Fin (n + 1)) =
              Fin.succ j := by
            apply Fin.ext
            dsimp [j]
            omega
          simp only [Head.wrap]
          rw [hj]
          apply congrArg Head.outer
          apply Fin.ext
          dsimp [j]
          omega

private theorem headSpine_lam (t : Term (n + 1) α) :
    headSpine (Term.lam t) = (headSpine t).map HeadSpine.wrap := by
  unfold headSpine
  simp only [peelPrefix, Option.map_map]
  apply congrArg (fun f :
      RawSpine (extendScope (n + 1) (peelPrefix t).binders) α →
        HeadSpine n α =>
    Option.map f (rawSpine (peelPrefix t).body))
  funext raw
  cases raw with
  | mk head args =>
      dsimp only [Function.comp_apply, HeadSpine.wrap]
      rw [classifyHead_wrap]

private theorem peelPrefix_sound (t : Term n α) :
    t = prefixClose (peelPrefix t).binders (peelPrefix t).body := by
  induction t with
  | bvar i => rfl
  | port x => rfl
  | app fn arg _ _ => rfl
  | lam body ih =>
      simp only [peelPrefix, prefixClose]
      congr 1

private theorem peelPrefix_prefixClose (binders : Nat)
    (body : Term (extendScope n binders) α)
    (hbody : rawSpine body ≠ none) :
    peelPrefix (prefixClose binders body) =
      { binders := binders, body := body } := by
  induction binders generalizing n with
  | zero =>
      simp only [prefixClose]
      cases body <;> simp_all [peelPrefix, rawSpine]
  | succ binders ih =>
      simp only [prefixClose, peelPrefix]
      rw [ih body hbody]

private theorem headSpine_toTerm (spine : HeadSpine n α) :
    headSpine spine.toTerm = some spine := by
  unfold HeadSpine.toTerm headSpine
  rw [peelPrefix_prefixClose spine.binders
    (applyArgs spine.head.toTerm spine.args) (by
      rw [← spine.head.toRaw_toTerm, rawSpine_applyArgs]
      simp)]
  dsimp only
  rw [← spine.head.toRaw_toTerm, rawSpine_applyArgs]
  simp only [Option.map_some]
  rw [classifyHead_toRaw]

private theorem headSpine_sound {t : Term n α} {spine : HeadSpine n α}
    (h : headSpine t = some spine) : t = spine.toTerm := by
  unfold headSpine at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨raw, hraw, hspine⟩ := h
  subst spine
  unfold HeadSpine.toTerm
  calc
    t = prefixClose (peelPrefix t).binders (peelPrefix t).body :=
      peelPrefix_sound t
    _ = prefixClose (peelPrefix t).binders
          (applyArgs raw.head.toTerm raw.args) := by
        rw [rawSpine_sound hraw]
    _ = prefixClose (peelPrefix t).binders
          (applyArgs (classifyHead (peelPrefix t).binders raw.head).toTerm
            raw.args) := by
        rw [classifyHead_toTerm]

private theorem applyArgs_mapFree (fn : Term n α)
    (args : List (Term n α)) (rename : α → β) :
    (applyArgs fn args).mapFree rename =
      applyArgs (fn.mapFree rename) (args.map (Term.mapFree rename)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons argument rest ih =>
      simpa only [applyArgs, Term.mapFree, List.map_cons] using
        ih (Term.app fn argument)

theorem prefixClose_mapFree (binders : Nat)
    (body : Term (extendScope n binders) α) (rename : α → β) :
    (prefixClose binders body).mapFree rename =
      prefixClose binders (body.mapFree rename) := by
  induction binders generalizing n with
  | zero => rfl
  | succ binders ih =>
      simp only [prefixClose, Term.mapFree]
      exact congrArg Term.lam (ih body)

private theorem Head.toTerm_mapFree (head : Head n binders α)
    (rename : α → β) :
    head.toTerm.mapFree rename = (head.mapFree rename).toTerm := by
  cases head <;> simp [Head.toTerm, Head.mapFree, Term.mapFree]

/-- Free-port renaming preserves the complete head-spine decomposition. -/
theorem headSpine_mapFree {term : Term n α} {spine : HeadSpine n α}
    (hspine : headSpine term = some spine) (rename : α → β) :
    headSpine (term.mapFree rename) = some (spine.mapFree rename) := by
  rw [headSpine_sound hspine, HeadSpine.toTerm, prefixClose_mapFree,
    applyArgs_mapFree, Head.toTerm_mapFree]
  exact headSpine_toTerm (spine.mapFree rename)

private def scopeEmbed (h : k ≤ K) :
    Fin (extendScope n k) → Fin (extendScope n K) :=
  fun i => ⟨K - k + i.val, by
    have hi : i.val < n + k := by
      simpa only [extendScope_eq] using i.isLt
    simpa only [extendScope_eq] using
      (show K - k + i.val < n + K by omega)⟩

private theorem scopeEmbed_refl :
    scopeEmbed (n := n) (k := k) (K := k) (Nat.le_refl k) = id := by
  funext i
  apply Fin.ext
  simp [scopeEmbed]

private theorem scopeEmbed_comp (h₁ : k ≤ K) (h₂ : K ≤ L) :
    scopeEmbed (n := n) h₂ ∘ scopeEmbed (n := n) h₁ =
      scopeEmbed (n := n) (Nat.le_trans h₁ h₂) := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, scopeEmbed, Fin.val_mk]
  omega

private theorem applyArgs_bindFree (fn : Term n α)
    (args : List (Term n α)) (substitution : α → Term n β) :
    (applyArgs fn args).bindFree substitution =
      applyArgs (fn.bindFree substitution)
        (args.map fun arg => arg.bindFree substitution) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg rest ih =>
      simpa only [applyArgs, Term.bindFree, List.map_cons] using
        ih (Term.app fn arg)

private theorem prefixClose_bindFree
    (binders : Nat) (body : Term (extendScope n binders) α)
    (substitution : α → Term n β) :
    (prefixClose binders body).bindFree substitution =
      prefixClose binders
        (body.bindFree fun x =>
          (substitution x).renameBound
            (scopeEmbed (n := n) (k := 0) (K := binders)
              (Nat.zero_le binders))) := by
  induction binders generalizing n with
  | zero =>
      simp only [prefixClose]
      apply congrArg (fun replacement => body.bindFree replacement)
      funext x
      rw [scopeEmbed_refl]
      exact (Term.renameBound_id (substitution x)).symm
  | succ binders ih =>
      simp only [prefixClose, Term.bindFree]
      rw [ih]
      apply congrArg Term.lam
      apply congrArg (prefixClose binders)
      apply congrArg (fun replacement => body.bindFree replacement)
      funext x
      unfold Term.lift
      calc
        _ = (substitution x).renameBound
            (scopeEmbed (n := n + 1) (k := 0) (K := binders)
              (Nat.zero_le binders) ∘ Fin.succ) :=
          Term.renameBound_comp (substitution x) Fin.succ
            (scopeEmbed (n := n + 1) (k := 0) (K := binders)
              (Nat.zero_le binders))
        _ = _ := by
          apply congrArg (fun rename => (substitution x).renameBound rename)
          funext index
          apply Fin.ext
          simp only [Function.comp_apply, scopeEmbed, Fin.val_mk, Fin.succ]
          omega

def Term.liftClosed (term : ClosedTerm) : Term n Empty :=
  term.renameBound Fin.elim0

private theorem prefixClose_bindFree_closed
    (binders : Nat) (body : Term (extendScope 0 binders) α)
    (substitution : α → ClosedTerm) :
    (prefixClose binders body).bindFree substitution =
      prefixClose binders
        (body.bindFree fun port => (substitution port).liftClosed) := by
  rw [prefixClose_bindFree]
  apply congrArg (prefixClose binders)
  apply congrArg (fun replacement => body.bindFree replacement)
  funext port
  apply congrArg (fun rename => (substitution port).renameBound rename)
  funext impossible
  exact Fin.elim0 impossible

/-- Substituting closed terms for free ports preserves an aligned bound rigid
head and maps the same substitution over every spine argument.  This is the
public bridge from canonical diagram evaluation to `rigidHead_args`. -/
theorem headSpine_bindFree_bound
    {term : Term 0 α} {spine : HeadSpine 0 α}
    (hspine : headSpine term = some spine)
    (headIndex : Fin spine.binders)
    (hhead : spine.head = .bound headIndex)
    (substitution : α → ClosedTerm) :
    headSpine (term.bindFree substitution) = some {
      binders := spine.binders
      head := .bound headIndex
      args := spine.args.map fun argument =>
        argument.bindFree fun port => (substitution port).liftClosed
    } := by
  let substituted : HeadSpine 0 Empty := {
    binders := spine.binders
    head := .bound headIndex
    args := spine.args.map fun argument =>
      argument.bindFree fun port => (substitution port).liftClosed
  }
  have hterm : term = spine.toTerm := headSpine_sound hspine
  rw [hterm, HeadSpine.toTerm, prefixClose_bindFree, applyArgs_bindFree]
  have hsubstitution :
      (fun port =>
        (substitution port).renameBound
          (scopeEmbed (n := 0) (k := 0) (K := spine.binders)
            (Nat.zero_le spine.binders))) =
        (fun port => (substitution port).liftClosed) := by
    funext port
    apply congrArg (fun rename => (substitution port).renameBound rename)
    funext impossible
    exact Fin.elim0 impossible
  rw [hsubstitution]
  have hbody :
      (spine.head.toTerm.bindFree fun port =>
          (substitution port).liftClosed) =
        (Head.bound headIndex : Head 0 spine.binders Empty).toTerm := by
    rw [hhead]
    rfl
  rw [hbody]
  exact headSpine_toTerm substituted

private def etaProjections (n K : Nat) :
    (d : Nat) → d ≤ K → List (Term (extendScope n K) α)
  | 0, _ => []
  | d + 1, hd =>
      Term.bvar ⟨d, by
        rw [extendScope_eq]
        omega⟩ :: etaProjections n K d (by omega)

private def etaEnvelopeArgs (K : Nat) (s : HeadSpine n α)
    (h : s.binders ≤ K) : List (Term (extendScope n K) α) :=
  s.args.map (Term.renameBound (scopeEmbed h)) ++
    etaProjections n K (K - s.binders) (Nat.sub_le _ _)

private theorem etaProjections_eq_of_d_eq (K : Nat)
    {d e : Nat} (hd : d ≤ K) (he : e ≤ K) (hde : d = e) :
    etaProjections (α := α) n K d hd = etaProjections n K e he := by
  subst e
  rfl

private theorem etaProjections_fusion_add (L d e : Nat) (hd : d ≤ L) :
    (etaProjections (α := α) n L d hd).map
        (Term.renameBound (scopeEmbed (n := n) (Nat.le_add_right L e))) ++
      etaProjections n (L + e) e (Nat.le_add_left e L) =
    etaProjections n (L + e) (e + d) (by omega) := by
  induction d with
  | zero => simp [etaProjections]
  | succ d ih =>
      simp only [etaProjections, List.map_cons, List.cons_append]
      congr 1
      · apply congrArg Term.bvar
        apply Fin.ext
        change L + e - L + d = e + (d + 1) - 1
        omega
      · exact ih (by omega)

private theorem etaProjections_fusion (b L K : Nat)
    (hb : b ≤ L) (hLK : L ≤ K) :
    (etaProjections (α := α) n L (L - b) (Nat.sub_le _ _)).map
        (Term.renameBound (scopeEmbed (n := n) hLK)) ++
      etaProjections n K (K - L) (Nat.sub_le _ _) =
    etaProjections n K (K - b) (Nat.sub_le _ _) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hLK
  have hf := etaProjections_fusion_add (α := α) (n := n)
    L (L - b) e (Nat.sub_le _ _)
  simp only [Nat.add_sub_cancel_left]
  calc
    _ = etaProjections n (L + e) (e + (L - b)) (by omega) := hf
    _ = _ := etaProjections_eq_of_d_eq (α := α) (n := n) (L + e)
      (by omega) (by omega) (by omega)

private theorem etaEnvelopeArgs_fusion (s : HeadSpine n α)
    (hsL : s.binders ≤ L) (hLK : L ≤ K) :
    (etaEnvelopeArgs L s hsL).map
        (Term.renameBound (scopeEmbed (n := n) hLK)) ++
      etaProjections n K (K - L) (Nat.sub_le _ _) =
    etaEnvelopeArgs K s (Nat.le_trans hsL hLK) := by
  simp only [etaEnvelopeArgs, List.map_append, List.map_map,
    List.append_assoc]
  rw [etaProjections_fusion (α := α) (n := n) s.binders L K hsL hLK]
  apply congrArg (fun xs => xs ++ etaProjections n K (K - s.binders)
    (Nat.sub_le _ _))
  apply List.map_congr_left
  intro t ht
  change (t.renameBound (scopeEmbed hsL)).renameBound (scopeEmbed hLK) = _
  rw [Term.renameBound_comp]
  apply congrArg (fun r => t.renameBound r)
  exact scopeEmbed_comp hsL hLK

private theorem etaEnvelopeArgs_identity (s : HeadSpine n α) :
    etaEnvelopeArgs s.binders s (Nat.le_refl _) = s.args := by
  simp only [etaEnvelopeArgs, Nat.sub_self, etaProjections, List.append_nil]
  rw [scopeEmbed_refl]
  induction s.args with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, Term.renameBound_id, ih]

private theorem etaProjections_wrap (K d : Nat) (hd : d ≤ K) :
    etaProjections (α := α) (n + 1) K d hd =
      etaProjections n (K + 1) d (by omega) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [etaProjections]
      congr 1
      exact ih (by omega)

private theorem etaEnvelopeArgs_wrap (s : HeadSpine (n + 1) α)
    (h : s.binders ≤ K) :
    etaEnvelopeArgs K s h =
      etaEnvelopeArgs (K + 1) s.wrap (by
        change s.binders + 1 ≤ K + 1
        omega) := by
  simp only [etaEnvelopeArgs, HeadSpine.wrap]
  have hd : K + 1 - (s.binders + 1) = K - s.binders := by omega
  rw [etaProjections_eq_of_d_eq (α := α) (n := n) (K + 1)
    (d := K + 1 - (s.binders + 1)) (e := K - s.binders)
    (Nat.sub_le _ _) (by omega) hd]
  rw [← etaProjections_wrap (α := α) (n := n) K (K - s.binders)
    (Nat.sub_le _ _)]
  apply congrArg (fun xs => xs ++
    etaProjections (α := α) (n + 1) K (K - s.binders) (Nat.sub_le _ _))
  apply List.map_congr_left
  intro t ht
  apply congrArg (fun r => t.renameBound r)
  funext i
  apply Fin.ext
  simp only [scopeEmbed, Fin.val_mk]
  omega

private theorem Head.Corresponds.refl (head : Head n k α) :
    head.Corresponds head := by
  cases head with
  | bound i => exact .bound i.val i.isLt i.isLt
  | outer i => exact .outer i
  | port x => exact .port x

private theorem Head.Corresponds.trans {a : Head n k α}
    {b : Head n l α} {c : Head n m α}
    (hab : a.Corresponds b) (hbc : b.Corresponds c) :
    a.Corresponds c := by
  cases hab with
  | bound i hik hil =>
      cases hbc
      next hjm => exact .bound i hik hjm
  | outer i =>
      cases hbc
      exact .outer i
  | port x =>
      cases hbc
      exact .port x

private inductive List.Forall₂ (r : α → β → Prop) :
    List α → List β → Prop where
  | nil : Forall₂ r [] []
  | cons : r x y → Forall₂ r xs ys → Forall₂ r (x :: xs) (y :: ys)

private theorem List.Forall₂.reduces_refl (xs : List (Term n α)) :
    List.Forall₂ Reduces xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons .refl ih

private theorem List.Forall₂.reduces_trans {xs ys zs : List (Term n α)}
    (hxy : List.Forall₂ Reduces xs ys)
    (hyz : List.Forall₂ Reduces ys zs) :
    List.Forall₂ Reduces xs zs := by
  induction hxy generalizing zs with
  | nil => cases hyz; exact .nil
  | cons hxy hxys ih =>
      cases hyz with
      | cons hyz hyzs => exact .cons (hxy.trans hyz) (ih hyzs)

private theorem List.Forall₂.reduces_rename
    {xs ys : List (Term n α)} (h : List.Forall₂ Reduces xs ys)
    (ρ : Fin n → Fin m) :
    List.Forall₂ Reduces (xs.map (Term.renameBound ρ))
      (ys.map (Term.renameBound ρ)) := by
  induction h with
  | nil => exact .nil
  | cons hxy hxys ih => exact .cons (hxy.renameBound ρ) ih

private theorem List.Forall₂.append
    {r : α → β → Prop} {xs us : List α} {ys vs : List β}
    (hxy : List.Forall₂ r xs ys) (huv : List.Forall₂ r us vs) :
    List.Forall₂ r (xs ++ us) (ys ++ vs) := by
  induction hxy with
  | nil => exact huv
  | cons hxy hxys ih => exact .cons hxy ih

private structure RigidResidualAt
    (K : Nat) (source target : HeadSpine n α) : Prop where
  source_le : source.binders ≤ K
  target_le : target.binders ≤ K
  head : source.head.Corresponds target.head
  args : List.Forall₂ Reduces
    (etaEnvelopeArgs K source source_le)
    (etaEnvelopeArgs K target target_le)

private theorem RigidResidualAt.refl (s : HeadSpine n α)
    (h : s.binders ≤ K) : RigidResidualAt K s s where
  source_le := h
  target_le := h
  head := Head.Corresponds.refl s.head
  args := List.Forall₂.reduces_refl _

private theorem RigidResidualAt.trans
    {source middle target : HeadSpine n α}
    (hsm : RigidResidualAt K source middle)
    (hmt : RigidResidualAt K middle target) :
    RigidResidualAt K source target := by
  have hmiddle : hsm.target_le = hmt.source_le := Subsingleton.elim _ _
  cases hmiddle
  exact
    { source_le := hsm.source_le
      target_le := hmt.target_le
      head := hsm.head.trans hmt.head
      args := hsm.args.reduces_trans hmt.args }

private theorem RigidResidualAt.raise
    {source target : HeadSpine n α}
    (hst : RigidResidualAt K source target) (hKL : K ≤ L) :
    RigidResidualAt L source target := by
  have hargs := (hst.args.reduces_rename (scopeEmbed (n := n) hKL)).append
    (List.Forall₂.reduces_refl
      (etaProjections (α := α) n L (L - K) (Nat.sub_le _ _)))
  rw [etaEnvelopeArgs_fusion source hst.source_le hKL,
    etaEnvelopeArgs_fusion target hst.target_le hKL] at hargs
  exact
    { source_le := Nat.le_trans hst.source_le hKL
      target_le := Nat.le_trans hst.target_le hKL
      head := hst.head
      args := hargs }

private def RawHead.rename (ρ : Fin n → Fin m) :
    RawHead n α → RawHead m α
  | .bvar i => .bvar (ρ i)
  | .port x => .port x

private def RawSpine.rename (ρ : Fin n → Fin m)
    (s : RawSpine n α) : RawSpine m α where
  head := s.head.rename ρ
  args := s.args.map (Term.renameBound ρ)

private theorem rawSpine_renameBound (t : Term n α)
    (ρ : Fin n → Fin m) :
    rawSpine (t.renameBound ρ) = (rawSpine t).map (RawSpine.rename ρ) := by
  induction t with
  | bvar i => rfl
  | port x => rfl
  | lam body ih => rfl
  | app fn arg ihFn ihArg =>
      simp only [Term.renameBound, rawSpine, ihFn]
      cases rawSpine fn with
      | none => rfl
      | some s =>
          cases s
          simp only [Option.map_some, RawSpine.rename, RawHead.rename,
            List.map_append, List.map_cons, List.map_nil]

private theorem rawSpine_app_inv {fn arg : Term n α} {s : RawSpine n α}
    (h : rawSpine (Term.app fn arg) = some s) :
    ∃ fs, rawSpine fn = some fs ∧
      s = { head := fs.head, args := fs.args ++ [arg] } := by
  simp only [rawSpine, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  exact ⟨fs, hfs, rfl⟩

private def RawSpine.toHeadSpine (raw : RawSpine n α) : HeadSpine n α where
  binders := 0
  head := classifyHead 0 raw.head
  args := raw.args

private def RawSpine.pushArg (raw : RawSpine n α)
    (arg : Term n α) : HeadSpine n α where
  binders := 0
  head := classifyHead 0 raw.head
  args := raw.args ++ [arg]

private theorem headSpine_of_raw {t : Term n α} {raw : RawSpine n α}
    (hraw : rawSpine t = some raw) :
    headSpine t = some raw.toHeadSpine := by
  let s : HeadSpine n α := raw.toHeadSpine
  have ht : t = s.toTerm := by
    unfold s RawSpine.toHeadSpine HeadSpine.toTerm
    simp only [prefixClose]
    rw [classifyHead_toTerm, rawSpine_sound hraw]
    rfl
  rw [ht, headSpine_toTerm]

private theorem headSpine_app_inv {fn arg : Term n α} {s : HeadSpine n α}
    (h : headSpine (Term.app fn arg) = some s) :
    ∃ raw : RawSpine n α, rawSpine fn = some raw ∧
      s = raw.pushArg arg := by
  unfold headSpine at h
  simp only [peelPrefix, rawSpine, Option.map_eq_some_iff] at h
  obtain ⟨raw, ⟨fnRaw, hfn, rfl⟩, rfl⟩ := h
  exact ⟨fnRaw, hfn, rfl⟩

private theorem headSpine_app_push_raw {fn arg : Term n α}
    {raw : RawSpine n α} (hraw : rawSpine fn = some raw) :
    headSpine (Term.app fn arg) = some (raw.pushArg arg) := by
  let pushed : RawSpine n α :=
    { head := raw.head, args := raw.args ++ [arg] }
  have hrawApp : rawSpine (Term.app fn arg) = some pushed := by
    change (rawSpine fn).map (fun s =>
      { head := s.head, args := s.args ++ [arg] }) = some pushed
    rw [hraw]
    rfl
  have h := headSpine_of_raw hrawApp
  change headSpine (Term.app fn arg) = some (raw.pushArg arg) at h
  exact h

private theorem headSpine_zero_raw {t : Term n α} {s : HeadSpine n α}
    (ht : headSpine t = some s) (hzero : s.binders = 0) :
    ∃ raw : RawSpine n α, rawSpine t = some raw ∧ s = raw.toHeadSpine := by
  cases s with
  | mk binders head args =>
      dsimp only at hzero ⊢
      subst binders
      let raw : RawSpine n α := { head := head.toRaw, args := args }
      have hraw : rawSpine t = some raw := by
        rw [headSpine_sound ht]
        unfold HeadSpine.toTerm raw
        simp only [prefixClose]
        calc
          rawSpine (applyArgs head.toTerm args) =
              rawSpine (applyArgs head.toRaw.toTerm args) := by
            rw [head.toRaw_toTerm]
          _ = some { head := head.toRaw, args := args } :=
            rawSpine_applyArgs head.toRaw args
      refine ⟨raw, hraw, ?_⟩
      unfold raw RawSpine.toHeadSpine
      simp only [classifyHead_toRaw]

private theorem rawSpine_lift_inv {fn : Term n α}
    {lifted : RawSpine (n + 1) α}
    (h : rawSpine fn.lift = some lifted) :
    ∃ raw : RawSpine n α, rawSpine fn = some raw ∧
      lifted = raw.rename Fin.succ := by
  unfold Term.lift at h
  rw [rawSpine_renameBound] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨raw, hraw, rfl⟩ := h
  exact ⟨raw, hraw, rfl⟩

private def RawSpine.etaSource (raw : RawSpine n α) : HeadSpine n α :=
  (raw.rename Fin.succ).pushArg
    (Term.bvar (free := α) (bound := n + 1) 0) |>.wrap

private theorem classifyHead_rename_succ_wrap (head : RawHead n α) :
    (classifyHead (n := n + 1) 0 (head.rename Fin.succ)).wrap.Corresponds
      (classifyHead (n := n) 0 head) := by
  cases head with
  | port x => exact .port x
  | bvar i =>
      have hsource : classifyHead (n := n + 1) 0
          ((RawHead.bvar i : RawHead n α).rename Fin.succ) =
          (.outer (Fin.succ i) : Head (n + 1) 0 α) := by
        simp only [RawHead.rename, classifyHead]
        split
        next h => omega
        next h =>
          apply congrArg Head.outer
          apply Fin.ext
          simp only [Fin.val_mk, Fin.succ]
          omega
      have htarget : classifyHead (n := n) 0
          (RawHead.bvar i : RawHead n α) =
          (.outer i : Head n 0 α) := by
        simp only [classifyHead]
        split
        next h => omega
        next h =>
          apply congrArg Head.outer
          apply Fin.ext
          change i.val - 0 = i.val
          omega
      rw [hsource, htarget]
      exact .outer i

private theorem etaSource_head (raw : RawSpine n α) :
    raw.etaSource.head.Corresponds raw.toHeadSpine.head := by
  unfold RawSpine.etaSource RawSpine.pushArg RawSpine.toHeadSpine
  exact classifyHead_rename_succ_wrap raw.head

private theorem etaEnvelopeArgs_one (head : Head n 0 α)
    (args : List (Term n α)) :
    args.map Term.lift ++
      [(Term.bvar (free := α) (bound := n + 1) 0)] =
      etaEnvelopeArgs 1
        ({ binders := 0, head := head, args := args } : HeadSpine n α)
        (by change 0 ≤ 1; omega) := by
  simp only [etaEnvelopeArgs, etaProjections]
  apply congrArg (fun xs => xs ++
    [(Term.bvar (free := α) (bound := n + 1) 0)])
  apply List.map_congr_left
  intro t ht
  unfold Term.lift
  apply congrArg (fun r => t.renameBound r)
  funext i
  apply Fin.ext
  simp only [scopeEmbed, Fin.val_mk, Fin.succ]
  omega

private theorem etaSource_envelope (raw : RawSpine n α) :
    etaEnvelopeArgs 1 raw.etaSource (by
      change 1 ≤ 1
      omega) =
    etaEnvelopeArgs 1 raw.toHeadSpine (by
      change 0 ≤ 1
      omega) := by
  change etaEnvelopeArgs 1
      ((raw.rename Fin.succ).pushArg
        (Term.bvar (free := α) (bound := n + 1) 0)).wrap _ = _
  rw [← etaEnvelopeArgs_wrap
    ((raw.rename Fin.succ).pushArg
      (Term.bvar (free := α) (bound := n + 1) 0)) (K := 0) (by
        change 0 ≤ 0
        omega)]
  have hid := etaEnvelopeArgs_identity
    ((raw.rename Fin.succ).pushArg
      (Term.bvar (free := α) (bound := n + 1) 0))
  change etaEnvelopeArgs 0
      ((raw.rename Fin.succ).pushArg
        (Term.bvar (free := α) (bound := n + 1) 0)) _ = _ at hid
  rw [hid]
  change _ = etaEnvelopeArgs 1
    ({ binders := 0, head := classifyHead 0 raw.head, args := raw.args } :
      HeadSpine n α) _
  rw [← etaEnvelopeArgs_one (classifyHead 0 raw.head) raw.args]
  unfold RawSpine.pushArg RawSpine.rename
  rfl

private theorem headCorresponds_wrap
    {a : Head (n + 1) k α} {b : Head (n + 1) l α}
    (h : a.Corresponds b) : a.wrap.Corresponds b.wrap := by
  cases h with
  | bound i hik hil => exact .bound (i + 1) (by omega) (by omega)
  | outer i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .bound 0 (by omega) (by omega)
      · exact .outer j
  | port x => exact .port x

private theorem OneStep.preserveRigidBase
    {a b : Term n α} {source : HeadSpine n α}
    (ha : headSpine a = some source) (hab : OneStep a b) :
    ∃ target, headSpine b = some target ∧
      RigidResidualAt source.binders source target := by
  induction hab with
  | beta hred =>
      obtain ⟨raw, hraw, rfl⟩ := headSpine_app_inv ha
      simp only [rawSpine] at hraw
      contradiction
  | eta heta =>
      rw [etaContract_sound heta, headSpine_lam] at ha
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨bodySpine, hbody, rfl⟩ := ha
      obtain ⟨lifted, hlifted, rfl⟩ := headSpine_app_inv hbody
      obtain ⟨raw, hraw, rfl⟩ := rawSpine_lift_inv hlifted
      refine ⟨raw.toHeadSpine, headSpine_of_raw hraw, ?_⟩
      have hargs : List.Forall₂ Reduces
          (etaEnvelopeArgs 1 raw.etaSource (by change 1 ≤ 1; omega))
          (etaEnvelopeArgs 1 raw.toHeadSpine (by change 0 ≤ 1; omega)) := by
        rw [etaSource_envelope raw]
        exact List.Forall₂.reduces_refl _
      exact
        { source_le := by change 1 ≤ 1; omega
          target_le := by change 0 ≤ 1; omega
          head := etaSource_head raw
          args := hargs }
  | lam hab ih =>
      rw [headSpine_lam] at ha
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨innerSource, hinner, rfl⟩ := ha
      obtain ⟨innerTarget, htarget, hres⟩ := ih hinner
      refine ⟨innerTarget.wrap, ?_, ?_⟩
      · rw [headSpine_lam, htarget]
        rfl
      · have hargs := hres.args
        rw [etaEnvelopeArgs_wrap innerSource hres.source_le,
          etaEnvelopeArgs_wrap innerTarget hres.target_le] at hargs
        exact
          { source_le := by
              change innerSource.binders + 1 ≤ innerSource.binders + 1
              omega
            target_le := by
              change innerTarget.binders + 1 ≤ innerSource.binders + 1
              exact Nat.add_le_add_right hres.target_le 1
            head := headCorresponds_wrap hres.head
            args := hargs }
  | @appFn q γ fn fn' fixedArg hab ih =>
      obtain ⟨sourceRaw, hsourceRaw, rfl⟩ := headSpine_app_inv ha
      have hsource := headSpine_of_raw hsourceRaw
      obtain ⟨innerTarget, htarget, hres⟩ := ih hsource
      have hzero : innerTarget.binders = 0 := Nat.eq_zero_of_le_zero hres.target_le
      obtain ⟨targetRaw, htargetRaw, htargetEq⟩ :=
        headSpine_zero_raw htarget hzero
      subst innerTarget
      refine ⟨targetRaw.pushArg fixedArg,
        headSpine_app_push_raw htargetRaw, ?_⟩
      have hargs := hres.args
      change List.Forall₂ Reduces
        (etaEnvelopeArgs 0 sourceRaw.toHeadSpine _)
        (etaEnvelopeArgs 0 targetRaw.toHeadSpine _) at hargs
      have hsourceIdentity := etaEnvelopeArgs_identity sourceRaw.toHeadSpine
      have htargetIdentity := etaEnvelopeArgs_identity targetRaw.toHeadSpine
      change etaEnvelopeArgs 0 sourceRaw.toHeadSpine _ = _ at hsourceIdentity
      change etaEnvelopeArgs 0 targetRaw.toHeadSpine _ = _ at htargetIdentity
      rw [hsourceIdentity, htargetIdentity] at hargs
      have hargs' := hargs.append
        (List.Forall₂.cons (Reduces.refl (a := fixedArg)) List.Forall₂.nil)
      have hsourceArgs := etaEnvelopeArgs_identity
        (sourceRaw.pushArg fixedArg)
      have htargetArgs := etaEnvelopeArgs_identity
        (targetRaw.pushArg fixedArg)
      change etaEnvelopeArgs 0 (sourceRaw.pushArg fixedArg) _ = _ at hsourceArgs
      change etaEnvelopeArgs 0 (targetRaw.pushArg fixedArg) _ = _ at htargetArgs
      have hfinal : List.Forall₂ Reduces
          (etaEnvelopeArgs 0 (sourceRaw.pushArg fixedArg)
            (by change 0 ≤ 0; omega))
          (etaEnvelopeArgs 0 (targetRaw.pushArg fixedArg)
            (by change 0 ≤ 0; omega)) := by
        rw [hsourceArgs, htargetArgs]
        exact hargs'
      exact
        { source_le := by change 0 ≤ 0; omega
          target_le := by change 0 ≤ 0; omega
          head := hres.head
          args := hfinal }
  | @appArg q γ changedArg changedArg' fixedFn hab ih =>
      obtain ⟨sourceRaw, hsourceRaw, rfl⟩ := headSpine_app_inv ha
      refine ⟨sourceRaw.pushArg changedArg',
        headSpine_app_push_raw hsourceRaw, ?_⟩
      have hargs := (List.Forall₂.reduces_refl sourceRaw.args).append
        (List.Forall₂.cons (Reduces.tail .refl hab) List.Forall₂.nil)
      have hsourceArgs := etaEnvelopeArgs_identity
        (sourceRaw.pushArg changedArg)
      have htargetArgs := etaEnvelopeArgs_identity
        (sourceRaw.pushArg changedArg')
      change etaEnvelopeArgs 0 (sourceRaw.pushArg changedArg) _ = _ at hsourceArgs
      change etaEnvelopeArgs 0 (sourceRaw.pushArg changedArg') _ = _ at htargetArgs
      have hfinal : List.Forall₂ Reduces
          (etaEnvelopeArgs 0 (sourceRaw.pushArg changedArg)
            (by change 0 ≤ 0; omega))
          (etaEnvelopeArgs 0 (sourceRaw.pushArg changedArg')
            (by change 0 ≤ 0; omega)) := by
        rw [hsourceArgs, htargetArgs]
        exact hargs
      exact
        { source_le := by change 0 ≤ 0; omega
          target_le := by change 0 ≤ 0; omega
          head := Head.Corresponds.refl _
          args := hfinal }

private theorem OneStep.preserveRigid
    {a b : Term n α} {source : HeadSpine n α}
    (ha : headSpine a = some source) (hab : OneStep a b)
    (hK : source.binders ≤ K) :
    ∃ target, headSpine b = some target ∧ RigidResidualAt K source target := by
  obtain ⟨target, hb, hres⟩ := OneStep.preserveRigidBase ha hab
  exact ⟨target, hb, hres.raise hK⟩

private theorem Reduces.preserveRigid
    {a b : Term n α} {source : HeadSpine n α}
    (ha : headSpine a = some source) (hab : Reduces a b)
    (hK : source.binders ≤ K) :
    ∃ target, headSpine b = some target ∧ RigidResidualAt K source target := by
  induction hab generalizing source K with
  | refl => exact ⟨source, ha, RigidResidualAt.refl source hK⟩
  | tail hab hstep ih =>
      obtain ⟨middle, hmiddle, hres₁⟩ := ih ha hK
      obtain ⟨target, htarget, hres₂⟩ :=
        OneStep.preserveRigid hmiddle hstep hres₁.target_le
      exact ⟨target, htarget, hres₁.trans hres₂⟩

private theorem List.Forall₂.length_eq
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons hxy hxys ih => simp only [List.length_cons, ih]

private theorem List.Forall₂.get
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) (i : Fin xs.length) :
    r (xs.get i) (ys.get ⟨i.val, by rw [← h.length_eq]; exact i.isLt⟩) := by
  induction h with
  | nil => exact Fin.elim0 i
  | cons hxy hxys ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hxy
      · exact ih j

private theorem List.Forall₂.of_get
    {r : α → β → Prop} {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length)
    (hget : ∀ index : Fin xs.length,
      r (xs.get index) (ys.get (Fin.cast hlen index))) :
    List.Forall₂ r xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact .nil
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlength : xs.length = ys.length := by simpa using hlen
          apply List.Forall₂.cons
          · have head := hget (Fin.mk 0 (by simp))
            simpa using head
          · apply ih hlength
            intro index
            have tail := hget index.succ
            simpa using tail

private theorem BetaEta.applyArgs₂ {fn fn' : Term n α}
    {left right : List (Term n α)}
    (head : BetaEta fn fn') (arguments : List.Forall₂ BetaEta left right) :
    BetaEta (VisualProof.Lambda.applyArgs fn left)
      (VisualProof.Lambda.applyArgs fn' right) := by
  induction arguments generalizing fn fn' with
  | nil => exact head
  | cons argument rest ih => exact ih (head.app argument)

private theorem Reduces.toBetaEta {a b : Term n α} (h : Reduces a b) :
    BetaEta a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (.step hstep)

private theorem BetaEta.prefixClose {a b : Term (extendScope n k) α}
    (h : BetaEta a b) : BetaEta (prefixClose k a) (prefixClose k b) := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih =>
      change BetaEta (Term.lam (VisualProof.Lambda.prefixClose k a))
        (Term.lam (VisualProof.Lambda.prefixClose k b))
      exact (ih h).lam

private theorem BetaEta.prefixClose_cancel
    {a b : Term (extendScope n k) α}
    (h : BetaEta (VisualProof.Lambda.prefixClose k a)
      (VisualProof.Lambda.prefixClose k b)) : BetaEta a b := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => exact ih h.lam_cancel

theorem rigidHead_args
  {n : Nat} {α : Type u} {a b : Term n α}
  {sa sb : HeadSpine n α}
  (ha : headSpine a = some sa)
  (hb : headSpine b = some sb)
  (heq : BetaEta a b)
  (hbinders : sa.binders = sb.binders)
  (hhead : sa.head.Corresponds sb.head)
  (hlen : sa.args.length = sb.args.length) :
  ∀ i (hi : i < sa.args.length),
    BetaEta (prefixClose sa.binders (sa.args.get ⟨i, hi⟩))
      (prefixClose sb.binders (sb.args.get ⟨i, hlen ▸ hi⟩)) := by
  cases sa with
  | mk ka ahead aargs =>
      cases sb with
      | mk kb bhead bargs =>
          dsimp only at ha hb hbinders hhead hlen ⊢
          subst kb
          obtain ⟨common, hac, hbc⟩ := churchRosser heq
          obtain ⟨commonSpine, hcommon, hresA⟩ :=
            Reduces.preserveRigid ha hac (Nat.le_refl ka)
          obtain ⟨commonSpineB, hcommonB, hresB⟩ :=
            Reduces.preserveRigid hb hbc (Nat.le_refl ka)
          have hspine : commonSpineB = commonSpine := by
            rw [hcommon] at hcommonB
            exact (Option.some.inj hcommonB).symm
          subst commonSpineB
          have htargetProof : hresA.target_le = hresB.target_le :=
            Subsingleton.elim _ _
          cases htargetProof
          have hargsA := hresA.args
          have hargsB := hresB.args
          have hidA := etaEnvelopeArgs_identity
            ({ binders := ka, head := ahead, args := aargs } : HeadSpine n α)
          have hidB := etaEnvelopeArgs_identity
            ({ binders := ka, head := bhead, args := bargs } : HeadSpine n α)
          change etaEnvelopeArgs ka
            ({ binders := ka, head := ahead, args := aargs } : HeadSpine n α)
              _ = aargs at hidA
          change etaEnvelopeArgs ka
            ({ binders := ka, head := bhead, args := bargs } : HeadSpine n α)
              _ = bargs at hidB
          rw [hidA] at hargsA
          rw [hidB] at hargsB
          intro i hi
          have hargA := hargsA.get ⟨i, hi⟩
          have hargB := hargsB.get ⟨i, hlen ▸ hi⟩
          have hcommonIndex :
              (⟨i, by rw [← hargsB.length_eq]; exact hlen ▸ hi⟩ :
                Fin (etaEnvelopeArgs ka commonSpine hresA.target_le).length) =
              ⟨i, by rw [← hargsA.length_eq]; exact hi⟩ := by
            apply Fin.ext
            rfl
          rw [hcommonIndex] at hargB
          exact (hargA.toBetaEta.prefixClose).trans
            hargB.toBetaEta.prefixClose.symm

/-- Canonical-evaluation form of rigid-head decomposition.  It starts with
beta-eta equality only after one closed substitution, matching what equality
of two term-node evaluations supplies. -/
theorem rigidHead_args_bindFree_bound
    {α : Type u} {a b : Term 0 α} {sa sb : HeadSpine 0 α}
    (ha : headSpine a = some sa)
    (hb : headSpine b = some sb)
    (sameBinders : sa.binders = sb.binders)
    (headIndex : Fin sa.binders)
    (firstHead : sa.head = .bound headIndex)
    (secondHead : sb.head = .bound (Fin.cast sameBinders headIndex))
    (sameLength : sa.args.length = sb.args.length)
    (substitution : α → ClosedTerm)
    (equivalent : BetaEta (a.bindFree substitution)
      (b.bindFree substitution)) :
    ∀ index (valid : index < sa.args.length),
      BetaEta
        ((prefixClose sa.binders (sa.args.get ⟨index, valid⟩)).bindFree
          substitution)
        ((prefixClose sb.binders
          (sb.args.get ⟨index, sameLength ▸ valid⟩)).bindFree substitution) := by
  let leftSpine : HeadSpine 0 Empty := {
    binders := sa.binders
    head := .bound headIndex
    args := sa.args.map fun argument =>
      argument.bindFree fun port => (substitution port).liftClosed
  }
  let rightSpine : HeadSpine 0 Empty := {
    binders := sb.binders
    head := .bound (Fin.cast sameBinders headIndex)
    args := sb.args.map fun argument =>
      argument.bindFree fun port => (substitution port).liftClosed
  }
  have hleft : headSpine (a.bindFree substitution) = some leftSpine := by
    exact headSpine_bindFree_bound ha headIndex firstHead substitution
  have hright : headSpine (b.bindFree substitution) = some rightSpine := by
    exact headSpine_bindFree_bound hb (Fin.cast sameBinders headIndex)
      secondHead substitution
  have hbinders : leftSpine.binders = rightSpine.binders := sameBinders
  have hheads : leftSpine.head.Corresponds rightSpine.head := by
    exact .bound headIndex.val headIndex.isLt
      (by simpa only [sameBinders] using headIndex.isLt)
  have hlength : leftSpine.args.length = rightSpine.args.length := by
    simpa [leftSpine, rightSpine] using sameLength
  have hrigid := rigidHead_args hleft hright equivalent hbinders hheads hlength
  intro index valid
  have hvalid : index < leftSpine.args.length := by
    simpa [leftSpine] using valid
  have h := hrigid index hvalid
  dsimp only [leftSpine, rightSpine] at h
  simp at h
  rw [← prefixClose_bindFree_closed, ← prefixClose_bindFree_closed] at h
  exact h

/-- Aligned bound rigid heads are reconstructed by congruence from pairwise
beta-eta-equivalent closed argument abstractions. This is the converse logical
kernel required when head-strip replaces, rather than retains, its head
equation. -/
theorem rigidHead_of_args_bindFree_bound
    {α : Type u} {a b : Term 0 α} {sa sb : HeadSpine 0 α}
    (ha : headSpine a = some sa)
    (hb : headSpine b = some sb)
    (sameBinders : sa.binders = sb.binders)
    (headIndex : Fin sa.binders)
    (firstHead : sa.head = .bound headIndex)
    (secondHead : sb.head = .bound (Fin.cast sameBinders headIndex))
    (sameLength : sa.args.length = sb.args.length)
    (substitution : α → ClosedTerm)
    (argumentsEquivalent : ∀ index (valid : index < sa.args.length),
      BetaEta
        ((prefixClose sa.binders (sa.args.get ⟨index, valid⟩)).bindFree
          substitution)
        ((prefixClose sb.binders
          (sb.args.get ⟨index, sameLength ▸ valid⟩)).bindFree substitution)) :
    BetaEta (a.bindFree substitution) (b.bindFree substitution) := by
  cases sa with
  | mk ka ahead aargs =>
      cases sb with
      | mk kb bhead bargs =>
          dsimp only at ha hb sameBinders headIndex firstHead secondHead sameLength argumentsEquivalent ⊢
          subst kb
          let leftSpine : HeadSpine 0 Empty := {
            binders := ka
            head := .bound headIndex
            args := aargs.map fun argument =>
              argument.bindFree fun port => (substitution port).liftClosed
          }
          let rightSpine : HeadSpine 0 Empty := {
            binders := ka
            head := .bound headIndex
            args := bargs.map fun argument =>
              argument.bindFree fun port => (substitution port).liftClosed
          }
          have hleft : headSpine (a.bindFree substitution) = some leftSpine :=
            headSpine_bindFree_bound ha headIndex firstHead substitution
          have hright : headSpine (b.bindFree substitution) = some rightSpine :=
            headSpine_bindFree_bound hb headIndex secondHead substitution
          have hlength : leftSpine.args.length = rightSpine.args.length := by
            simpa [leftSpine, rightSpine] using sameLength
          have harguments : List.Forall₂ BetaEta leftSpine.args
              rightSpine.args := by
            apply List.Forall₂.of_get hlength
            intro index
            let original : Fin aargs.length :=
              Fin.cast (by simp [leftSpine]) index
            have equivalent := argumentsEquivalent original.val original.isLt
            rw [prefixClose_bindFree_closed, prefixClose_bindFree_closed] at equivalent
            have bodies := equivalent.prefixClose_cancel
            simpa [leftSpine, rightSpine, original] using bodies
          rw [headSpine_sound hleft, headSpine_sound hright]
          unfold HeadSpine.toTerm
          apply BetaEta.prefixClose
          apply BetaEta.applyArgs₂
          · exact .refl
          · exact harguments

end VisualProof.Lambda
