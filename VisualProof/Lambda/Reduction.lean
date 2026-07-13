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
        simp only [Fin.val_mk]
        omega
      next h =>
        simp only [Head.toTerm, RawHead.toTerm]
        apply congrArg Term.bvar
        apply Fin.ext
        simp only [Fin.val_mk]
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

end VisualProof.Lambda
