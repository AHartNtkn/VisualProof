import VisualProof.Lambda.Reduction

namespace VisualProof.Lambda

def betaEtaSetoid : Setoid ClosedTerm where
  r := BetaEta
  iseqv := betaEta_equivalence

def Individual := Quotient betaEtaSetoid

def quote (term : ClosedTerm) : Individual :=
  Quotient.mk betaEtaSetoid term

theorem quote_eq_iff {a b : ClosedTerm} :
    quote a = quote b ↔ BetaEta a b := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := betaEtaSetoid) h

theorem Term.bindFree_betaEta
    (term : Term n α) {left right : α → Term n β}
    (h : ∀ x, BetaEta (left x) (right x)) :
    BetaEta (term.bindFree left) (term.bindFree right) := by
  induction term with
  | bvar _ => exact .refl
  | port x => exact h x
  | lam body ih =>
      exact ih (fun x => (h x).renameBound Fin.succ) |>.lam
  | app fn arg ihFn ihArg => exact BetaEta.app (ihFn h) (ihArg h)

theorem quote_bindFree_independent
    (term : Term 0 α) {left right : α → ClosedTerm}
    (h : ∀ x, BetaEta (left x) (right x)) :
    quote (term.bindFree left) = quote (term.bindFree right) := by
  exact Quotient.sound (term.bindFree_betaEta h)

theorem quote_bindFree_independent_of_quotes
    (term : Term 0 α) {left right : α → ClosedTerm}
    (h : ∀ x, quote (left x) = quote (right x)) :
    quote (term.bindFree left) = quote (term.bindFree right) := by
  apply quote_bindFree_independent
  intro x
  exact quote_eq_iff.mp (h x)

structure LambdaModel where
  Carrier : Type
  eval : {n : Nat} → Term 0 (Fin n) → (Fin n → Carrier) → Carrier
  eval_port : ∀ {n} (i : Fin n) (env : Fin n → Carrier),
    eval (.port i) env = env i
  eval_bindFree : ∀ {n m} (term : Term 0 (Fin n))
      (substitution : Fin n → Term 0 (Fin m))
      (env : Fin m → Carrier),
    eval (term.bindFree substitution) env =
      eval term (fun i => eval (substitution i) env)
  betaEta_sound : ∀ {n} {a b : Term 0 (Fin n)} {env : Fin n → Carrier},
    BetaEta a b → eval a env = eval b env

theorem LambdaModel.eval_mapFree
    (model : LambdaModel) (rename : Fin n → Fin m)
    (term : Term 0 (Fin n)) (env : Fin m → model.Carrier) :
    model.eval (term.mapFree rename) env =
      model.eval term (env ∘ rename) := by
  rw [Term.mapFree_eq_bindFree_ports, model.eval_bindFree]
  apply congrArg (model.eval term)
  funext i
  exact model.eval_port (rename i) env

private noncomputable def representative (individual : Individual) : ClosedTerm :=
  Classical.choose (Quotient.exists_rep individual)

private theorem quote_representative (individual : Individual) :
    quote (representative individual) = individual := by
  exact Classical.choose_spec (Quotient.exists_rep individual)

noncomputable def canonicalEval
    (term : Term 0 (Fin n)) (env : Fin n → Individual) : Individual :=
  quote (term.bindFree (fun i => representative (env i)))

theorem canonicalEval_eq_of_representatives
    (term : Term 0 (Fin n)) (env : Fin n → Individual)
    (reps : Fin n → ClosedTerm)
    (hreps : ∀ i, quote (reps i) = env i) :
    canonicalEval term env = quote (term.bindFree reps) := by
  unfold canonicalEval
  apply quote_bindFree_independent_of_quotes
  intro i
  exact (quote_representative (env i)).trans (hreps i).symm

noncomputable def canonicalModel : LambdaModel where
  Carrier := Individual
  eval := canonicalEval
  eval_port := by
    intro n i env
    exact quote_representative (env i)
  eval_bindFree := by
    intro n m term substitution env
    let reps : Fin m → ClosedTerm := fun i => representative (env i)
    let substitutedReps : Fin n → ClosedTerm :=
      fun i => (substitution i).bindFree reps
    calc
      canonicalEval (term.bindFree substitution) env =
          quote ((term.bindFree substitution).bindFree reps) :=
        canonicalEval_eq_of_representatives _ _ reps
          (fun i => quote_representative (env i))
      _ = quote (term.bindFree substitutedReps) :=
        congrArg quote (Term.bindFree_assoc term substitution reps)
      _ = canonicalEval term (fun i => canonicalEval (substitution i) env) :=
        (canonicalEval_eq_of_representatives term _ substitutedReps
          (fun i => (canonicalEval_eq_of_representatives
            (substitution i) env reps
              (fun j => quote_representative (env j))).symm)).symm
  betaEta_sound := by
    intro n a b env h
    unfold canonicalEval
    exact Quotient.sound
      (h.bindFree (fun i => representative (env i)))

theorem canonicalModel_eval_eq_quote
    (term : Term 0 (Fin n)) (env : Fin n → Individual)
    (reps : Fin n → ClosedTerm)
    (hreps : ∀ i, quote (reps i) = env i) :
    canonicalModel.eval term env = quote (term.bindFree reps) := by
  exact canonicalEval_eq_of_representatives term env reps hreps

theorem canonicalModel_eval_port (i : Fin n)
    (env : Fin n → Individual) :
    canonicalModel.eval (Term.port i) env = env i := by
  exact canonicalModel.eval_port i env

theorem canonicalModel_eval_quoted
    (term : ClosedTerm) (env : Fin n → Individual) :
    canonicalModel.eval (term.mapFree Empty.elim) env = quote term := by
  unfold canonicalModel canonicalEval
  apply congrArg quote
  have noFree_bind : ∀ {k : Nat} (body : Term k Empty)
      (reps : Fin n → Term k Empty),
      (body.mapFree Empty.elim).bindFree reps = body := by
    intro k body
    induction body with
    | bvar _ => intro _; rfl
    | port x => exact Empty.elim x
    | lam body ih =>
        intro reps
        exact congrArg Term.lam (ih (fun i => (reps i).lift))
    | app fn arg ihFn ihArg =>
        intro reps
        simp only [Term.mapFree, Term.bindFree, ihFn reps, ihArg reps]
  exact noFree_bind term (fun i => representative (env i))

end VisualProof.Lambda
