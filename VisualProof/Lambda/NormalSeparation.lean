import VisualProof.Lambda.Certificate
import VisualProof.Lambda.Normalize
import VisualProof.Lambda.Quotient

namespace VisualProof.Lambda

def hasRedex : Term n α → Bool
  | .bvar _ | .port _ => false
  | .lam body => (etaContract body).isSome || hasRedex body
  | .app (.lam _) _ => true
  | .app fn arg => hasRedex fn || hasRedex arg

def isNormal (term : Term n α) : Bool :=
  !hasRedex term

theorem hasRedex_eq_true_iff {term : Term n α} :
    hasRedex term = true ↔ ∃ next, OneStep term next := by
  induction term with
  | bvar index =>
      constructor
      · intro impossible
        contradiction
      · rintro ⟨next, step⟩
        cases step
  | port value =>
      constructor
      · intro impossible
        contradiction
      · rintro ⟨next, step⟩
        cases step
  | lam body ih =>
      constructor
      · simp only [hasRedex, Bool.or_eq_true, Option.isSome_iff_exists]
        rintro (⟨next, contracted⟩ | bodyRedex)
        · exact ⟨next, OneStep.eta contracted⟩
        · obtain ⟨next, step⟩ := ih.mp bodyRedex
          exact ⟨Term.lam next, OneStep.lam step⟩
      · rintro ⟨next, step⟩
        cases step with
        | eta contracted =>
            rw [etaContract_sound contracted]
            simp only [hasRedex, etaContract_complete, Option.isSome_some,
              Bool.true_or]
        | lam bodyStep =>
            simpa only [hasRedex, Bool.or_eq_true] using
              (Or.inr (ih.mpr ⟨_, bodyStep⟩))
  | app fn arg ihFn ihArg =>
      cases fn with
      | bvar index =>
          constructor
          · intro argRedex
            obtain ⟨next, step⟩ := ihArg.mp argRedex
            exact ⟨Term.app (Term.bvar index) next, OneStep.appArg step⟩
          · rintro ⟨next, step⟩
            cases step with
            | appFn fnStep => cases fnStep
            | appArg argStep => exact ihArg.mpr ⟨_, argStep⟩
      | port value =>
          constructor
          · intro argRedex
            obtain ⟨next, step⟩ := ihArg.mp argRedex
            exact ⟨Term.app (Term.port value) next, OneStep.appArg step⟩
          · rintro ⟨next, step⟩
            cases step with
            | appFn fnStep => cases fnStep
            | appArg argStep => exact ihArg.mpr ⟨_, argStep⟩
      | lam body =>
          constructor
          · intro _
            exact ⟨_, OneStep.beta rfl⟩
          · intro _
            rfl
      | app innerFn innerArg =>
          constructor
          · intro redex
            have redex' : hasRedex (Term.app innerFn innerArg) = true ∨
                hasRedex arg = true := by
              simpa only [hasRedex, Bool.or_eq_true] using redex
            rcases redex' with fnRedex | argRedex
            · obtain ⟨next, step⟩ := ihFn.mp fnRedex
              exact ⟨Term.app next arg, OneStep.appFn step⟩
            · obtain ⟨next, step⟩ := ihArg.mp argRedex
              exact ⟨Term.app (Term.app innerFn innerArg) next,
                OneStep.appArg step⟩
          · rintro ⟨next, step⟩
            cases step with
            | appFn fnStep =>
                simpa only [hasRedex, Bool.or_eq_true] using
                  (Or.inl (ihFn.mpr ⟨_, fnStep⟩))
            | appArg argStep =>
                simpa only [hasRedex, Bool.or_eq_true] using
                  (Or.inr (ihArg.mpr ⟨_, argStep⟩))

theorem isNormal_iff {term : Term n α} :
    isNormal term = true ↔ Normal term := by
  constructor
  · intro normalTrue next step
    have redexTrue := hasRedex_eq_true_iff.mpr ⟨next, step⟩
    simp [isNormal, redexTrue] at normalTrue
  · intro normal
    cases redex : hasRedex term with
    | false => simp [isNormal, redex]
    | true =>
        obtain ⟨next, step⟩ := hasRedex_eq_true_iff.mp redex
        exact False.elim (normal next step)

theorem checkPath_reduces {start finish : Term n α} {path : ReductionPath} :
    checkPath start path = some finish → Reduces start finish := by
  induction path generalizing start with
  | nil =>
      intro equality
      cases equality
      exact .refl
  | cons step rest ih =>
      simp only [checkPath]
      split
      · intro impossible
        contradiction
      · rename_i next stepValid
        intro restValid
        exact (Reduces.tail .refl (stepAt_sound stepValid)).trans
          (ih restValid)

structure NormalSeparationCertificate where
  firstSteps : ReductionPath
  secondSteps : ReductionPath
  deriving DecidableEq, Repr

def checkNormalSeparation [DecidableEq α]
    (first second : Term n α)
    (certificate : NormalSeparationCertificate) : Bool :=
  match checkPath first certificate.firstSteps,
      checkPath second certificate.secondSteps with
  | some firstNormal, some secondNormal =>
      isNormal firstNormal && isNormal secondNormal &&
        decide (firstNormal ≠ secondNormal)
  | _, _ => false

structure CheckedNormalSeparation [DecidableEq α]
    (first second : Term n α) where
  certificate : NormalSeparationCertificate
  valid : checkNormalSeparation first second certificate = true

theorem CheckedNormalSeparation.sound [DecidableEq α]
    {first second : Term n α}
    (checked : CheckedNormalSeparation first second) :
    ∃ firstNormal secondNormal,
      Reduces first firstNormal ∧
      Reduces second secondNormal ∧
      Normal firstNormal ∧
      Normal secondNormal ∧
      firstNormal ≠ secondNormal := by
  have valid := checked.valid
  unfold checkNormalSeparation at valid
  generalize hfirst : checkPath first checked.certificate.firstSteps =
    firstResult at valid
  generalize hsecond : checkPath second checked.certificate.secondSteps =
    secondResult at valid
  cases firstResult with
  | none => simp at valid
  | some firstNormal =>
      cases secondResult with
      | none => simp at valid
      | some secondNormal =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          rcases valid with ⟨⟨firstNormalTrue, secondNormalTrue⟩, different⟩
          exact ⟨firstNormal, secondNormal,
            checkPath_reduces hfirst,
            checkPath_reduces hsecond,
            isNormal_iff.mp firstNormalTrue,
            isNormal_iff.mp secondNormalTrue,
            different⟩

theorem Reduces.betaEta {first second : Term n α}
    (reduces : Reduces first second) : BetaEta first second := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (.step step)

theorem CheckedNormalSeparation.not_betaEta [DecidableEq α]
    {first second : Term n α}
    (checked : CheckedNormalSeparation first second) :
    ¬ BetaEta first second := by
  obtain ⟨firstNormal, secondNormal, firstReduces, secondReduces,
    firstNormalProof, secondNormalProof, different⟩ := checked.sound
  intro equivalent
  exact not_betaEta_of_normal_ne firstNormalProof secondNormalProof different
    (firstReduces.betaEta.symm.trans
      (equivalent.trans secondReduces.betaEta))

theorem CheckedNormalSeparation.quote_ne
    {first second : ClosedTerm}
    (checked : CheckedNormalSeparation first second) :
    quote first ≠ quote second := by
  intro equal
  exact checked.not_betaEta (quote_eq_iff.mp equal)

theorem shared_output_closed_terms_false
    {first second : ClosedTerm}
    (checked : CheckedNormalSeparation first second) :
    ¬ ∃ output : Individual,
      output = quote first ∧ output = quote second := by
  rintro ⟨output, firstEq, secondEq⟩
  exact checked.quote_ne (firstEq.symm.trans secondEq)

example : checkNormalSeparation
    (Term.lam (Term.bvar 0) : ClosedTerm)
    (Term.lam (Term.lam (Term.bvar 1)) : ClosedTerm)
    { firstSteps := [], secondSteps := [] } = true := by
  native_decide

example : checkNormalSeparation
    (Term.app (Term.lam (Term.bvar 0)) (Term.lam (Term.bvar 0)) : ClosedTerm)
    (Term.lam (Term.lam (Term.bvar 1)) : ClosedTerm)
    { firstSteps := [{ path := [], kind := .beta }], secondSteps := [] } = true := by
  native_decide

end VisualProof.Lambda
