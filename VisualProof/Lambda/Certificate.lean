import VisualProof.Lambda.Reduction

namespace VisualProof.Lambda

inductive RedexKind
  | beta
  | eta
  deriving DecidableEq, Repr

inductive PathSegment
  | fn
  | arg
  | body
  deriving DecidableEq, Repr

structure ReductionStep where
  path : List PathSegment
  kind : RedexKind
  deriving DecidableEq, Repr

abbrev ReductionPath := List ReductionStep

structure Certificate where
  left : ReductionPath
  right : ReductionPath
  deriving DecidableEq, Repr

private def stepRoot (t : Term n α) (kind : RedexKind) : Option (Term n α) :=
  match kind, t with
  | .beta, .app (.lam body) arg =>
      some (body.substBound (Fin.cases arg Term.bvar))
  | .eta, .lam body => etaContract body
  | _, _ => none

def stepAt : Term n α → List PathSegment → RedexKind → Option (Term n α)
  | t, [], kind => stepRoot t kind
  | .lam body, .body :: rest, kind =>
      (stepAt body rest kind).map Term.lam
  | .app fn arg, .fn :: rest, kind =>
      (stepAt fn rest kind).map (fun fn' => Term.app fn' arg)
  | .app fn arg, .arg :: rest, kind =>
      (stepAt arg rest kind).map (fun arg' => Term.app fn arg')
  | _, _ :: _, _ => none

private theorem stepRoot_sound : stepRoot start kind = some finish →
    OneStep start finish := by
  intro h
  cases kind with
  | beta =>
      cases start with
      | bvar _ => cases h
      | port _ => cases h
      | lam _ => cases h
      | app fn arg =>
          cases fn with
          | bvar _ => cases h
          | port _ => cases h
          | app _ _ => cases h
          | lam body =>
              simp only [stepRoot] at h
              cases h
              exact OneStep.beta rfl
  | eta =>
      cases start with
      | bvar _ => cases h
      | port _ => cases h
      | app _ _ => cases h
      | lam body => exact OneStep.eta h

theorem stepAt_sound {n : Nat} {α : Type u} {start finish : Term n α}
    {path : List PathSegment} {kind : RedexKind} :
    stepAt start path kind = some finish →
    OneStep start finish := by
  induction path generalizing n start finish with
  | nil =>
      intro h
      apply stepRoot_sound
      simpa only [stepAt] using h
  | cons segment rest ih =>
      cases segment <;> cases start <;>
        simp only [stepAt] <;> intro h <;> try contradiction
      case fn.app fn arg =>
        obtain ⟨fn', hfn, rfl⟩ := Option.map_eq_some_iff.mp h
        exact OneStep.appFn (ih (start := fn) (finish := fn') hfn)
      case arg.app fn arg =>
        obtain ⟨arg', harg, rfl⟩ := Option.map_eq_some_iff.mp h
        exact OneStep.appArg (ih (start := arg) (finish := arg') harg)
      case body.lam body =>
        obtain ⟨body', hbody, rfl⟩ := Option.map_eq_some_iff.mp h
        exact OneStep.lam (ih (start := body) (finish := body') hbody)

def checkPath (start : Term n α) : ReductionPath → Option (Term n α)
  | [] => some start
  | step :: rest =>
      match stepAt start step.path step.kind with
      | none => none
      | some next => checkPath next rest

theorem checkPath_sound : checkPath start path = some finish →
    BetaEta start finish := by
  induction path generalizing start with
  | nil =>
      simp only [checkPath]
      intro h
      cases h
      exact .refl
  | cons step rest ih =>
      simp only [checkPath]
      split
      next => intro h; contradiction
      next next hstep =>
        intro hpath
        exact (BetaEta.step (stepAt_sound hstep)).trans (ih hpath)

def checkCertificate [DecidableEq α]
    (left right : Term n α) (cert : Certificate) : Bool :=
  match checkPath left cert.left, checkPath right cert.right with
  | some leftEnd, some rightEnd => decide (leftEnd = rightEnd)
  | _, _ => false

theorem checkCertificate_sound {n : Nat} {α : Type u} [DecidableEq α]
    {left right : Term n α} {cert : Certificate} :
    checkCertificate left right cert = true → BetaEta left right := by
  unfold checkCertificate
  generalize hleft : checkPath left cert.left = leftResult
  generalize hright : checkPath right cert.right = rightResult
  cases leftResult with
  | none => intro h; contradiction
  | some leftEnd =>
      cases rightResult with
      | none => intro h; contradiction
      | some rightEnd =>
          simp only [decide_eq_true_eq]
          intro hend
          subst rightEnd
          exact (checkPath_sound hleft).trans (checkPath_sound hright).symm

def idTerm : ClosedTerm := Term.lam (Term.bvar 0)

def constId : ClosedTerm := Term.app (Term.lam (Term.bvar 0)) idTerm

theorem constId_beta : BetaEta constId idTerm := by
  exact BetaEta.step (OneStep.beta rfl)

theorem validCertificate_accepts : checkCertificate constId idTerm
    { left := [{ path := [], kind := .beta }], right := [] } = true := by
  rfl

theorem invalidFirstSegment_rejects : checkCertificate idTerm idTerm
    { left := [{ path := [.fn], kind := .beta }], right := [] } = false := by
  rfl

end VisualProof.Lambda
