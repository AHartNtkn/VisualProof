namespace VisualProof.Lambda

inductive TermCore (free : Type u) : Nat → Type u
  | bvar : Fin bound → TermCore free bound
  | port : free → TermCore free bound
  | lam : TermCore free (bound + 1) → TermCore free bound
  | app : TermCore free bound → TermCore free bound → TermCore free bound
  deriving DecidableEq, Repr

abbrev Term (bound : Nat) (free : Type u) := TermCore free bound

abbrev Term.bvar (i : Fin bound) : Term bound free := TermCore.bvar i
abbrev Term.port (x : free) : Term bound free := TermCore.port x
abbrev Term.lam (body : Term (bound + 1) free) : Term bound free := TermCore.lam body
abbrev Term.app (fn arg : Term bound free) : Term bound free := TermCore.app fn arg

abbrev ClosedTerm := Term 0 Empty

def Term.mapFree (f : α → β) : Term n α → Term n β
  | .bvar i => .bvar i
  | .port x => .port (f x)
  | .lam body => .lam (body.mapFree f)
  | .app fn arg => .app (fn.mapFree f) (arg.mapFree f)

def Term.freeSupport [DecidableEq α] : Term n α → List α
  | .bvar _ => []
  | .port x => [x]
  | .lam body => body.freeSupport
  | .app fn arg =>
      let fnSupport := fn.freeSupport
      let argSupport := arg.freeSupport
      fnSupport ++ argSupport.filter (fun x => x ∉ fnSupport)

theorem Term.mapFree_id (t : Term n α) : t.mapFree id = t := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam _ ih => simp only [mapFree, ih]
  | app _ _ ihFn ihArg => simp only [mapFree, ihFn, ihArg]

theorem Term.mapFree_comp (f : α → β) (g : β → γ) (t : Term n α) :
    (t.mapFree f).mapFree g = t.mapFree (g ∘ f) := by
  induction t with
  | bvar _ => rfl
  | port _ => rfl
  | lam _ ih => simp only [mapFree, ih]
  | app _ _ ihFn ihArg => simp only [mapFree, ihFn, ihArg]

end VisualProof.Lambda
