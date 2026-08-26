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

private def supportIndex [DecidableEq α] (value : α) :
    (support : List α) → value ∈ support → Fin support.length
  | [], absent => False.elim (by simpa using absent)
  | head :: tail, present =>
      if heq : value = head then
        ⟨0, by simp⟩
      else
        Fin.succ (supportIndex value tail (by
          simpa [heq] using present))

private theorem supportIndex_get [DecidableEq α] (value : α)
    (support : List α) (present : value ∈ support) :
    support.get (supportIndex value support present) = value := by
  induction support with
  | nil => simp at present
  | cons head tail ih =>
      unfold supportIndex
      split
      · rename_i heq
        simpa [heq]
      · rename_i hne
        simpa using ih (by simpa [hne] using present)

private def Term.compactInto [DecidableEq α] (support : List α) :
    (term : Term n α) →
      (∀ value, value ∈ term.freeSupport → value ∈ support) →
      Term n (Fin support.length)
  | .bvar index, _ => .bvar index
  | .port value, contained =>
      .port (supportIndex value support (contained value (by simp [freeSupport])))
  | .lam body, contained =>
      .lam (body.compactInto support fun value present =>
        contained value (by simpa [freeSupport] using present))
  | .app fn argument, contained =>
      .app
        (fn.compactInto support fun value present =>
          contained value (by simp [freeSupport, present]))
        (argument.compactInto support fun value present =>
          contained value (by
            by_cases hfn : value ∈ fn.freeSupport
            · simp [freeSupport, hfn]
            · simp [freeSupport, hfn, present]))

/-- Deterministically replace a term's occurring free variables by their
first-occurrence positions in its deduplicated support. -/
def Term.compact [DecidableEq α] (term : Term n α) :
    Term n (Fin term.freeSupport.length) :=
  term.compactInto term.freeSupport (fun _ present => present)

private theorem Term.compactInto_reconstruct [DecidableEq α]
    (support : List α) (term : Term n α)
    (contained : ∀ value, value ∈ term.freeSupport → value ∈ support) :
    (term.compactInto support contained).mapFree support.get = term := by
  induction term with
  | bvar index => rfl
  | port value =>
      simp only [compactInto, mapFree]
      exact congrArg Term.port
        (supportIndex_get value support (contained value (by simp [freeSupport])))
  | lam body ih =>
      simp only [compactInto, mapFree]
      exact congrArg Term.lam (ih _)
  | app fn argument ihFn ihArgument =>
      simp only [compactInto, mapFree]
      rw [ihFn _, ihArgument _]

theorem Term.compact_reconstruct [DecidableEq α] (term : Term n α) :
    term.compact.mapFree term.freeSupport.get = term :=
  term.compactInto_reconstruct term.freeSupport
    (fun _ present => present)

theorem Term.freeSupport_nodup [DecidableEq α] (term : Term n α) :
    term.freeSupport.Nodup := by
  induction term with
  | bvar _ => simp [freeSupport]
  | port _ => simp [freeSupport]
  | lam _ ih => simpa [freeSupport] using ih
  | app fn argument ihFn ihArgument =>
      simp only [freeSupport]
      rw [List.nodup_append]
      refine ⟨ihFn, List.Pairwise.filter _ ihArgument, ?_⟩
      intro left hleft right hright heq
      subst right
      have hright' : left ∈ Term.freeSupport argument ∧
          left ∉ Term.freeSupport fn := by
        simpa using hright
      have hnot : left ∉ Term.freeSupport fn := by
        exact hright'.2
      exact hnot hleft

/-- Replace positional free ports by the outer de Bruijn variables that will
bind them. Port `0` becomes the outermost of the `ports` new binders, exactly
matching the TypeScript positional closure convention. -/
def Term.closeOverPortsBody :
    (term : Term n (Fin ports)) → Term (ports + n) Empty
  | .bvar index => .bvar ⟨index.val, by omega⟩
  | .port port => .bvar ⟨n + (ports - 1 - port.val), by
      have hport := port.isLt
      omega⟩
  | .lam body => .lam body.closeOverPortsBody
  | .app fn argument => .app fn.closeOverPortsBody argument.closeOverPortsBody

/-- Abstract every one of the `ports` outer variables, from the last
positional port inward. -/
def Term.abstractPorts :
    (ports : Nat) → Term ports Empty → ClosedTerm
  | 0, term => term
  | ports + 1, term => abstractPorts ports (.lam term)

/-- Close a positional term over all of its ports. Applying the result to
ports `0, 1, …` restores the original open term up to beta reduction. -/
def Term.closeOverPorts (term : Term 0 (Fin ports)) : ClosedTerm :=
  Term.abstractPorts ports term.closeOverPortsBody

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
