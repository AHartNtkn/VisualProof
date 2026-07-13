import VisualProof.Lambda.Syntax

namespace VisualProof.Lambda

private def liftRenaming (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def Term.renameBound (ρ : Fin n → Fin m) : Term n α → Term m α
  | .bvar i => .bvar (ρ i)
  | .port x => .port x
  | .lam body => .lam (body.renameBound (liftRenaming ρ))
  | .app fn arg => .app (fn.renameBound ρ) (arg.renameBound ρ)

def Term.lift : Term n α → Term (n + 1) α :=
  Term.renameBound Fin.succ

end VisualProof.Lambda
