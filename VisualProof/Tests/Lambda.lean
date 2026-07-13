import VisualProof.Lambda.Syntax

open VisualProof Lambda

example : Term 0 (Fin 1) := Term.port 0
example : Term 0 Empty := Term.lam (Term.bvar 0)
