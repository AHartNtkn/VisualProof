namespace VisualProof.Rule.Lambda

/-- A covered quotient from two positional term interfaces to one carrier.
Mappings may repeat when multiple native slots share one physical wire. -/
structure Correspondence (leftArity rightArity : Nat) where
  commonArity : Nat
  left : Fin leftArity → Fin commonArity
  right : Fin rightArity → Fin commonArity
  covered : ∀ commonSlot,
    (∃ leftSlot, left leftSlot = commonSlot) ∨
      (∃ rightSlot, right rightSlot = commonSlot)

def Correspondence.symm
    (correspondence : Correspondence leftArity rightArity) :
    Correspondence rightArity leftArity where
  commonArity := correspondence.commonArity
  left := correspondence.right
  right := correspondence.left
  covered := fun commonSlot =>
    (correspondence.covered commonSlot).elim Or.inr Or.inl

end VisualProof.Rule.Lambda
