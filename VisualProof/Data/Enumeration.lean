/-- A proof-derived finite enumeration. Values need not be duplicate-free. -/
structure Enumeration (α : Type u) where
  values : List α
  complete : ∀ value, value ∈ values

namespace Enumeration

def empty : Enumeration Empty where
  values := []
  complete := nofun

end Enumeration
