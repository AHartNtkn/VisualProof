import VisualProof.Concrete.Step.Core

namespace VisualProof.Concrete

open VisualProof.Data.Finite

theorem survivor_index?_injective (domain : SurvivorDomain size) :
    ∀ {left right mapped}, domain.index? left = some mapped →
      domain.index? right = some mapped → left = right := by
  intro left right mapped hleft hright
  have leftOrigin := (domain.index?_eq_some_iff left mapped).mp hleft
  have rightOrigin := (domain.index?_eq_some_iff right mapped).mp hright
  exact leftOrigin.symm.trans rightOrigin

def erasurePolarity (orientation : Orientation) (depth : Nat) : Prop :=
  match orientation with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

instance (orientation : Orientation) (depth : Nat) :
    Decidable (erasurePolarity orientation depth) := by
  cases orientation <;> simp [erasurePolarity] <;> infer_instance

def spawnPolarity (orientation : Orientation) (depth : Nat) : Prop :=
  match orientation with
  | .forward => depth % 2 = 1
  | .backward => depth % 2 = 0

instance (orientation : Orientation) (depth : Nat) :
    Decidable (spawnPolarity orientation depth) := by
  cases orientation <;> simp [spawnPolarity] <;> infer_instance

end VisualProof.Concrete
