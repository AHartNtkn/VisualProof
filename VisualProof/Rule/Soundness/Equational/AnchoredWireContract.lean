import VisualProof.Rule.Soundness.Equational.AnchoredWireOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- Reinsert the single identifier omitted by a survivor domain as the final
identifier of an append-one carrier. -/
def restoreDeletedEquiv
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted)) :
    FiniteEquiv (Fin (domain.count + 1)) (Fin size) where
  toFun := Fin.lastCases deleted domain.origin
  invFun := fun original =>
    if equality : original = deleted then
      Fin.last domain.count
    else
      (domain.index original (by
        rw [domain_eq]
        exact decide_eq_true equality)).castSucc
  left_inv := by
    intro candidate
    refine Fin.lastCases (motive := fun current =>
      (if equality : Fin.lastCases deleted domain.origin current = deleted then
          Fin.last domain.count
        else
          (domain.index (Fin.lastCases deleted domain.origin current) (by
            rw [domain_eq]
            exact decide_eq_true equality)).castSucc) = current) ?_
      (fun survivor => ?_) candidate
    · simp
    · have survivorNe : domain.origin survivor ≠ deleted := by
        intro equality
        have survives := domain.origin_survives survivor
        rw [domain_eq, equality] at survives
        simp at survives
      simp only [Fin.lastCases_castSucc, dif_neg survivorNe]
      exact congrArg Fin.castSucc (domain.index_origin survivor)
  right_inv := by
    intro original
    by_cases equality : original = deleted
    · subst original
      simp
    · simp only [dif_neg equality, Fin.lastCases_castSucc]
      exact domain.origin_index original (by
        rw [domain_eq]
        exact decide_eq_true equality)

@[simp] theorem restoreDeletedEquiv_survivor
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted))
    (survivor : Fin domain.count) :
    restoreDeletedEquiv domain deleted domain_eq survivor.castSucc =
      domain.origin survivor := by
  change Fin.lastCases (motive := fun _ => Fin size) deleted domain.origin
    survivor.castSucc = domain.origin survivor
  exact Fin.lastCases_castSucc (motive := fun _ : Fin (domain.count + 1) =>
    Fin size) (last := deleted) (cast := domain.origin) survivor

@[simp] theorem restoreDeletedEquiv_fresh
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted)) :
    restoreDeletedEquiv domain deleted domain_eq (Fin.last domain.count) =
      deleted := by
  change Fin.lastCases (motive := fun _ => Fin size) deleted domain.origin
    (Fin.last domain.count) = deleted
  exact Fin.lastCases_last (motive := fun _ : Fin (domain.count + 1) =>
    Fin size) (last := deleted) (cast := domain.origin)

def anchoredContractNodeRestore
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount) :
    FiniteEquiv
      (Fin ((anchoredContractNodeDomain input.val redundant).count + 1))
      (Fin input.val.nodeCount) :=
  restoreDeletedEquiv (anchoredContractNodeDomain input.val redundant) redundant
    (by intro candidate; rfl)

def anchoredContractWireRestore
    (input : CheckedDiagram signature)
    (drop : Fin input.val.wireCount) :
    FiniteEquiv
      (Fin ((anchoredContractWireDomain input.val drop).count + 1))
      (Fin input.val.wireCount) :=
  restoreDeletedEquiv (anchoredContractWireDomain input.val drop) drop
    (by intro candidate; rfl)

end AnchoredWireContractSoundness

end VisualProof.Rule
