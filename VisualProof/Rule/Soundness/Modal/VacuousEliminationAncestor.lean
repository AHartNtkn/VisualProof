import VisualProof.Rule.Soundness.Modal.VacuousElimination

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Every ancestor of the promoted focus is the surviving image of an
ancestor of the eliminated bubble's parent. -/
private theorem sourceAncestor_maps
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (descendant ancestor : Fin trace.sourceDiagram.regionCount)
    (descendantEnclosesFocus : trace.sourceDiagram.Encloses descendant
      (trace.targetIndex targetWellFormed))
    (steps : Nat)
    (bound : steps < trace.sourceDiagram.regionCount + 1)
    (climb : trace.sourceDiagram.climb steps descendant = some ancestor) :
    input.Encloses (trace.origin ancestor) (trace.origin descendant) := by
  induction steps generalizing descendant ancestor with
  | zero =>
      have equality : descendant = ancestor := by
        simpa [ConcreteDiagram.climb] using Option.some.inj climb
      subst ancestor
      exact ConcreteDiagram.Encloses.refl input (trace.origin descendant)
  | succ steps induction =>
      cases parentEq : (trace.sourceDiagram.regions descendant).parent? with
      | none => simp [ConcreteDiagram.climb, parentEq] at climb
      | some parent =>
          have tail : trace.sourceDiagram.climb steps parent = some ancestor := by
            simpa [ConcreteDiagram.climb, parentEq] using climb
          have parentNeFocus : parent ≠ trace.targetIndex targetWellFormed := by
            intro equality
            subst parent
            exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
              sourceWellFormed parentEq) descendantEnclosesFocus
          have originalParent :
              (input.regions (trace.origin descendant)).parent? =
                some (trace.origin parent) :=
            (trace.promotedRegion_parent_eq_regular_iff targetWellFormed
              descendant parent parentNeFocus).1 parentEq
          have parentEnclosesDescendant : trace.sourceDiagram.Encloses parent
              descendant := by
            refine ⟨⟨1, by have := descendant.isLt; omega⟩, ?_⟩
            simp [ConcreteDiagram.climb, parentEq]
          have parentEnclosesFocus :=
            ConcreteElaboration.checked_encloses_trans sourceWellFormed
              parentEnclosesDescendant descendantEnclosesFocus
          have mappedTail := induction parent ancestor parentEnclosesFocus
            (by omega) tail
          have originalParentEncloses : input.Encloses (trace.origin parent)
              (trace.origin descendant) := by
            refine ⟨⟨1, by have := (trace.origin descendant).isLt; omega⟩, ?_⟩
            simp [ConcreteDiagram.climb, originalParent]
          exact ConcreteElaboration.checked_encloses_trans targetWellFormed
            mappedTail originalParentEncloses

/-- An enclosure of the promoted focus reflects to enclosure of the original
parent under the survivor origin map. -/
theorem sourceEnclosesFocus_iff_forward
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (ancestor : Fin trace.sourceDiagram.regionCount)
    (encloses : trace.sourceDiagram.Encloses ancestor
      (trace.targetIndex targetWellFormed)) :
    input.Encloses (trace.origin ancestor) trace.parent := by
  obtain ⟨steps, climb⟩ := encloses
  have mapped := sourceAncestor_maps trace targetWellFormed sourceWellFormed
    (trace.targetIndex targetWellFormed) ancestor
    (ConcreteDiagram.Encloses.refl trace.sourceDiagram
      (trace.targetIndex targetWellFormed)) steps.val steps.isLt climb
  have focusOrigin : trace.origin (trace.targetIndex targetWellFormed) =
      trace.parent := trace.targetIndex_origin targetWellFormed
  rw [focusOrigin] at mapped
  exact mapped

/-- Lift one original ancestor chain above the eliminated bubble's parent to
the promoted focus. -/
private theorem targetAncestor_lifts
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetCurrent : Fin input.regionCount)
    (sourceCurrent : Fin trace.sourceDiagram.regionCount)
    (currentOrigin : trace.origin sourceCurrent = targetCurrent)
    (targetCurrentEnclosesParent : input.Encloses targetCurrent trace.parent)
    (sourceCurrentEnclosesFocus : trace.sourceDiagram.Encloses sourceCurrent
      (trace.targetIndex targetWellFormed))
    (steps : Nat)
    (bound : steps < input.regionCount + 1)
    (climb : input.climb steps targetCurrent = some ancestor) :
    ∃ sourceAncestor,
      trace.origin sourceAncestor = ancestor ∧
        trace.sourceDiagram.Encloses sourceAncestor
          (trace.targetIndex targetWellFormed) := by
  induction steps generalizing targetCurrent sourceCurrent ancestor with
  | zero =>
      have equality : targetCurrent = ancestor := by
        simpa [ConcreteDiagram.climb] using Option.some.inj climb
      subst ancestor
      exact ⟨sourceCurrent, currentOrigin,
        sourceCurrentEnclosesFocus⟩
  | succ steps induction =>
      cases parentEq : (input.regions targetCurrent).parent? with
      | none => simp [ConcreteDiagram.climb, parentEq] at climb
      | some parent =>
          have tail : input.climb steps parent = some ancestor := by
            simpa [ConcreteDiagram.climb, parentEq] using climb
          have parentEnclosesCurrent : input.Encloses parent targetCurrent := by
            refine ⟨⟨1, by have := targetCurrent.isLt; omega⟩, ?_⟩
            simp [ConcreteDiagram.climb, parentEq]
          have parentEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans targetWellFormed
              parentEnclosesCurrent targetCurrentEnclosesParent
          have parentNeBubble : parent ≠ bubble := by
            intro equality
            subst parent
            have bubbleParent : (input.regions bubble).parent? =
                some trace.parent := by
              simp [trace.bubble_eq, CRegion.parent?]
            exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
              targetWellFormed bubbleParent) parentEnclosesTarget
          let sourceParent := (vacuousRegionDomain input bubble).index parent
            (by simp [vacuousRegionDomain, parentNeBubble])
          have sourceParentOrigin : trace.origin sourceParent = parent :=
            SurvivorDomain.origin_index _ parent _
          have sourceParentNeFocus :
              sourceParent ≠ trace.targetIndex targetWellFormed := by
            intro equality
            have parentIsTarget : parent = trace.parent := by
              have focusOrigin :
                  trace.origin (trace.targetIndex targetWellFormed) =
                    trace.parent := trace.targetIndex_origin targetWellFormed
              exact sourceParentOrigin.symm.trans
                ((congrArg trace.origin equality).trans focusOrigin)
            exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
              targetWellFormed parentEq)
                (by simpa [parentIsTarget] using targetCurrentEnclosesParent)
          have sourceParentEq :
              (trace.sourceDiagram.regions sourceCurrent).parent? =
                some sourceParent := by
            apply (trace.promotedRegion_parent_eq_regular_iff targetWellFormed
              sourceCurrent sourceParent sourceParentNeFocus).2
            simpa [currentOrigin, sourceParentOrigin] using parentEq
          have sourceParentEnclosesCurrent :
              trace.sourceDiagram.Encloses sourceParent sourceCurrent := by
            refine ⟨⟨1, by have := sourceCurrent.isLt; omega⟩, ?_⟩
            simp [ConcreteDiagram.climb, sourceParentEq]
          have sourceParentEnclosesFocus :=
            ConcreteElaboration.checked_encloses_trans sourceWellFormed
              sourceParentEnclosesCurrent sourceCurrentEnclosesFocus
          exact induction (ancestor := ancestor) parent sourceParent
            sourceParentOrigin
            parentEnclosesTarget sourceParentEnclosesFocus (by omega) tail

/-- Every original ancestor of the eliminated bubble's parent has a unique
surviving representative enclosing the promoted focus. -/
theorem sourceEnclosesFocus_iff_backward
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (ancestor : Fin input.regionCount)
    (encloses : input.Encloses ancestor trace.parent) :
    ∃ sourceAncestor,
      trace.origin sourceAncestor = ancestor ∧
        trace.sourceDiagram.Encloses sourceAncestor
          (trace.targetIndex targetWellFormed) := by
  obtain ⟨steps, climb⟩ := encloses
  exact targetAncestor_lifts trace targetWellFormed sourceWellFormed
    trace.parent (trace.targetIndex targetWellFormed)
    (trace.targetIndex_origin targetWellFormed)
    (ConcreteDiagram.Encloses.refl input trace.parent)
    (ConcreteDiagram.Encloses.refl trace.sourceDiagram
      (trace.targetIndex targetWellFormed)) steps.val steps.isLt climb

end VisualProof.Rule.VacuousElimTrace
