import VisualProof.Refinement.Implementation.DoubleCutIntroPartition
import VisualProof.Concrete.Subgraph.Splice.Input.Route

namespace VisualProof.Refinement.Implementation.DoubleCutIntroContext

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport
open VisualProof.Refinement.Implementation.DoubleCutIntroPartition

/-- The enclosing concrete route is unchanged by double-cut introduction;
only its region indices are lifted past the two fresh regions. -/
private theorem route_lift_aux
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {start target : Fin input.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input start target path)
    (targetEq : target = selection.val.anchor) :
    Concrete.Splice.RegionRoute (doubleCutIntroRaw input selection)
      (Fin.castAdd 2 start) (Fin.castAdd 2 target) path := by
  induction route with
  | here region => exact .here _
  | @step start child target rest parent position positionEq tail induction =>
      have startNe : start ≠ selection.val.anchor := by
        intro equality
        subst start
        exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          wellFormed parent
          (targetEq ▸ Concrete.Splice.Input.RegionRoute.encloses tail wellFormed)
      have childUnselected : child ∉ selection.val.childRoots := by
        intro selected
        have direct := selection.property.childRoots_direct child selected
        exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          wellFormed direct
          (targetEq ▸ Concrete.Splice.Input.RegionRoute.encloses tail wellFormed)
      have targetParent :
          ((doubleCutIntroRaw input selection).regions
            (Fin.castAdd 2 child)).parent? = some (Fin.castAdd 2 start) := by
        rw [oldRegion_parent, if_neg childUnselected, parent]
        rfl
      let targetPosition : Fin
          (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection) (Fin.castAdd 2 start)).length :=
        Fin.cast (by simp [regular_localOccurrences input selection start startNe])
          position
      have targetGet :
          (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection)
            (Fin.castAdd 2 start)).get targetPosition =
              .child (Fin.castAdd 2 child) := by
        have sourceGet := indexOf?_sound positionEq
        simpa [targetPosition,
          regular_localOccurrences input selection start startNe,
          liftOccurrence] using
          congrArg (liftOccurrence input) sourceGet
      have targetPositionEq :
          indexOf? (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection) (Fin.castAdd 2 start))
            (.child (Fin.castAdd 2 child)) = some targetPosition := by
        rw [← targetGet]
        exact indexOf?_get_eq_some_of_nodup
          (Concrete.Elaboration.localOccurrences_nodup _ _) targetPosition
      have positionVal : targetPosition.val = position.val := rfl
      simpa [positionVal] using Concrete.Splice.RegionRoute.step targetParent
        targetPosition targetPositionEq (induction targetEq)

theorem route_lift
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input start
      selection.val.anchor path) :
    Concrete.Splice.RegionRoute (doubleCutIntroRaw input selection)
      (Fin.castAdd 2 start) (Fin.castAdd 2 selection.val.anchor) path :=
  route_lift_aux input selection wellFormed route rfl

end VisualProof.Refinement.Implementation.DoubleCutIntroContext
