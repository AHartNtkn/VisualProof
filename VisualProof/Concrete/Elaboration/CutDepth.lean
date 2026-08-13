import VisualProof.Concrete.Step.Core
import VisualProof.Concrete.Elaboration.Traversal

namespace VisualProof.Concrete

open Elaboration

private theorem concreteCutDepthAux_eq_of_climb_to_root
    {diagram : Concrete.Diagram}
    (wellFormed : diagram.WellFormed)
    {region : Fin diagram.regionCount} {steps fuel : Nat}
    (climb : diagram.climb steps region = some diagram.root)
    (enough : steps ≤ fuel) :
    concreteCutDepthAux diagram fuel region =
      concreteCutDepthAux diagram steps region := by
  induction steps generalizing fuel region with
  | zero =>
      have regionEq : region = diagram.root := by
        simpa only [Diagram.climb_zero, Option.some.injEq] using climb
      subst region
      cases fuel with
      | zero => rfl
      | succ fuel =>
          change (match diagram.regions diagram.root with
            | .sheet => 0
            | .cut parent => concreteCutDepthAux diagram fuel parent + 1
            | .bubble parent _ => concreteCutDepthAux diagram fuel parent) = 0
          rw [wellFormed.root_is_sheet]
  | succ steps induction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases regionKind : diagram.regions region with
          | sheet =>
              simp [Diagram.climb, regionKind, CRegion.parent?] at climb
          | cut parent =>
              have parentClimb :
                  diagram.climb steps parent = some diagram.root := by
                simpa [Diagram.climb, regionKind, CRegion.parent?] using climb
              have parentDepth := induction parentClimb (by omega : steps ≤ fuel)
              simpa [concreteCutDepthAux, regionKind] using parentDepth
          | bubble parent arity =>
              have parentClimb :
                  diagram.climb steps parent = some diagram.root := by
                simpa [Diagram.climb, regionKind, CRegion.parent?] using climb
              simpa [concreteCutDepthAux, regionKind] using
                induction parentClimb (by omega : steps ≤ fuel)

/-- Once a parent climb reaches the root, extra evaluation depth cannot change
the number of enclosing cuts. -/
theorem concreteCutDepth_eq_aux_of_climb_to_root
    {diagram : Concrete.Diagram}
    (wellFormed : diagram.WellFormed)
    {region : Fin diagram.regionCount} {steps : Nat}
    (climb : diagram.climb steps region = some diagram.root) :
    concreteCutDepth diagram region =
      concreteCutDepthAux diagram steps region := by
  unfold concreteCutDepth
  exact concreteCutDepthAux_eq_of_climb_to_root wellFormed climb
    (ParentTraversal.climb_to_root_steps_le_regionCount diagram
      wellFormed.root_is_sheet wellFormed.all_regions_reach_root climb)

@[simp] theorem concreteCutDepth_root
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed) :
    concreteCutDepth diagram diagram.root = 0 := by
  rw [concreteCutDepth_eq_aux_of_climb_to_root wellFormed
    (diagram.climb_zero diagram.root)]
  rfl

/-- A direct cut child contributes exactly one enclosing cut. -/
theorem concreteCutDepth_cut_child
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {parent child : Fin diagram.regionCount}
    (childKind : diagram.regions child = .cut parent) :
    concreteCutDepth diagram child = concreteCutDepth diagram parent + 1 := by
  obtain ⟨steps, parentClimb⟩ := wellFormed.all_regions_reach_root parent
  have childClimb :
      diagram.climb (steps.val + 1) child = some diagram.root := by
    change diagram.climb (Nat.succ steps.val) child = some diagram.root
    simpa [Diagram.climb, childKind, CRegion.parent?] using parentClimb
  rw [concreteCutDepth_eq_aux_of_climb_to_root wellFormed childClimb,
    concreteCutDepth_eq_aux_of_climb_to_root wellFormed parentClimb]
  simp [concreteCutDepthAux, childKind]

/-- A direct bubble child preserves enclosing-cut depth. -/
theorem concreteCutDepth_bubble_child
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {parent child : Fin diagram.regionCount} {arity : Nat}
    (childKind : diagram.regions child = .bubble parent arity) :
    concreteCutDepth diagram child = concreteCutDepth diagram parent := by
  obtain ⟨steps, parentClimb⟩ := wellFormed.all_regions_reach_root parent
  have childClimb :
      diagram.climb (steps.val + 1) child = some diagram.root := by
    change diagram.climb (Nat.succ steps.val) child = some diagram.root
    simpa [Diagram.climb, childKind, CRegion.parent?] using parentClimb
  rw [concreteCutDepth_eq_aux_of_climb_to_root wellFormed childClimb,
    concreteCutDepth_eq_aux_of_climb_to_root wellFormed parentClimb]
  simp [concreteCutDepthAux, childKind]

end VisualProof.Concrete
