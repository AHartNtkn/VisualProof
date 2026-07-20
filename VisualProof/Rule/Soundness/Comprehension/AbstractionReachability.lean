import VisualProof.Rule.Soundness.Comprehension.AbstractionNode

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- Exactly the source regions retained by the executor are available to the
semantic recursion. Deleted occurrence interiors remain opaque; surviving
wrapped material and occurrence anchors remain traversable. -/
def Reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Prop :=
  trace.domains.regions.survives region = true

/-- Regions reached by the outer frame simulation.  Material selected by the
wrap is discharged by the wrap kernel itself, so the generic recursion may
reach the wrap anchor but never enters its selected interior. -/
def OuterReachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Prop :=
  trace.Reachable region ∧
    (region = wrap.val.anchor ∨ region ∉ wrap.selectedRegions)

theorem outerReachable_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences) :
    trace.OuterReachable input.val.root := by
  refine ⟨trace.root_survives, ?_⟩
  by_cases equal : input.val.root = wrap.val.anchor
  · exact Or.inl equal
  · exact Or.inr (selection_root_not_selected input wrap)

/-- A distinguished region reachable by the outer simulation is necessarily
the wrap anchor; occurrence anchors inside the selected material belong to the
specialized fixed-relation kernel. -/
theorem outerReachable_focused_eq
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (reachable : trace.OuterReachable region)
    (focused : ¬ trace.FrameRegular region) :
    region = wrap.val.anchor := by
  by_cases wrapEq : region = wrap.val.anchor
  · exact wrapEq
  · have anchored : ∃ index : Fin occurrences.length,
        region = (occurrences.get index).selection.val.anchor := by
      classical
      by_cases existsAnchor : ∃ index : Fin occurrences.length,
          region = (occurrences.get index).selection.val.anchor
      · exact existsAnchor
      · exact False.elim (focused ⟨reachable.1, wrapEq, by
          intro index equal
          exact existsAnchor ⟨index, equal⟩⟩)
    obtain ⟨index, anchorEq⟩ := anchored
    rcases payload.anchors_inside index with atWrap | inside
    · exact False.elim (wrapEq (anchorEq.trans atWrap))
    · have outside := reachable.2.resolve_left wrapEq
      exact False.elim (outside (anchorEq ▸ inside))

theorem outerReachable_child_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent child : Fin input.val.regionCount)
    (reachable : trace.OuterReachable parent)
    (regular : trace.FrameRegular parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.OuterReachable child := by
  refine ⟨trace.child_survives_of_regular parent child regular childParent, ?_⟩
  by_cases wrapEq : child = wrap.val.anchor
  · exact Or.inl wrapEq
  · apply Or.inr
    intro selected
    rcases selectedRegion_parent_cases input wrap selected childParent with
      parentWrap | parentSelected
    · exact regular.2.1 parentWrap
    · rcases reachable.2 with parentWrap | parentOutside
      · exact regular.2.1 parentWrap
      · exact parentOutside parentSelected

theorem reachable_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences) :
    trace.Reachable input.val.root :=
  trace.root_survives

theorem survives_of_reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (region : Fin input.val.regionCount)
    (reachable : trace.Reachable region) :
    trace.domains.regions.survives region = true :=
  reachable

theorem reachable_child_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (parent child : Fin input.val.regionCount)
    (_reachable : trace.Reachable parent)
    (regular : trace.FrameRegular parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.Reachable child :=
  trace.child_survives_of_regular parent child regular childParent

/-- Any source child that the target compiler still sees directly below a
focused survivor must itself survive. A deleted child maps to the target root,
whose checked sheet shape cannot have a parent. -/
theorem reachable_child_of_focus
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (parent child : Fin input.val.regionCount)
    (_parentReachable : trace.Reachable parent)
    (targetParent : (trace.diagram.regions (trace.regionMap child)).parent? =
      some (trace.regionMap parent)) :
    trace.Reachable child := by
  by_cases survives : trace.domains.regions.survives child = true
  · exact survives
  · unfold regionMap at targetParent
    rw [dif_neg survives] at targetParent
    rw [targetWellFormed.root_is_sheet] at targetParent
    contradiction

end AbstractionRawTrace

end VisualProof.Rule
