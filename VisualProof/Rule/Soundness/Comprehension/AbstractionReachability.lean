import VisualProof.Rule.Soundness.Comprehension.AbstractionNode

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- Regions reachable by the ordinary source traversal before the wrap focus:
the untouched regular frame and the wrap anchor itself. -/
def Reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Prop :=
  region = wrap.val.anchor ∨
    trace.FrameRegular region ∧ region ∉ wrap.selectedRegions

theorem reachable_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    trace.Reachable input.val.root := by
  by_cases wrapRoot : input.val.root = wrap.val.anchor
  · exact Or.inl wrapRoot
  · apply Or.inr
    constructor
    · refine ⟨trace.root_survives, wrapRoot, ?_⟩
      intro index equal
      rcases payload.anchors_inside index with same | selected
      · exact wrapRoot (equal.trans same)
      · exact selection_root_not_selected input wrap (equal ▸ selected)
    · exact selection_root_not_selected input wrap

theorem survives_of_reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (reachable : trace.Reachable region) :
    trace.domains.regions.survives region = true := by
  rcases reachable with wrapRegion | outer
  · exact wrapRegion ▸ wrap_anchor_survives payload
  · exact outer.1.1

theorem reachable_child_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent child : Fin input.val.regionCount)
    (reachable : trace.Reachable parent)
    (regular : trace.FrameRegular parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.Reachable child := by
  by_cases childWrap : child = wrap.val.anchor
  · exact Or.inl childWrap
  · apply Or.inr
    have parentNotSelected : parent ∉ wrap.selectedRegions := by
      rcases reachable with parentWrap | outer
      · exact False.elim (regular.2.1 parentWrap)
      · exact outer.2
    have childNotSelected : child ∉ wrap.selectedRegions := by
      intro selected
      rcases selectedRegion_parent_cases input wrap selected childParent with
        parentWrap | parentSelected
      · exact regular.2.1 parentWrap
      · exact parentNotSelected parentSelected
    refine ⟨⟨trace.child_survives_of_regular parent child regular childParent,
      childWrap, ?_⟩, childNotSelected⟩
    intro index equal
    rcases payload.anchors_inside index with same | selected
    · exact childWrap (equal.trans same)
    · exact childNotSelected (equal ▸ selected)

private theorem direct_child_selected_is_childRoot
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (child : Fin input.val.regionCount)
    (childParent : (input.val.regions child).parent? =
      some selection.val.anchor)
    (selected : child ∈ selection.selectedRegions) :
    child ∈ selection.val.childRoots := by
  obtain ⟨root, rootMember, encloses⟩ :=
    (selection.mem_selectedRegions child).1 selected
  rcases ConcreteElaboration.encloses_direct_child childParent encloses with
    rootEq | rootEnclosesAnchor
  · simpa [rootEq] using rootMember
  · exact False.elim
      (ConcreteElaboration.checked_direct_child_not_encloses_parent
        input.property (selection.property.childRoots_direct root rootMember)
          rootEnclosesAnchor)

/-- A source/target child pair that remains directly below the focused wrap
anchor is necessarily a surviving regular child outside the wrapped material.
Opaque occurrence interiors map to the target root and wrap child roots are
reparented beneath the fresh bubble, so neither can enter recursive transport. -/
theorem reachable_child_of_wrap_focus
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (child : Fin input.val.regionCount)
    (sourceParent : (input.val.regions child).parent? = some wrap.val.anchor)
    (targetParent : (trace.diagram.regions (trace.regionMap child)).parent? =
      some (trace.regionMap wrap.val.anchor)) :
    trace.Reachable child := by
  have wrapSurvives := wrap_anchor_survives payload
  have wrapMap : trace.regionMap wrap.val.anchor =
      trace.targetRegion wrap.val.anchor wrapSurvives :=
    trace.regionMap_of_survives _ wrapSurvives
  by_cases survives : trace.domains.regions.survives child = true
  · have childMap : trace.regionMap child = trace.targetRegion child survives :=
      trace.regionMap_of_survives child survives
    have parentShape := trace.targetRegion_parent child wrap.val.anchor survives
      sourceParent
    by_cases direct : child ∈ wrap.val.childRoots
    · rw [childMap, wrapMap] at targetParent
      rw [if_pos direct] at parentShape
      rw [parentShape] at targetParent
      exact False.elim
        (trace.targetRegion_ne_bubble wrap.val.anchor wrapSurvives
          (Option.some.inj targetParent).symm)
    · have childNotSelected : child ∉ wrap.selectedRegions := by
        intro selected
        exact direct (direct_child_selected_is_childRoot input wrap child
          sourceParent selected)
      have childNotWrap : child ≠ wrap.val.anchor := by
        intro equal
        subst child
        exact ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property sourceParent
            (ConcreteDiagram.Encloses.refl input.val wrap.val.anchor)
      apply Or.inr
      refine ⟨⟨survives, childNotWrap, ?_⟩, childNotSelected⟩
      intro index equal
      rcases payload.anchors_inside index with same | selected
      · exact childNotWrap (equal.trans same)
      · exact childNotSelected (equal ▸ selected)
  · unfold regionMap at targetParent
    rw [dif_neg survives] at targetParent
    rw [targetWellFormed.root_is_sheet] at targetParent
    contradiction

end AbstractionRawTrace

end VisualProof.Rule
