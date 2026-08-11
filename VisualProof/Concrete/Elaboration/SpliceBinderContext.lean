import VisualProof.Concrete.Elaboration.SpliceCompilerContext

/-! Binder contexts transported through the retained frame of a splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

/-- Retained frame regions preserve their exact concrete region constructor. -/
@[simp] theorem plugRegion_frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    layout.plugRaw.regions (layout.frameRegion region) =
      layout.mapFrameRegion (input.frame.val.regions region) := by
  simp [PlugLayout.plugRaw, PlugLayout.plugRegion, PlugLayout.frameRegion,
    Fin.addCases_left]

/-- Material regions preserve the exact constructor of their source pattern
region, with every parent rewritten by the source-derived body map. -/
@[simp] theorem plugRegion_materialRegion (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.plugRaw.regions (layout.materialRegion material) =
      layout.mapPatternRegion (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material)) := by
  simp [PlugLayout.plugRaw, PlugLayout.plugRegion,
    PlugLayout.materialRegion, Fin.addCases_right]

/-- Climbing from a retained frame region commutes with the frame-region
embedding.  In particular, no upward traversal from the frame can enter a
material region. -/
theorem climb_frameRegion (layout : PlugLayout input)
    (steps : Nat) (region : Fin input.frame.val.regionCount) :
    layout.plugRaw.climb steps (layout.frameRegion region) =
      (input.frame.val.climb steps region).map layout.frameRegion := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps inductionHypothesis =>
      cases regionEq : input.frame.val.regions region with
      | sheet =>
          simp [Diagram.climb, regionEq, PlugLayout.mapFrameRegion,
            CRegion.parent?]
          rfl
      | cut parent =>
          simp [Diagram.climb, regionEq, PlugLayout.mapFrameRegion,
            CRegion.parent?, inductionHypothesis]
      | bubble parent arity =>
          simp [Diagram.climb, regionEq, PlugLayout.mapFrameRegion,
            CRegion.parent?, inductionHypothesis]

/-- Retained frame embedding reflects and preserves enclosure.  The forward
direction uses source well-formedness only to recover the source-sized bound
on a successful target climb. -/
theorem encloses_frameRegion_iff (layout : PlugLayout input)
    (sourceWellFormed : input.frame.val.WellFormed)
    (ancestor descendant : Fin input.frame.val.regionCount) :
    layout.plugRaw.Encloses (layout.frameRegion ancestor)
        (layout.frameRegion descendant) ↔
      input.frame.val.Encloses ancestor descendant := by
  constructor
  · rintro ⟨steps, targetClimb⟩
    rw [layout.climb_frameRegion] at targetClimb
    cases sourceClimb : input.frame.val.climb steps.val descendant with
    | none => simp [sourceClimb] at targetClimb
    | some sourceAncestor =>
        simp only [sourceClimb, Option.map_some] at targetClimb
        have ancestorEq : sourceAncestor = ancestor :=
          layout.frameRegion_injective (Option.some.inj targetClimb)
        subst sourceAncestor
        obtain ⟨rootSteps, ancestorToRoot⟩ :=
          sourceWellFormed.all_regions_reach_root ancestor
        have descendantToRoot : input.frame.val.climb
            (steps.val + rootSteps.val) descendant =
              some input.frame.val.root :=
          climb_add sourceClimb ancestorToRoot
        have bounded := ParentTraversal.climb_to_root_steps_le_regionCount
          input.frame.val sourceWellFormed.root_is_sheet
            sourceWellFormed.all_regions_reach_root descendantToRoot
        exact ⟨⟨steps.val, by omega⟩, sourceClimb⟩
  · rintro ⟨steps, sourceClimb⟩
    refine ⟨⟨steps.val, ?_⟩, ?_⟩
    · simp only [PlugLayout.plugRaw, PlugLayout.regionCount]
      omega
    · rw [layout.climb_frameRegion, sourceClimb]
      rfl

/-- A material region cannot enclose a retained frame region.  This follows
from the exact upward climb computation, rather than from an assumed target
separation invariant. -/
theorem materialRegion_not_encloses_frameRegion
    (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (frame : Fin input.frame.val.regionCount) :
    ¬layout.plugRaw.Encloses (layout.materialRegion material)
      (layout.frameRegion frame) := by
  rintro ⟨steps, targetClimb⟩
  rw [layout.climb_frameRegion] at targetClimb
  cases sourceClimb : input.frame.val.climb steps.val frame with
  | none => simp [sourceClimb] at targetClimb
  | some ancestor =>
      simp only [sourceClimb, Option.map_some] at targetClimb
      have impossible : layout.frameRegion ancestor =
          layout.materialRegion material :=
        Option.some.inj targetClimb
      exact layout.frameRegion_ne_materialRegion ancestor material impossible

/-- Embedding a source compiler binder context preserves its coverage at the
retained splice site.  A target binder enclosing that site must be a retained
frame bubble; material bubbles are excluded by the climb computation above. -/
theorem mapFrameBinders_covers_site
    (layout : PlugLayout input)
    {binders : BinderContext input.frame.val rels}
    (sourceCovers : binders.Covers input.site) :
    (layout.mapFrameBinders binders).Covers
      (layout.frameRegion input.site) := by
  intro targetBinder targetParent arity targetBubble targetEncloses
  refine Fin.addCases (motive := fun candidate =>
      targetBinder = candidate →
        ∃ relation : RelVar rels arity,
          layout.mapFrameBinders binders targetBinder =
            some ⟨arity, relation⟩)
    (fun frame binderEq => ?_)
    (fun material binderEq => ?_) targetBinder rfl
  · subst targetBinder
    change layout.plugRaw.regions (layout.frameRegion frame) =
      .bubble targetParent arity at targetBubble
    change layout.plugRaw.Encloses (layout.frameRegion frame)
      (layout.frameRegion input.site) at targetEncloses
    change ∃ relation : RelVar rels arity,
      layout.mapFrameBinders binders (layout.frameRegion frame) =
        some ⟨arity, relation⟩
    rw [layout.plugRegion_frameRegion] at targetBubble
    cases sourceRegionEq : input.frame.val.regions frame with
    | sheet =>
        rw [sourceRegionEq] at targetBubble
        cases targetBubble
    | cut sourceParent =>
        rw [sourceRegionEq] at targetBubble
        cases targetBubble
    | bubble sourceParent sourceArity =>
        rw [sourceRegionEq] at targetBubble
        have arityEq : sourceArity = arity :=
          (CRegion.bubble.inj targetBubble).2
        subst sourceArity
        have sourceEncloses : input.frame.val.Encloses frame input.site :=
          (layout.encloses_frameRegion_iff
            input.frame.property frame input.site).1 targetEncloses
        obtain ⟨relation, sourceLookup⟩ := sourceCovers frame sourceParent
          arity sourceRegionEq sourceEncloses
        exact ⟨relation, by
          rw [layout.mapFrameBinders_frameRegion]
          exact sourceLookup⟩
  · subst targetBinder
    change layout.plugRaw.Encloses (layout.materialRegion material)
      (layout.frameRegion input.site) at targetEncloses
    exact (layout.materialRegion_not_encloses_frameRegion
      material input.site targetEncloses).elim

end Splice.Input.PlugLayout

end VisualProof.Concrete
