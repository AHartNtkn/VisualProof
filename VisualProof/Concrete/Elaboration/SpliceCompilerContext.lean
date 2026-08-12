import VisualProof.Concrete.Elaboration.SpliceWireLayout

/-! Compiler contexts transported through a source-derived splice layout. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

/-- The canonical position of a known wire in an ordered compiler context. -/
noncomputable def contextPosition
    (context : WireContext d) (wire : Fin d.wireCount)
    (member : wire ∈ context) : Fin context.length :=
  (context.lookup? wire).get
    (Option.isSome_iff_exists.mpr (WireContext.lookup?_complete member))

theorem contextPosition_get
    (context : WireContext d) (wire : Fin d.wireCount)
    (member : wire ∈ context) :
    context.get (contextPosition context wire member) = wire := by
  apply WireContext.lookup?_sound
  exact (Option.some_get (Option.isSome_iff_exists.mpr
    (WireContext.lookup?_complete member))).symm

theorem climb_frameRegion (layout : PlugLayout input)
    (steps : Nat) (region : Fin input.frame.val.regionCount) :
    layout.plugRaw.climb steps (layout.frameRegion region) =
      (input.frame.val.climb steps region).map layout.frameRegion := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [Diagram.climb]
      cases sourceRegion : input.frame.val.regions region with
      | sheet =>
          rw [layout.plugRaw_regions_frame, sourceRegion]
          simp [PlugLayout.mapFrameRegion, CRegion.parent?]
          rfl
      | cut parent =>
          rw [layout.plugRaw_regions_frame, sourceRegion]
          simpa [PlugLayout.mapFrameRegion, CRegion.parent?, sourceRegion]
            using ih parent
      | bubble parent arity =>
          rw [layout.plugRaw_regions_frame, sourceRegion]
          simpa [PlugLayout.mapFrameRegion, CRegion.parent?, sourceRegion]
            using ih parent

theorem encloses_frameRegion_iff
    (layout : PlugLayout input)
    (ancestor descendant : Fin input.frame.val.regionCount) :
    layout.plugRaw.Encloses (layout.frameRegion ancestor)
        (layout.frameRegion descendant) ↔
      input.frame.val.Encloses ancestor descendant := by
  constructor
  · rintro ⟨steps, targetClimb⟩
    rw [layout.climb_frameRegion] at targetClimb
    obtain ⟨sourceFinish, sourceClimb, mapped⟩ :=
      Option.map_eq_some_iff.mp targetClimb
    have finishEq : sourceFinish = ancestor :=
      (layout.frameRegion_eq_frameRegion_iff _ _).1 mapped
    subst sourceFinish
    obtain ⟨rootSteps, ancestorRoot⟩ :=
      input.frame.property.all_regions_reach_root ancestor
    obtain ⟨totalSteps, descendantRoot⟩ :=
      input.frame.property.all_regions_reach_root descendant
    have composed : input.frame.val.climb
        (steps.val + rootSteps.val) descendant =
          some input.frame.val.root :=
      climb_add sourceClimb ancestorRoot
    have totalEq : steps.val + rootSteps.val = totalSteps.val :=
      ParentTraversal.climb_to_root_steps_unique input.frame.val
        input.frame.property.root_is_sheet composed descendantRoot
    refine ⟨⟨steps.val, by omega⟩, sourceClimb⟩
  · rintro ⟨steps, sourceClimb⟩
    refine ⟨⟨steps.val, by
      have := steps.isLt
      simp only [PlugLayout.plugRaw, PlugLayout.regionCount]
      omega⟩, ?_⟩
    rw [layout.climb_frameRegion, sourceClimb]
    rfl

/-- Embed an ordered source frame wire context into the retained target
carrier without changing its order. -/
noncomputable def mapFrameContext (layout : PlugLayout input)
    (context : WireContext input.frame.val) : WireContext layout.plugRaw :=
  context.map (layout.frameWireMap)

/-- The position map induced by stable frame-context embedding. -/
noncomputable def mapFrameContextIndex (layout : PlugLayout input)
    (context : WireContext input.frame.val) :
    Fin context.length → Fin (layout.mapFrameContext context).length :=
  Fin.cast (List.length_map layout.frameWireMap).symm

@[simp] theorem mapFrameContextIndex_val
    (layout : PlugLayout input)
    (context : WireContext input.frame.val) (index : Fin context.length) :
    (layout.mapFrameContextIndex context index).val = index.val := rfl

theorem mapFrameContext_get
    (layout : PlugLayout input)
    (context : WireContext input.frame.val) (index : Fin context.length) :
    (layout.mapFrameContext context).get
        (layout.mapFrameContextIndex context index) =
      layout.frameWireMap (context.get index) := by
  exact List.getElem_map (layout.frameWireMap)

theorem frameWireMap_scope
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    (layout.plugRaw.wires (layout.frameWireMap wire)).scope =
      layout.frameRegion (input.frame.val.wires wire).scope := by
  have scope := coalescedScope_quotientWire input consistent wire
  unfold PlugLayout.frameWireMap
  rw [layout.plugRaw_wires_frame, scope]

/-- Embed one exact source compiler context into the corresponding exact
target frame context. -/
noncomputable def mapFrameExactContext
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.frameRegion region)) :
    Fin sourceContext.length → Fin targetContext.length :=
  fun index => contextPosition targetContext
    (layout.frameWireMap (sourceContext.get index)) (by
      apply (targetExact.mem_iff _).mpr
      rw [layout.frameWireMap_scope consistent]
      exact (layout.encloses_frameRegion_iff _ _).2
        ((sourceExact.mem_iff _).mp (List.get_mem _ _)))

theorem mapFrameExactContext_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.frameRegion region))
    (index : Fin sourceContext.length) :
    targetContext.get (layout.mapFrameExactContext consistent region
      sourceContext targetContext sourceExact targetExact index) =
        layout.frameWireMap (sourceContext.get index) :=
  contextPosition_get _ _ _

theorem mapFrameContext_append
    (layout : PlugLayout input)
    (first second : WireContext input.frame.val) :
    layout.mapFrameContext (first ++ second) =
      layout.mapFrameContext first ++
        layout.mapFrameContext second := by
  exact List.map_append

theorem mapFrameContext_exactScopeWires
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    layout.mapFrameContext
        (exactScopeWires input.frame.val region) =
      layout.frameLocalWires region := rfl

/-- A source frame binder context embedded into the retained target regions.
Material target regions have no entry until the recursive compiler pushes one. -/
def mapFrameBinders (layout : PlugLayout input)
    (binders : BinderContext input.frame.val rels) :
    BinderContext layout.plugRaw rels :=
  fun region => Fin.addCases binders (fun _ => none) region

@[simp] theorem mapFrameBinders_frameRegion
    (layout : PlugLayout input)
    (binders : BinderContext input.frame.val rels)
    (region : Fin input.frame.val.regionCount) :
    layout.mapFrameBinders binders (layout.frameRegion region) =
      binders region := by
  simp [mapFrameBinders, PlugLayout.frameRegion, PlugLayout.plugRaw,
    PlugLayout.regionCount]

@[simp] theorem mapFrameBinders_materialRegion
    (layout : PlugLayout input)
    (binders : BinderContext input.frame.val rels)
    (material : layout.materialRegions.Carrier) :
    layout.mapFrameBinders binders (layout.materialRegion material) = none := by
  simp [mapFrameBinders, PlugLayout.materialRegion, PlugLayout.plugRaw,
    PlugLayout.regionCount]

/-- Pushing a retained frame bubble commutes with embedding its binder context. -/
theorem mapFrameBinders_push
    (layout : PlugLayout input)
    (binders : BinderContext input.frame.val rels)
    (binder : Fin input.frame.val.regionCount) (arity : Nat) :
    (layout.mapFrameBinders binders).push (layout.frameRegion binder) arity =
      layout.mapFrameBinders (binders.push binder arity) := by
  funext candidate
  refine Fin.addCases (motive := fun region => candidate = region → _)
    (fun frame candidateEq => ?_)
    (fun material candidateEq => ?_) candidate rfl
  · subst candidate
    change (layout.mapFrameBinders binders).push
        (layout.frameRegion binder) arity (layout.frameRegion frame) =
      layout.mapFrameBinders (binders.push binder arity)
        (layout.frameRegion frame)
    by_cases atBinder : frame = binder
    · subst frame
      rw [BinderContext.push_self, layout.mapFrameBinders_frameRegion,
        BinderContext.push_self]
    · have targetNe : layout.frameRegion frame ≠
          layout.frameRegion binder := fun equality =>
        atBinder ((layout.frameRegion_eq_frameRegion_iff _ _).1 equality)
      rw [BinderContext.push_other _ arity targetNe,
        layout.mapFrameBinders_frameRegion,
        layout.mapFrameBinders_frameRegion,
        BinderContext.push_other _ arity atBinder]
  · subst candidate
    change (layout.mapFrameBinders binders).push
        (layout.frameRegion binder) arity (layout.materialRegion material) =
      layout.mapFrameBinders (binders.push binder arity)
        (layout.materialRegion material)
    have targetNe : layout.materialRegion material ≠
        layout.frameRegion binder :=
      layout.materialRegion_ne_frameRegion material binder
    rw [BinderContext.push_other _ arity targetNe,
      layout.mapFrameBinders_materialRegion,
      layout.mapFrameBinders_materialRegion]
    rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
