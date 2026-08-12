import VisualProof.Concrete.Elaboration.SpliceWireLayout

/-! Compiler contexts transported through a source-derived splice layout. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

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
