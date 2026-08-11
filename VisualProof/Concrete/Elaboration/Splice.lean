import VisualProof.Concrete.Elaboration.Transform
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.Core

/-! Proof kernels for transporting the unchanged frame through a splice layout.

These lemmas deliberately stop short of compiling a complete splice.  They
identify the frame-wire carrier under the source-only attachment contract and
place its lexical scopes inside an arbitrary plug layout. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input

/-- When attachments do not identify distinct frame wires, quotienting the
attachment partition is only a reindexing of the frame wire carrier. -/
noncomputable def quotientWireEquiv (input : Input)
    (consistent : input.AttachmentConsistent) :
    FiniteEquiv (Fin input.frame.val.wireCount) input.wireQuotient.Carrier where
  toFun := input.quotientWire
  invFun := input.wireQuotient.origin
  left_inv := by
    intro wire
    apply input.quotientWire_injective consistent
    exact input.quotientWire_wireQuotient_origin
      (input.quotientWire wire)
  right_inv := input.quotientWire_wireQuotient_origin

@[simp] theorem quotientWireEquiv_apply (input : Input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    input.quotientWireEquiv consistent wire = input.quotientWire wire := rfl

@[simp] theorem quotientWireEquiv_symm_apply (input : Input)
    (consistent : input.AttachmentConsistent)
    (quotient : input.wireQuotient.Carrier) :
    (input.quotientWireEquiv consistent).symm quotient =
      input.wireQuotient.origin quotient := rfl

namespace PlugLayout

/-- The complete target-carrier embedding of an unchanged frame wire. -/
noncomputable def frameWireEmbedding (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) :
    Fin input.frame.val.wireCount → Fin layout.wireCount :=
  layout.frameWire ∘ input.quotientWireEquiv consistent

@[simp] theorem frameWireEmbedding_apply (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    layout.frameWireEmbedding consistent wire =
      layout.frameWire (input.quotientWire wire) := rfl

theorem frameWire_injective (layout : PlugLayout input) :
    Function.Injective layout.frameWire := by
  intro left right equality
  apply Fin.ext
  simpa [frameWire] using congrArg Fin.val equality

theorem frameWireEmbedding_injective (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) :
    Function.Injective (layout.frameWireEmbedding consistent) := by
  intro left right equality
  apply input.quotientWire_injective consistent
  apply layout.frameWire_injective
  exact equality

theorem frameRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.frameRegion := by
  intro left right equality
  apply Fin.ext
  simpa [frameRegion] using congrArg Fin.val equality

theorem coalescedScope_quotientWire (input : Input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    input.coalescedScope (input.quotientWire wire) =
      (input.frame.val.wires wire).scope := by
  obtain ⟨member, hmember, hscope⟩ :=
    input.coalescedScope_eq_member_scope (input.quotientWire wire)
  have quotientEq : input.quotientWire member = input.quotientWire wire :=
    (input.mem_classWires _ _).1 hmember
  have memberEq : member = wire :=
    input.quotientWire_injective consistent quotientEq
  simpa [memberEq] using hscope

theorem frameWireEmbedding_scope (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    (layout.plugRaw.wires (layout.frameWireEmbedding consistent wire)).scope =
      layout.frameRegion (input.frame.val.wires wire).scope := by
  simp only [frameWireEmbedding_apply, plugRaw, frameWire, plugWire,
    Fin.addCases_left]
  exact congrArg layout.frameRegion
    (coalescedScope_quotientWire input consistent wire)

/-- A frame wire is local to a source region exactly when its image is local
to that region's frame image in the plug target. -/
theorem frameWireEmbedding_mem_exactScopeWires_iff
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount)
    (wire : Fin input.frame.val.wireCount) :
    layout.frameWireEmbedding consistent wire ∈
        exactScopeWires layout.plugRaw (layout.frameRegion region) ↔
      wire ∈ exactScopeWires input.frame.val region := by
  calc
    _ ↔ (layout.plugRaw.wires
          (layout.frameWireEmbedding consistent wire)).scope =
        layout.frameRegion region :=
      mem_exactScopeWires layout.plugRaw (layout.frameRegion region) _
    _ ↔ (input.frame.val.wires wire).scope = region := by
      rw [layout.frameWireEmbedding_scope consistent wire]
      constructor
      · intro equality
        exact layout.frameRegion_injective equality
      · exact congrArg layout.frameRegion
    _ ↔ _ := (mem_exactScopeWires input.frame.val region wire).symm

/-- The image of the source local-wire list is a duplicate-free target context
whose membership is exactly the embedded source local scope. -/
noncomputable def frameScopeContext (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount) :
    WireContext layout.plugRaw :=
  (exactScopeWires input.frame.val region).map
    (layout.frameWireEmbedding consistent)

theorem frameScopeContext_nodup (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount) :
    (layout.frameScopeContext consistent region).Nodup := by
  unfold frameScopeContext
  refine (exactScopeWires_nodup input.frame.val region).map
    (layout.frameWireEmbedding consistent) ?_
  intro left right distinct equality
  exact distinct (layout.frameWireEmbedding_injective consistent equality)

theorem mem_frameScopeContext_iff (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount)
    (targetWire : Fin layout.wireCount) :
    targetWire ∈ layout.frameScopeContext consistent region ↔
      ∃ sourceWire ∈ exactScopeWires input.frame.val region,
        layout.frameWireEmbedding consistent sourceWire = targetWire := by
  unfold frameScopeContext
  exact List.mem_map

theorem frameScopeContext_subset_exactScopeWires (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount) :
    ∀ targetWire, targetWire ∈ layout.frameScopeContext consistent region →
      targetWire ∈ exactScopeWires layout.plugRaw (layout.frameRegion region) := by
  intro targetWire member
  obtain ⟨sourceWire, hsource, mapped⟩ :=
    (layout.mem_frameScopeContext_iff consistent region targetWire).1 member
  rw [← mapped]
  exact (layout.frameWireEmbedding_mem_exactScopeWires_iff
    consistent region sourceWire).2 hsource

end PlugLayout

end Splice.Input

end VisualProof.Concrete
