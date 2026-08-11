import VisualProof.Concrete.Elaboration.Compile.SiteKernel
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

/-- The exact arity-indexed compiler input carried by a splice pattern. -/
def patternState (input : Input) : State input.pattern.val.boundary.length where
  checked := input.pattern
  boundary_length := rfl

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

namespace CompilerRoute

theorem region_encloses
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {origin site : Fin diagram.regionCount}
    {context siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.region origin context)
      site siteContext) :
    diagram.Encloses origin site := by
  cases route with
  | regionHere => exact Diagram.Encloses.refl diagram origin
  | @regionStep _ child _ _ _ parent nested =>
      have originChild : diagram.Encloses origin child := by
        refine ⟨⟨1, by have := origin.isLt; omega⟩, ?_⟩
        simp [Diagram.climb, parent]
      exact checked_encloses_trans wellFormed originChild
        (region_encloses wellFormed nested)
termination_by sizeOf route

private theorem hiddenWires_eq_nil
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram)
    (terminal : spine.TerminalBodyContract pattern.val)
    (nonempty : spine.proxyCount ≠ 0) :
    pattern.val.hiddenWires = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro wire member
  have hidden := (OpenDiagram.mem_hiddenWires pattern.val wire).1 member
  have notBoundary : wire ∉ pattern.val.boundary := by
    simpa only [OpenDiagram.mem_exposedWires] using hidden.2
  exact (terminal.root_has_no_nonboundary_wires nonempty wire notBoundary)
    hidden.1

private theorem exactScopeWires_proxy_eq_nil
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram)
    (terminal : spine.TerminalBodyContract pattern.val)
    (proxy : Fin spine.proxyCount)
    (nonterminal : proxy.val + 1 < spine.proxyCount) :
    exactScopeWires pattern.val.diagram (spine.proxy proxy) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro wire member
  have scopeEq := (mem_exactScopeWires pattern.val.diagram
    (spine.proxy proxy) wire).1 member
  by_cases boundary : wire ∈ pattern.val.boundary
  · have rootScope := terminal.boundary_is_root_scoped wire boundary
    exact spine.proxy_ne_root proxy (scopeEq.symm.trans rootScope)
  · exact (terminal.nonterminal_has_no_nonboundary_wires
      proxy nonterminal wire boundary) scopeEq

private theorem terminal_context_from_proxy
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram)
    (terminal : spine.TerminalBodyContract pattern.val)
    (proxy : Fin spine.proxyCount)
    (context : WireContext pattern.val.diagram)
    {site : Fin pattern.val.diagram.regionCount}
    {siteContext : WireContext pattern.val.diagram}
    (route : ConcreteCompilerRoute pattern.val.diagram
      (.region (spine.proxy proxy) context)
      site siteContext)
    (siteEq : site = spine.bodyContainer) :
    siteContext = context := by
  cases route with
  | regionHere => rfl
  | @regionStep _ child _ _ _ parent nested =>
      have nestedEncloses := region_encloses
        pattern.property.diagram_well_formed nested
      have nonterminal : proxy.val + 1 < spine.proxyCount := by
        apply Classical.byContradiction
        intro atEnd
        let last : Fin spine.proxyCount :=
          ⟨spine.proxyCount - 1, by
            have := proxy.isLt
            omega⟩
        have proxyEq : proxy = last := by
          apply Fin.ext
          dsimp [last]
          omega
        have bodyEq : spine.bodyContainer = spine.proxy last :=
          spine.body_eq_terminal_of_nonempty (by
            have := proxy.isLt
            omega)
        have childEnclosesProxy : pattern.val.diagram.Encloses child
            (spine.proxy proxy) := by
          simpa [siteEq, proxyEq, bodyEq] using nestedEncloses
        exact (checked_direct_child_not_encloses_parent
          pattern.property.diagram_well_formed parent)
            childEnclosesProxy
      let next : Fin spine.proxyCount :=
        ⟨proxy.val + 1, nonterminal⟩
      have childEq : child = spine.proxy next :=
        terminal.nonterminal_direct_child proxy nonterminal child parent
      subst child
      have noLocals := exactScopeWires_proxy_eq_nil pattern spine terminal
        proxy nonterminal
      have recursive := terminal_context_from_proxy pattern spine terminal next
        (context.extend (spine.proxy proxy)) nested siteEq
      simpa [WireContext.extend, noLocals] using recursive
termination_by spine.proxyCount - proxy.val
decreasing_by omega

/-- A terminal-body route inherits exactly the pattern's ordered exposed-wire
context.  All hidden root wires and nonterminal-proxy local blocks are empty
by the terminal contract. -/
theorem terminal_context
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram)
    (terminal : spine.TerminalBodyContract pattern.val)
    {site : Fin pattern.val.diagram.regionCount}
    {siteContext : WireContext pattern.val.diagram}
    (route : ConcreteCompilerRoute pattern.val.diagram
      (.openRoot pattern.val.exposedWires pattern.val.hiddenWires)
      site siteContext)
    (siteEq : site = spine.bodyContainer) :
    siteContext = pattern.val.exposedWires := by
  cases route with
  | root => rfl
  | @rootStep _ _ child _ _ parent nested =>
      have nestedEncloses := region_encloses
        pattern.property.diagram_well_formed nested
      have nonempty : spine.proxyCount ≠ 0 := by
        intro empty
        have bodyEq := spine.body_eq_root_of_empty empty
        have childEnclosesRoot : pattern.val.diagram.Encloses child
            pattern.val.diagram.root := by
          simpa [siteEq, bodyEq] using nestedEncloses
        exact (checked_direct_child_not_encloses_parent
          pattern.property.diagram_well_formed parent)
            childEnclosesRoot
      let first : Fin spine.proxyCount :=
        ⟨0, Nat.pos_of_ne_zero nonempty⟩
      have childEq : child = spine.proxy first :=
        terminal.root_direct_child nonempty child parent
      subst child
      have noHidden := hiddenWires_eq_nil pattern spine terminal nonempty
      have recursive := terminal_context_from_proxy pattern spine terminal first
        (pattern.val.exposedWires ++ pattern.val.hiddenWires) nested siteEq
      simpa [noHidden] using recursive

end CompilerRoute

/-- A compiled terminal body consumes exactly the pattern's ordered exposed
wire classes as its inherited context. -/
theorem compiledPattern_siteContext
    (input : Input) (terminal : input.TerminalBody)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    compiled.siteContext = input.pattern.val.exposedWires :=
  CompilerRoute.terminal_context input.pattern input.binderSpine terminal
    compiled.route rfl

/-- The exact local material compiler input required by a splice.  The sole
splice-specific field identifies the ordered inherited context with the
pattern interface; no root route or abstract focus is retained. -/
structure CompiledMaterial (input : Input)
    extends LocalCompiledSite input.patternState
      input.binderSpine.bodyContainer where
  siteContext_eq : toLocalCompiledSite.siteContext =
    input.pattern.val.exposedWires

/-- Forget a full source focus after retaining the terminal pattern-interface
identity needed by splice wire transport. -/
def CompiledMaterial.ofCompiledSite
    (input : Input) (terminal : input.TerminalBody)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    CompiledMaterial input where
  toLocalCompiledSite := compiled.local
  siteContext_eq := compiledPattern_siteContext input terminal compiled

namespace PlugLayout

theorem bodyContainer_not_material (input : Input) :
    ¬ input.binderSpine.IsMaterialRegion
      input.binderSpine.bodyContainer := by
  by_cases empty : input.binderSpine.proxyCount = 0
  · rw [input.binderSpine.body_eq_root_of_empty empty]
    exact fun material => material.1 rfl
  · let terminal : Fin input.binderSpine.proxyCount :=
      ⟨input.binderSpine.proxyCount - 1, by omega⟩
    have bodyEq : input.binderSpine.bodyContainer =
        input.binderSpine.proxy terminal :=
      input.binderSpine.body_eq_terminal_of_nonempty empty
    intro material
    exact material.2 terminal bodyEq

@[simp] theorem materialRegions_index?_bodyContainer
    (layout : PlugLayout input) :
    layout.materialRegions.index? input.binderSpine.bodyContainer = none := by
  rw [SurvivorDomain.index?_eq_none_iff, layout.materialRegions_exact]
  exact decide_eq_false_iff_not.mpr (bodyContainer_not_material input)

@[simp] theorem bodyRegion_bodyContainer (layout : PlugLayout input) :
    layout.bodyRegion input.binderSpine.bodyContainer =
      layout.frameRegion input.site := by
  simp [bodyRegion]

@[simp] theorem materialRegions_index?_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.materialRegions.index? (input.binderSpine.proxy proxy) = none := by
  rw [SurvivorDomain.index?_eq_none_iff, layout.materialRegions_exact]
  exact decide_eq_false_iff_not.mpr fun material => material.2 proxy rfl

@[simp] theorem bodyRegion_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.bodyRegion (input.binderSpine.proxy proxy) =
      layout.frameRegion input.site := by
  simp [bodyRegion]

@[simp] theorem proxyIndex?_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.proxyIndex? (input.binderSpine.proxy proxy) = some proxy := by
  unfold proxyIndex?
  have member : input.binderSpine.proxy proxy ∈ layout.proxies := by
    simp [proxies]
  obtain ⟨found, foundEq⟩ := indexOf?_complete member
  rw [foundEq]
  simp only [Option.map_some, Option.some.injEq]
  apply Fin.ext
  have foundValue := indexOf?_sound foundEq
  have foundValueElem :
      layout.proxies[found.val] = input.binderSpine.proxy proxy := by
    simpa only [List.get_eq_getElem] using foundValue
  let original : Fin input.binderSpine.proxyCount :=
    ⟨found.val, by
      simpa [proxies, allFin_eq_finRange] using found.isLt⟩
  have proxyEq : input.binderSpine.proxy original =
      input.binderSpine.proxy proxy := by
    simpa [proxies, allFin_eq_finRange, original] using foundValueElem
  have indexEq := input.binderSpine.proxy_injective proxyEq
  simpa [allFin_eq_finRange] using congrArg Fin.val indexEq

@[simp] theorem binderRegion_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.binderRegion (input.binderSpine.proxy proxy) =
      layout.frameRegion (input.binderTarget proxy) := by
  simp [binderRegion]

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
